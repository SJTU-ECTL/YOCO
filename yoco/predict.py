from __future__ import annotations

import hashlib
import json
from pathlib import Path

import torch
from torch.utils.data import DataLoader

from yoco.root_phase import RootPhaseAigDataset, RootPhaseDETR, RootPhaseDetrConfig, collate_root_phase
from yoco.root_phase.data import FEATURE_DIM, HOP_DEPTH, MAX_CUT_SIZE


def load_model(checkpoint: Path, device: torch.device) -> RootPhaseDETR:
    try:
        ckpt = torch.load(checkpoint, map_location="cpu", weights_only=True)
    except TypeError:
        ckpt = torch.load(checkpoint, map_location="cpu")
    if not isinstance(ckpt, dict) or "model_config" not in ckpt or "model_state" not in ckpt:
        raise ValueError("Checkpoint is not a compatible RootPhaseDETR checkpoint")
    config = RootPhaseDetrConfig.from_dict(ckpt["model_config"])
    if (config.input_dim, config.max_hop, config.max_cut_size) != (FEATURE_DIM, HOP_DEPTH, MAX_CUT_SIZE):
        raise ValueError("Checkpoint feature/schema mismatch: expected 10 input features, 8 hops, and 5 leaf slots")
    model = RootPhaseDETR(config)
    model.load_state_dict(ckpt["model_state"], strict=True)
    return model.to(device).eval()


def infer_cuts(model: RootPhaseDETR, dataset: RootPhaseAigDataset, device: torch.device,
               batch_size: int = 64, threshold: float = 0.5) -> list[dict]:
    loader = DataLoader(dataset, batch_size=batch_size, shuffle=False, num_workers=0,
                        collate_fn=collate_root_phase)
    predictions: dict[tuple[int, tuple[int, ...]], dict] = {}
    with torch.inference_mode():
        for batch in loader:
            batch = {k: v.to(device) if torch.is_tensor(v) else v for k, v in batch.items()}
            output = model(batch)
            prob = output["select_logits"].softmax(dim=-1)[..., 1]
            chosen = prob >= threshold
            pred_leaf = torch.stack([logits.argmax(dim=-1) for logits in output["leaf_logits"]], dim=-1)
            max_nodes = int(batch["x"].shape[1])
            for b in range(int(chosen.shape[0])):
                root = int(batch["roots"][b].item())
                for phase in (0, 1):
                    if not bool(chosen[b, phase].item()):
                        continue
                    local = [int(v) for v in pred_leaf[b, phase].tolist() if int(v) != max_nodes]
                    if (not 2 <= len(local) <= 5 or len(set(local)) != len(local) or 0 in local
                            or any(v < 0 or v >= max_nodes for v in local)
                            or any(not bool(batch["node_mask"][b, v].item()) for v in local)):
                        continue
                    leaves = [int(batch["global_ids"][b, v].item()) for v in local]
                    if root in leaves or len(set(leaves)) != len(leaves):
                        continue
                    key = root, tuple(sorted(leaves))
                    conf = float(prob[b, phase].item())
                    if key not in predictions:
                        predictions[key] = {
                            "type": "cut", "root": root, "leaves": sorted(leaves),
                            "gate": "AIG_DERIVED", "gate_class_id": None,
                            "binding_id": None, "input_permutation": None,
                            "input_negations": [], "output_negation": 0,
                            "confidence": conf, "source": "model", "phase_sources": [phase],
                        }
                    else:
                        row = predictions[key]
                        row["confidence"] = max(float(row["confidence"]), conf)
                        row["phase_sources"] = sorted(set(row["phase_sources"] + [phase]))
    return [predictions[key] for key in sorted(predictions)]


def write_cuts(aig_path: Path, rows: list[dict], dataset: RootPhaseAigDataset,
               target: Path, circuit: str) -> Path:
    if not rows:
        for root in dataset.roots:
            node = dataset.graph.nodes[root]
            leaves = [int(fanin) for fanin, _ in node.fanins]
            if len(leaves) == 2 and leaves[0] != leaves[1]:
                rows = [{
                    "type": "cut", "root": int(root), "leaves": sorted(leaves),
                    "gate": "AIG_AND_FALLBACK", "gate_class_id": None,
                    "binding_id": None, "input_permutation": None,
                    "input_negations": [int(node.fanins[0][1]), int(node.fanins[1][1])],
                    "output_negation": 0, "confidence": 1.0, "source": "fallback",
                }]
                break
    if not rows:
        raise RuntimeError("No usable AIG AND node found for supplied-cut mapping")
    header = {
        "type": "header", "schema_version": 1, "circuit": circuit,
        "aig_sha256": hashlib.sha256(aig_path.read_bytes()).hexdigest(),
        "library_sha256": None, "node_id_space": "frozen_global_id",
        "cut_size": 5, "split": "test", "vocabulary_sha256": None,
    }
    target.write_text("\n".join(json.dumps(r, sort_keys=True) for r in [header, *rows]) + "\n",
                      encoding="utf-8")
    return target
