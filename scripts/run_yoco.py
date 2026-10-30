from __future__ import annotations

import argparse
import os
os.environ.setdefault("CUBLAS_WORKSPACE_CONFIG", ":4096:8")
import json
import random
import sys
import tempfile
import shutil
from pathlib import Path

import torch

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from yoco.mapping import create_aig, map_aig, measure_qor, verify_equivalence
from yoco.predict import infer_cuts, load_model, write_cuts
from yoco.root_phase import RootPhaseAigDataset


def resolve_path(path: Path, cwd: Path) -> Path:
    return (path if path.is_absolute() else cwd / path).resolve()


def main() -> None:
    parser = argparse.ArgumentParser(description="YOCO: binary AIGER technology mapping")
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--checkpoint", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--abc", type=Path, default=REPO / "abc" / "abc")
    parser.add_argument("--lib", type=Path, default=REPO / "abc" / "asap7_clean.lib")
    parser.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--select-threshold", type=float, default=0.5)
    parser.add_argument("--max-cone-nodes", type=int, default=0)
    parser.add_argument("--expect-adp", type=float)
    parser.add_argument("--adp-rtol", type=float, default=0.01)
    args = parser.parse_args()
    cwd = Path.cwd()
    source = resolve_path(args.input, cwd)
    checkpoint = resolve_path(args.checkpoint, cwd)
    output = resolve_path(args.output, cwd)
    abc = resolve_path(args.abc, cwd)
    lib = resolve_path(args.lib, cwd)
    if not 0.0 <= args.select_threshold <= 1.0:
        parser.error("--select-threshold must be between 0 and 1")
    if args.batch_size < 1:
        parser.error("--batch-size must be positive")
    for file in (source, checkpoint, abc, lib):
        if not file.is_file():
            parser.error(f"Required file missing: {file}")
    if source == output or output == source.parent:
        parser.error("Output must not overwrite or contain the input source directory")
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error("--output must be an empty directory to avoid stale results")
    random.seed(42)
    torch.manual_seed(42)
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(42)
        torch.backends.cuda.matmul.allow_tf32 = False
        torch.backends.cudnn.allow_tf32 = False
        torch.backends.cuda.enable_flash_sdp(False)
        torch.backends.cuda.enable_mem_efficient_sdp(False)
        torch.backends.cuda.enable_math_sdp(True)
    torch.use_deterministic_algorithms(True)
    device = torch.device(args.device)
    circuit = source.stem
    with tempfile.TemporaryDirectory(prefix="yoco_") as tmp_name:
        tmp = Path(tmp_name)
        aig = tmp / "input.aig"
        cuts = tmp / "predicted_cuts.jsonl"
        create_aig(abc, source, aig)
        dataset = RootPhaseAigDataset(aig, args.max_cone_nodes)
        if not len(dataset):
            raise RuntimeError("The circuit contains no AND nodes; YOCO mapping requires an AIG network")
        model = load_model(checkpoint, device)
        rows = infer_cuts(model, dataset, device, args.batch_size, args.select_threshold)
        write_cuts(aig, rows, dataset, cuts, circuit)
        verilog = tmp / "mapped.v"
        blif = tmp / "mapped.blif"
        map_aig(abc, lib, aig, cuts, verilog, blif)
        verify_equivalence(abc, lib, aig, blif)
        area, delay, adp = measure_qor(abc, lib, blif)
        if args.expect_adp is not None and abs(adp - args.expect_adp) > args.adp_rtol * args.expect_adp:
            raise RuntimeError(f"ADP regression: got {adp:.6f}, expected {args.expect_adp:.6f}, "
                               f"relative tolerance {args.adp_rtol:.4f}")
        shutil.copy2(verilog, output / "mapped.v")
        shutil.copy2(blif, output / "mapped.blif")
        metrics = {"area": area, "delay": delay, "adp": adp, "cec_passed": True}
        (output / "metrics.json").write_text(json.dumps(metrics, indent=2) + "\n", encoding="utf-8")
        print(f"Area={area:.6f} Delay={delay:.6f} ADP={adp:.6f} CEC=PASS")
        print(f"Output: {output}")


if __name__ == "__main__":
    main()
