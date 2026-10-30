from __future__ import annotations

import math
from pathlib import Path
from typing import Any, Sequence

import torch
from torch.utils.data import Dataset

from yoco.partition.aig import read_binary_aiger

HOP_DEPTH = 8
MAX_CUT_SIZE = 5
KIND_NAMES = ["AND", "PI", "PO", "BUF", "CONST", "OTHER"]
KIND_TO_ID = {name: i for i, name in enumerate(KIND_NAMES)}
FEATURE_DIM = len(KIND_NAMES) + 4


def build_hop_cone(graph: Any, root: int, max_hops: int = HOP_DEPTH) -> tuple[list[int], list[int]]:
    seen = {int(root)}
    nodes = [int(root)]
    hops = [0]
    frontier = [int(root)]
    for depth in range(1, max_hops + 1):
        nxt: set[int] = set()
        for u in frontier:
            for v, _inv in graph.nodes[u].fanins:
                v = int(v)
                if v not in seen:
                    nxt.add(v)
        if not nxt:
            break
        ordered = sorted(nxt)
        for v in ordered:
            seen.add(v)
            nodes.append(v)
            hops.append(depth)
        frontier = ordered
    return nodes, hops


class RootPhaseAigDataset(Dataset):
    def __init__(self, aig_path: str | Path, max_cone_nodes: int = 384):
        self.aig_path = Path(aig_path).resolve()
        self.graph = read_binary_aiger(self.aig_path)
        self.roots = sorted(
            int(nid) for nid, node in self.graph.nodes.items()
            if str(node.kind).upper() == "AND"
        )
        self.max_cone_nodes = max_cone_nodes
        self.fanout = {int(nid): 0 for nid in self.graph.nodes}
        for node in self.graph.nodes.values():
            for fanin, _ in node.fanins:
                self.fanout[int(fanin)] = self.fanout.get(int(fanin), 0) + 1

    def __len__(self) -> int:
        return len(self.roots)

    def __getitem__(self, index: int) -> dict[str, Any]:
        root = int(self.roots[index])
        cone_nodes, hops = build_hop_cone(self.graph, root)
        if self.max_cone_nodes and len(cone_nodes) > self.max_cone_nodes:
            raise ValueError(
                f"AIG root {root}: cone has {len(cone_nodes)} nodes, "
                f"exceeding --max-cone-nodes={self.max_cone_nodes}; "
                "increase the limit or reduce batch size"
            )
        local = {gid: i for i, gid in enumerate(cone_nodes)}
        n = len(cone_nodes)
        x = torch.zeros((n, FEATURE_DIM), dtype=torch.float32)
        kind_ids = []
        fanouts = []
        indegrees = []
        invfanins = []
        src, dst, invs = [], [], []
        for u_gid in cone_nodes:
            node = self.graph.nodes[u_gid]
            kind = str(node.kind).upper()
            if kind not in KIND_TO_ID:
                kind = "CONST" if "CONST" in kind else "OTHER"
            kind_ids.append(KIND_TO_ID[kind])
            fanouts.append(min(int(self.fanout.get(u_gid, 0)), 32767))
            indegrees.append(min(len(node.fanins), 255))
            invfanins.append(min(sum(1 for _v, flag in node.fanins if flag), 255))
            for v_gid, inv in node.fanins:
                v_gid = int(v_gid)
                if v_gid not in local:
                    continue
                u, v = local[u_gid], local[v_gid]
                bit = int(bool(inv))
                src.extend([v, u])
                dst.extend([u, v])
                invs.extend([bit, bit])
        x[torch.arange(n), torch.tensor(kind_ids, dtype=torch.long)] = 1.0
        x[:, 6] = torch.tensor(hops, dtype=torch.float32) / float(HOP_DEPTH)
        x[:, 7] = torch.log1p(torch.tensor(fanouts, dtype=torch.float32)) / 8.0
        x[:, 8] = torch.tensor(indegrees, dtype=torch.float32) / 2.0
        x[:, 9] = torch.tensor(invfanins, dtype=torch.float32) / 2.0
        return {
            "index": index,
            "root": root,
            "x": x,
            "hop": torch.tensor(hops, dtype=torch.long),
            "global_ids": torch.tensor(cone_nodes, dtype=torch.long),
            "edge_index": torch.tensor([src, dst], dtype=torch.long),
            "edge_inv": torch.tensor(invs, dtype=torch.float32),
        }


def collate_root_phase(samples: Sequence[dict[str, Any]]) -> dict[str, Any]:
    if not samples:
        raise ValueError("Empty inference batch")
    bsz = len(samples)
    max_nodes = max(int(s["x"].shape[0]) for s in samples)
    x = torch.zeros((bsz, max_nodes, FEATURE_DIM), dtype=torch.float32)
    hop = torch.zeros((bsz, max_nodes), dtype=torch.long)
    node_mask = torch.zeros((bsz, max_nodes), dtype=torch.bool)
    global_ids = torch.full((bsz, max_nodes), -1, dtype=torch.long)
    roots = torch.empty((bsz,), dtype=torch.long)
    indices = torch.empty((bsz,), dtype=torch.long)
    edges, invs = [], []
    for b, sample in enumerate(samples):
        n = int(sample["x"].shape[0])
        x[b, :n] = sample["x"]
        hop[b, :n] = sample["hop"]
        node_mask[b, :n] = True
        global_ids[b, :n] = sample["global_ids"]
        roots[b] = int(sample["root"])
        indices[b] = int(sample["index"])
        if sample["edge_index"].numel():
            edges.append(sample["edge_index"] + b * max_nodes)
            invs.append(sample["edge_inv"])
    edge_index = torch.cat(edges, dim=1) if edges else torch.empty((2, 0), dtype=torch.long)
    edge_inv = torch.cat(invs) if invs else torch.empty((0,), dtype=torch.float32)
    return {
        "indices": indices,
        "roots": roots,
        "x": x,
        "hop": hop,
        "node_mask": node_mask,
        "global_ids": global_ids,
        "edge_index": edge_index,
        "edge_inv": edge_inv,
        "null_index": max_nodes,
    }
