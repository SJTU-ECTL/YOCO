from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class AigNode:
    node_id: int
    kind: str
    fanins: tuple[tuple[int, bool], ...]


@dataclass(frozen=True)
class AigGraph:
    path: Path
    max_var: int
    pi_count: int
    po_count: int
    and_count: int
    nodes: dict[int, AigNode]
    po_ids: tuple[int, ...]


def _decode_aiger_uint(data: bytes, offset: int) -> tuple[int, int]:
    value = 0
    shift = 0
    while True:
        if offset >= len(data):
            raise ValueError("Unexpected end of AIGER data while decoding AND delta")
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        if byte < 0x80:
            return value, offset
        shift += 7


def _literal_to_node(literal: int) -> tuple[int, bool]:
    return literal >> 1, bool(literal & 1)


def read_binary_aiger(path: str | Path) -> AigGraph:
    aig_path = Path(path)
    data = aig_path.read_bytes()
    newline = data.find(b"\n")
    if newline < 0:
        raise ValueError(f"{aig_path} is missing an AIGER header")
    header = data[:newline].decode("ascii")
    fields = header.split()
    if len(fields) < 6 or fields[0] != "aig":
        raise ValueError(f"{aig_path} is not a binary AIGER file")

    max_var, pi_count, latch_count, po_count, and_count = (int(v) for v in fields[1:6])
    if latch_count:
        raise ValueError(f"{aig_path} has latches; this YOCO partitioner expects combinational AIGs")

    offset = newline + 1
    output_literals: list[int] = []
    for _ in range(po_count):
        next_newline = data.find(b"\n", offset)
        if next_newline < 0:
            raise ValueError(f"{aig_path} ended while reading output literals")
        output_literals.append(int(data[offset:next_newline]))
        offset = next_newline + 1

    var_to_obj: dict[int, int] = {0: 0}
    nodes: dict[int, AigNode] = {0: AigNode(0, "const", tuple())}
    for pi_id in range(1, pi_count + 1):
        var_to_obj[pi_id] = pi_id
        nodes[pi_id] = AigNode(pi_id, "PI", tuple())

    encoded_ands: list[tuple[int, int, int]] = []
    for idx in range(and_count):
        lhs = 2 * (pi_count + idx + 1)
        delta0, offset = _decode_aiger_uint(data, offset)
        delta1, offset = _decode_aiger_uint(data, offset)
        rhs0 = lhs - delta0
        rhs1 = rhs0 - delta1
        aig_var = lhs >> 1
        obj_id = pi_count + po_count + idx + 1
        var_to_obj[aig_var] = obj_id
        encoded_ands.append((obj_id, rhs0, rhs1))

    for obj_id, rhs0, rhs1 in encoded_ands:
        rhs0_var, rhs0_inv = _literal_to_node(rhs0)
        rhs1_var, rhs1_inv = _literal_to_node(rhs1)
        nodes[obj_id] = AigNode(obj_id, "AND", ((var_to_obj[rhs0_var], rhs0_inv), (var_to_obj[rhs1_var], rhs1_inv)))

    po_ids: list[int] = []
    for idx, literal in enumerate(output_literals):
        po_id = pi_count + idx + 1
        fanin_var, fanin_inv = _literal_to_node(literal)
        po_ids.append(po_id)
        nodes[po_id] = AigNode(po_id, "PO", ((var_to_obj[fanin_var], fanin_inv),))

    missing = sorted({fanin for node in nodes.values() for fanin, _ in node.fanins if fanin not in nodes})
    if missing:
        raise ValueError(f"{aig_path} references missing fanin nodes: {missing[:10]}")

    return AigGraph(
        path=aig_path,
        max_var=max_var,
        pi_count=pi_count,
        po_count=po_count,
        and_count=and_count,
        nodes=nodes,
        po_ids=tuple(po_ids),
    )
