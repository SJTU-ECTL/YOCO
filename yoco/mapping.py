from __future__ import annotations

import math
import re
import subprocess
from pathlib import Path


def _safe(path: Path) -> str:
    absolute = str(path.resolve())
    if any(ch.isspace() or ch in ';"\'' for ch in absolute):
        raise ValueError(f"Path contains whitespace or ABC command separators: {absolute}")
    return absolute


def abc_call(abc: Path, commands: str, timeout: int = 1800) -> str:
    proc = subprocess.run([str(abc.resolve()), "-c", commands],
                          cwd=abc.resolve().parent, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          check=False, timeout=timeout)
    output = proc.stdout or ""
    if proc.returncode:
        raise RuntimeError(f"ABC returned {proc.returncode}: {output[-2000:]}")
    return output


def create_aig(abc: Path, source: Path, destination: Path) -> None:
    import shutil
    if source.suffix.lower() != ".aig":
        raise ValueError("YOCO requires a binary AIGER .aig input")
    with source.open("rb") as stream:
        header = stream.readline(256).decode("ascii", errors="replace").split()
    if len(header) < 6 or header[0] != "aig":
        raise ValueError("Invalid binary AIGER input")
    if int(header[3]) != 0:
        raise ValueError("Sequential AIGs are not supported")
    shutil.copyfile(source, destination)


def map_aig(abc: Path, lib: Path, aig: Path, cuts: Path, verilog: Path, blif: Path) -> None:
    help_result = subprocess.run([str(abc.resolve()), "-c", "map -h"],
                                 cwd=abc.resolve().parent, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 timeout=60)
    support = help_result.stdout or ""
    if "-Y" not in support:
        raise RuntimeError("This ABC executable lacks the custom YOCO map -Y interface")
    output = abc_call(abc, (
        f"read {_safe(lib)}; read {_safe(aig)}; map -d -Y {_safe(cuts)}; "
        f"write_verilog {_safe(verilog)}; write_blif {_safe(blif)}; print_stats"
    ))
    if "YOCO_SUPPLIED_CUT_FILE" not in output or '"aig_sha256_match":1' not in output:
        raise RuntimeError(f"Supplied cuts were not accepted with a matching AIG hash: {output[-1500:]}")
    if "YOCO_SUPPLIED_CUT_DIRECT" not in output:
        raise RuntimeError("ABC did not execute YOCO direct supplied-cut mapping")
    if not blif.is_file() or not verilog.is_file() or not blif.stat().st_size:
        raise RuntimeError("ABC returned without a mapped netlist")


def verify_equivalence(abc: Path, lib: Path, aig: Path, blif: Path) -> None:
    output = abc_call(abc, f"read {_safe(lib)}; cec {_safe(aig)} {_safe(blif)}")
    if not re.search(r"Networks are equivalent", output, re.IGNORECASE):
        raise RuntimeError(f"CEC did not prove equivalence: {output[-1500:]}")


def measure_qor(abc: Path, lib: Path, blif: Path) -> tuple[float, float, float]:
    output = abc_call(abc, f"read_lib {_safe(lib)}; read_blif {_safe(blif)}; topo; stime")
    num = r"[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?"
    pairs = re.findall(rf"Area\s*=\s*({num}).*?Delay\s*=\s*({num})", output,
                       flags=re.IGNORECASE | re.DOTALL)
    if not pairs:
        raise RuntimeError(f"ABC topo/stime failed to print Area/Delay: {output[-1500:]}")
    area, delay = map(float, pairs[-1])
    if not all(math.isfinite(v) and v > 0 for v in (area, delay)):
        raise RuntimeError(f"Invalid mapped timing result: Area={area}, Delay={delay}")
    return area, delay, area * delay
