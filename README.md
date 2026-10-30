# YOCO: Inference-Only Technology Mapping

This repository performs YOCO technology mapping for **combinational binary AIGER (`.aig`) inputs** using the provided RootPhaseDETR checkpoint and the included YOCO-modified ABC. Other input formats and sequential AIGs are not supported.

## Setup

- Linux and Python 3.10+
- Install PyTorch: `python -m pip install -r requirements.txt`
- Compile the included, unchanged YOCO ABC source: `make -C abc -j`
- Use the included technology library `abc/asap7_clean.lib`
- `checkpoints/yoco.pt` must contain `model_config` and `model_state`

## Inference

The example uses the original adder AIG from the paper benchmarks:

```bash
python scripts/run_yoco.py \
  --input examples/adder.aig \
  --checkpoint checkpoints/yoco.pt \
  --output result/
```

For another combinational binary AIGER circuit:

```bash
python scripts/run_yoco.py \
  --input /path/to/circuit.aig \
  --checkpoint checkpoints/yoco.pt \
  --output result/
```

By default the runner uses `abc/abc` and `abc/asap7_clean.lib`. It accepts `--abc`, `--lib`, `--device`, `--batch-size`, and `--select-threshold` overrides.

The result directory contains only `mapped.v`, `mapped.blif`, and `metrics.json` (Area, Delay, ADP, CEC). The runner requires successful YOCO direct supplied-cut mapping, AIG hash validation, and CEC. Temporary predictions are deleted automatically. Each run requires an empty output directory.

Only the trained model architecture, preprocessing, inference, ABC mapping and the example AIG are included. Check the redistribution rights for the technology library and all third-party ABC material before public release.
