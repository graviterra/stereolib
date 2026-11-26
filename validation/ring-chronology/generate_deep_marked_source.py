"""Generate synthetic spiro receipts for DeepMarkedSource.lean without Lean.

From the public repository root, after tools/centres10/setup.sh:
  python3 validation/ring-chronology/generate_deep_marked_source.py \
    ".cache/centres10/classes:.cache/centres10/guava.jar" output/deep-marked-source

Then, in the aggregate memory-limited environment documented in BUILDING.md,
with the required modules already built:
  lake env lean --run validation/ring-chronology/DeepMarkedSource.lean \
    output/deep-marked-source [--native | --tree]

Use the host classpath separator (semicolon on Windows). No external corpus
is needed: both requests describe the same synthetic spiro graph and its mirror.
The output directory must be new.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("classpath", help="pinned classes directory and Guava jar")
    parser.add_argument("output", type=Path, help="new receipt directory")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "tools/centres10/release-1.0.json").read_text())
    packets = {}
    for name in ("original", "mirror"):
        payload = Path(__file__).with_name(f"{name}-root.req").read_text()
        result = json.loads(subprocess.check_output(
            [sys.executable, "-I", str(ROOT / "tools/centres10/run_pinned.py"),
             args.classpath, "--rule-prefixes"], input=payload, text=True))
        packets[name] = {"receipt": {"release": manifest["commit"],
            "molecularRequest": payload, "traces": result["traces"]},
            "observed": result["observed"]}
    args.output.mkdir(parents=True, exist_ok=False)
    for name, packet in packets.items():
        (args.output / f"{name}-root.source.json").write_text(json.dumps(packet) + "\n")

if __name__ == "__main__":
    main()
