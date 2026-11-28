"""Replay occurrence and sphere interventions on the published_metric_screen requests."""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, help="output from published_metric_screen.py")
    parser.add_argument("classpath", help="compiled adapters and pinned Centres dependencies")
    args = parser.parse_args()
    report = json.loads((args.directory / "report.json").read_text())
    if report["sdf_sha256"] != "28a000b36506dabe5a45f6d7672451c61c6e34f3e0f027f2599000d850273325":
        raise ValueError("unexpected source corpus")
    expected = {
        f"{r['name']}-atom{r['atom']}.req": r["published"]
        for r in report["results"] if r["published"]
    }
    vs280 = [name for name in expected if name.startswith("VS280-")]
    others = [name for name in expected if name not in vs280]
    if len(expected) != 129 or len(vs280) != 5:
        raise ValueError("incomplete published request manifest")

    def checked(command):
        proc = subprocess.run(
            ["java", "-Xmx512m", "-cp", args.classpath, *command],
            capture_output=True, text=True, check=True, timeout=300,
        )
        # The pinned Labeller catches assignment exceptions and writes to stderr.
        if proc.stderr:
            raise ValueError(proc.stderr)
        return proc.stdout.splitlines()

    calibration = checked(["CentresFusedLigands"])
    if calibration != ["128 frame inventories, 32 uniform reversals, 2048 occurrence-policy leaves"]:
        raise ValueError(f"fused calibration mismatch: {calibration}")
    print(calibration[0])
    for line in checked(["CentresSiteMetrics", "synthetic"]):
        print(line)

    def run(options, names):
        return checked(["CentresSiteMetrics", *options, *(str(args.directory / name) for name in names)])

    for scope, names, histogram in [("sphere", expected, {1: 116, 2: 8, 32: 5}),
                                    ("path", others, {1: 116, 2: 8})]:
        seen = set()
        counts = Counter()
        for line in run([scope, "32"], names):
            name, stock, active, _, leaves, labels = line.split("\t")
            if name in seen or not (stock == active == labels == expected[name]):
                raise ValueError(line)
            counts[int(leaves)] += 1
            seen.add(name)
        if seen != set(names) or counts != histogram:
            raise ValueError(f"{scope} cohort mismatch: {counts}")
        print(f"{scope}: {len(seen)} source labels, {sum(k*n for k,n in counts.items())} policy leaves")
    for line in run(["vs280"], vs280):
        print(line)


if __name__ == "__main__":
    main()
