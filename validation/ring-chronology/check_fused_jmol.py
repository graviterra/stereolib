"""Compare the construction-root arm formula with Jmol on 128 Cartesian models."""
import argparse
from collections import defaultdict
from pathlib import Path
import random
import re
import subprocess
import tempfile

from figure8_geometry import hand


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("classpath", help="compiled CentresFusedLigands and pinned Centres dependencies")
    parser.add_argument("jmol", type=Path, help="JmolData.jar")
    args = parser.parse_args()
    spec = subprocess.run(
        ["java", "-cp", args.classpath, "CentresFusedLigands", "--frames"],
        capture_output=True, text=True, check=True, timeout=30,
    )
    if spec.stderr:
        raise ValueError(spec.stderr)
    rows = [line.split() for line in spec.stdout.splitlines()]
    symbols = {1: "H", 6: "C", 8: "O"}
    elements = [symbols[int(row[1])] for row in rows if row[0] == "a"]
    bonds = [tuple(map(int, row[1:])) for row in rows if row[0] == "b"]
    frames = [tuple(map(int, row[1:])) for row in rows if row[0] == "f"]
    expected = {int(row[1]): row[2] for row in rows if row[0] == "p"}
    if len(elements) != 52 or len(frames) != 7 or set(expected) != set(range(128)):
        raise ValueError("incomplete fused graph input")
    generator = random.Random(491121)
    base = [tuple(generator.randint(-200, 200) for _ in range(3)) for _ in elements]

    with tempfile.TemporaryDirectory() as directory:
        commands = []
        for mask in range(128):
            points = base.copy()
            for j, (a, b, c, h) in enumerate(frames):
                want = "R" if mask & (1 << j) else "S"
                ids = [v + 1 for v in (a, b, c, h)]
                if hand(ids, points) != want:
                    # Inversion about a point in the first three carriers' plane
                    # reverses the signed distance of the private terminal H.
                    points[h] = tuple(x + y - z for x, y, z in zip(points[a], points[b], points[h]))
                if hand(ids, points) != want:
                    raise ValueError(f"frame mismatch at {mask}, {j}")
            file = Path(directory) / f"{mask}.mol"
            lines = [str(mask), "  TetraStereo     3D", "",
                     f"{len(elements):3}{len(bonds):3}  0  0  0  0            999 V2000"]
            for xyz, el in zip(points, elements):
                coords = "".join(f"{v / 20:10.4f}" for v in xyz)
                lines.append(f"{coords} {el:<3} 0  0  0  0  0  0  0  0  0  0  0  0")
            lines.extend(f"{a+1:3}{b+1:3}  1  0  0  0  0" for a, b in bonds)
            file.write_text("\n".join([*lines, "M  END", ""]))
            commands.extend([f'load "{file}"', "calculate chirality",
                             f'print "ROW {mask} [" + {{atomno=1}}.chirality + "]"'])
        script = Path(directory) / "fused.spt"
        script.write_text("\n".join([*commands, 'print "FUSED_COMPLETE"', ""]))
        result = subprocess.run(
            ["java", "-Xmx384m", "-Djava.awt.headless=true", "-jar", str(args.jmol), "-n", "-s", str(script)],
            capture_output=True, text=True, check=True, timeout=180,
        )
    labels = re.findall(r"^ROW (\d+) \[([RrSs]?)\]$", result.stdout, re.MULTILINE)
    actual = {int(mask): label or "unassigned" for mask, label in labels}
    if len(labels) != 128 or actual != expected or "FUSED_COMPLETE" not in result.stdout.splitlines():
        raise ValueError(f"Jmol disagreement: {[(k,v,actual.get(k)) for k,v in expected.items() if actual.get(k)!=v]}")
    if re.search(r"script error|exception", result.stdout + result.stderr, re.IGNORECASE):
        raise ValueError("Jmol emitted an exception or script error")
    # JmolData 14.32.10 writes each path in one-based physical atom numbers.
    paths = ["C1-C3", "C1-C3-C11-C7", "C1-C3-C11", "C1-C12", "C1-C12-C20-C16", "C1-C12-C20"]
    segments = re.split(r"^ROW (\d+) \[[RrSs]?\]$", result.stdout, flags=re.MULTILINE)
    for segment, mask in zip(segments[::2], segments[1::2]):
        observed = defaultdict(set)
        for label, path in re.findall(r"^creating aux ([RS]) for C\d+ = (C1(?:-C\d+)+)$", segment, re.MULTILINE):
            observed[path].add(label)
        for j, path in enumerate(paths):
            right = bool(int(mask) & (1 << (j + 1)))
            if j in (1, 4):  # far junction occurrences
                right = not right
            if observed[path] != {"R" if right else "S"}:
                raise ValueError(f"Jmol auxiliary disagreement at mask {mask}, path {path}: {observed[path]}")
    print("Jmol agrees at all 128 roots and all 768 specified auxiliary occurrences")


if __name__ == "__main__":
    main()
