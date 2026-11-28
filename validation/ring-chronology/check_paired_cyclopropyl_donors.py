"""Check a constructed pair of cyclic ligands with a third-sphere Rule 4b decision.

The supplied V2000 file has two identical cyclopropyl frameworks, each carrying
a CH(Cl)Br donor. Numbering is one-based. Run this file with python3 after
preparing the Jmol release jars used by check_figure14_regeneration.
Only JMOL_JAR and JMOL_SOURCES are needed; no Hanson SDF is required.
"""

import argparse
import hashlib
import re
import subprocess
from collections import Counter
from decimal import Decimal
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from check_figure14_regeneration import LAUNCHER, pinned, pinned_jmol_inputs, require_equal
from check_vs242_cross_band import public_labels, trace_geometry
from vs242_branch_words import tetrahedral_hand

FIXTURE = Path(__file__).with_name("PairedCyclopropylDonors.mol")


def derive(lines):
    require_equal((int(lines[3][:3]), int(lines[3][3:6])), (25, 26))
    elements = [row[31:34].strip() for row in lines[4:29]]
    require_equal(elements, ["C", "F", "H"] + ["C", "C", "C", "H", "H", "H", "H", "C", "H", "Cl", "Br"] * 2)
    points = {i: tuple(int(Decimal(row[k:k + 10]) * 10000) for k in (0, 10, 20))
              for i, row in enumerate(lines[4:29], 1)}
    bonds = []
    for row in lines[29:55]:
        a, b = int(row[:3]), int(row[3:6])
        require_equal(int(row[6:9]), 1)
        bonds.append(tuple(sorted((a, b))))
    expected_bonds = [(1, 2), (1, 3)]
    words, paths, labels = {}, {}, {}
    for a in (4, 15):
        b, c = a + 1, a + 2  # three-membered ring a-b-c-a
        d = a + 7             # distal CH(Cl)Br attached to b
        expected_bonds.extend([(1, a), (a, b), (b, c), (a, c), (a, a+3),
                               (b, a+4), (c, a+5), (c, a+6), (b, d),
                               (d, d+1), (d, d+2), (d, d+3)])

        # At a, the C1 substituent bearing F outranks b (C,C,H), then c (C,H,H).
        # At b, d bears Br and Cl. On the short path a is the real predecessor
        # and outranks c. On the detour via c, the forward copy of a is a ring
        # closure duplicate with no real descendants, so c outranks that copy.
        near = tetrahedral_hand(points, [1, b, c, a+3])
        direct = tetrahedral_hand(points, [d, a, c, a+4])
        detour = tetrahedral_hand(points, [d, c, a, a+4])
        far = tetrahedral_hand(points, [d+3, d+2, b, d+1])
        labels.update({a: near, b: direct, d: far})

        # At depth three the direct path via senior b precedes the detour via c.
        ordered = [((1, a), near), ((1, a, b), direct), ((1, a, b, d), far),
                   ((1, a, c, b), detour), ((1, a, c, b, d), far)]
        paths.update(ordered)
        for ref in "RS":
            words[a, ref] = "".join("l" if h == ref else "u" for _, h in ordered)

    require_equal(sorted(bonds), sorted(expected_bonds))
    # Lowercase l precedes u in Python. After an own-reference tie compare
    # the R-reference words; complementary arms then give a lowercase center.
    best = {a: min("RS", key=lambda ref: words[a, ref]) for a in (4, 15)}
    keys = [words[a, best[a]] for a in (4, 15)]
    if keys[0] != keys[1]:
        stage = "4b"
    else:
        stage = "5"
        keys = [words[a, "R"] for a in (4, 15)]
    if keys[0] == keys[1]:
        return words, best, paths, labels, None
    winner, loser = (4, 15) if keys[0] < keys[1] else (15, 4)
    hand = tetrahedral_hand(points, [2, winner, loser, 3])
    labels[1] = hand if stage == "4b" else hand.lower()
    return words, best, paths, labels, (winner, stage, loser)


def check_trace(lines, trace):
    words, best, paths, labels, decision = derive(lines)
    require_equal(public_labels(trace, 25), labels)
    observed = []
    for h, atom, raw in re.findall(r"^creating aux ([RSrs]) for C(\d+) = (C1-\S+)$", trace, re.MULTILINE):
        path = tuple(int(x[1:]) for x in raw.split("-"))
        require_equal(path[-1], int(atom))
        observed.append((path, h))
    require_equal(sorted(observed), sorted(paths.items()))

    readings = []
    rows = re.findall(r"^getBest (\d+) C(4|15) \(\{([^}]*)\}\)\(\{([^}]*)\}\) C1-C\2$", trace, re.MULTILINE)
    for stage, arm, right, left in rows:
        require_equal(stage, "6")
        for ref, raw in zip("RS", (right, left)):
            indices = []
            for token in raw.split():
                first, _, last = token.partition(":")
                lo, hi = int(first), int(last or first)
                require_equal(0 <= lo <= hi < 5, True)
                indices.extend(range(lo, hi + 1))
            require_equal(indices, sorted(set(indices)))
            readings.append(((int(arm), ref), "".join("l" if i in indices else "u" for i in range(5))))
    require_equal(sorted(readings), sorted(words.items()))
    summary = re.findall(r"^\s*C1-C(4|15)\t\([RS]\)[lu]+[^\n]*\n\s*(4b|5)\n\s*C1-C(4|15)\t\([RS]\)[lu]+",
                         trace, re.MULTILINE)
    require_equal([(int(a), rule, int(b)) for a, rule, b in summary], [decision] if decision else [])
    return words, best, labels, decision


def check_original(directory, jar, model):
    words, best, labels, decision = check_trace(model.read_text().splitlines(), trace_geometry(directory, jar, model))
    require_equal(decision, (4, "4b", 15))
    require_equal((words[4, best[4]], words[15, best[15]]), ("lllul", "lluuu"))
    return labels


# Priority-ordered heavy carriers and the private terminal H at C4,C5,C11 and
# C15,C16,C22. These coordinates leave the C1 frame and all heavy atoms fixed.
FRAMES = [(1, 5, 6, 7), (11, 4, 6, 8), (14, 13, 5, 12),
          (1, 16, 17, 18), (22, 15, 17, 19), (25, 24, 16, 23)]


def write_pattern(fixture_lines, model, target):
    lines = fixture_lines.copy()
    for frame, hand in zip(FRAMES, target, strict=True):
        points = {i: tuple(Decimal(lines[i+3][k:k+10]) for k in (0, 10, 20)) for i in frame}
        if tetrahedral_hand(points, frame) != hand:
            # Inversion through the three-heavy-carrier centroid reverses the
            # oriented volume. Recheck the hand after rounding to V2000 precision.
            h = frame[-1]
            xyz = [2 * sum(points[i][k] for i in frame[:3])/3 - points[h][k] for k in range(3)]
            lines[h+3] = "".join(f"{x:10.4f}" for x in xyz) + lines[h+3][30:]
            points[h] = tuple(Decimal(lines[h+3][k:k+10]) for k in (0, 10, 20))
            require_equal(tetrahedral_hand(points, frame), hand)
    model.write_text("\n".join(lines) + "\n")


def write_mirror(model, mirror):
    lines = model.read_text().splitlines()
    for i in range(4, 29):
        lines[i] = f"{-Decimal(lines[i][:10]):10.4f}" + lines[i][10:]
    mirror.write_text("\n".join(lines) + "\n")


def check_patterns(directory, jar, fixture, export, family):
    patterns = list(map("".join, product("RS", repeat=3)))
    fixture_lines = fixture.read_text().splitlines()
    destination = export.resolve() if export else directory
    destination.mkdir(parents=True, exist_ok=True)
    models, commands = {}, []
    for a, b in product(patterns, repeat=2):
        model = destination / f"{a}-{b}.mol"
        write_pattern(fixture_lines, model, a+b)
        mirror = directory / f"{a}-{b}-mirror.mol"
        write_mirror(model, mirror)
        for geometry, path in (("original", model), ("mirror", mirror)):
            models[a, b, geometry] = path
            commands.extend([f'print "BEGIN {a} {b} {geometry}"', f'load "{path}"',
                             "set cipRule6Full false", "calculate chirality",
                             "for (var j=1; j <= 25; j++) {",
                             "var v = {atomno=j}.chirality",
                             'if (v != "") {print "LABEL " + j + v}', "}", 'print "END_PATTERN"'])
    script = directory / "all.spt"
    script.write_text("\n".join(commands + ['print "ALL_COMPLETE"', ""]))
    result = subprocess.run(["java", "-Xmx256m", "-Djava.awt.headless=true", "-cp", str(jar),
                             str(directory / LAUNCHER), "-nos", str(script)], text=True,
                            stdout=subprocess.PIPE, check=True, timeout=120)
    require_equal(result.stdout.splitlines().count("ALL_COMPLETE"), 1)
    observations = re.findall(r"^BEGIN ([RS]{3}) ([RS]{3}) (original|mirror)\n(.*?)^END_PATTERN$",
                              result.stdout, re.MULTILINE | re.DOTALL)
    require_equal([(a, b, geometry) for a, b, geometry, _ in observations], list(models))
    counts = Counter()
    original_labels = {}
    swap = str.maketrans("RS", "SR")
    for a, b, geometry, trace in observations:
        model = models[a, b, geometry]
        _, best, labels, decision = check_trace(model.read_text().splitlines(), trace)
        if geometry == "original":
            original_labels[a, b] = labels
        else:
            require_equal(labels, {i: h.translate(swap) for i, h in original_labels[a, b].items()})
            a, b = a.translate(swap), b.translate(swap)
        require_equal("".join(labels[i] for i in (4, 5, 11, 15, 16, 22)), a+b)
        require_equal((best[4], best[15]), (a[0], b[0]))
        key_a, key_b = [(t[0] == t[1], t[0] == t[2]) for t in (a, b)]
        if a == b:
            expected = None
        elif key_a == key_b:
            require_equal(all(x != y for x, y in zip(a, b)), True)
            expected = (4, "5", 15) if a[0] == "R" else (15, "5", 4)
        else:
            expected = (4, "4b", 15) if key_a > key_b else (15, "4b", 4)
        require_equal(decision, expected)
        counts[labels.get(1, "")] += 1
    require_equal(counts, {"R": 48, "S": 48, "r": 8, "s": 8, "": 16})
    if family:
        records = []
        for a, b in product(patterns, repeat=2):
            lines = models[a, b, "original"].read_text().splitlines()
            lines[0] = f"{a}-{b}"
            records.append("\n".join(lines).rstrip("\n") + "\n$$$$\n")
        content = "".join(records).encode()
        require_equal(hashlib.sha256(content).hexdigest(),
                      "cf6af652cba05cef4ee12f5eb66e0718e837625eda460829e9781ae83d75d7fb")
        family.write_bytes(content)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export-patterns", type=Path, metavar="DIR", help="write all 64 synthetic V2000 models")
    parser.add_argument("--export-family", type=Path, metavar="SDF", help="write one pinned 64-record SDF")
    args = parser.parse_args()
    fixture = pinned(FIXTURE, "630c05ba50ea667ef31886264ad55c4ef30876f1cbcccde6e34a0c8f68aa9356")
    with TemporaryDirectory() as scratch:
        directory = Path(scratch)
        jar, _ = pinned_jmol_inputs(directory)
        original = check_original(directory, jar, fixture)
        require_equal(original[1], "R")
        mirror = directory / "mirror.mol"
        write_mirror(fixture, mirror)
        require_equal(check_original(directory, jar, mirror), {i: "S" if h == "R" else "R" for i, h in original.items()})
        check_patterns(directory, jar, fixture, args.export_patterns, args.export_family)
    print("Paired cyclopropyl donors: C1 R/S; 64 patterns and their mirrors give 48 R, 48 S, 8 r, 8 s, and 16 unassigned")


if __name__ == "__main__":
    main()
