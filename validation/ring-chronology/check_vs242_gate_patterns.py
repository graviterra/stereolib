"""Replay the 16 distal-agreement patterns of VS242 and their x reflections.

Run with python3 validation/ring-chronology/check_vs242_gate_patterns.py after
preparing the inputs pinned by check_figure14_regeneration. Bit i specifies
agreement at both distal donors of GATES[i], in the gate order 8, 20, 42, 51.
"""

import re
from collections import Counter
from decimal import Decimal
from pathlib import Path
from tempfile import TemporaryDirectory

from check_figure14_regeneration import molecule_record, pinned_inputs, require_equal
from check_vs242_cross_band import public_labels, root_words, trace_geometry
from vs242_branch_words import derive

# One-based (gate, near/far pairs); only the terminal Cl/H coordinates on
# each far carbon are exchanged. All four gate frames keep their coordinates.
GATES = [(8, [(5, 2), (10, 13)]), (20, [(22, 25), (29, 32)]),
         (42, [(44, 47), (67, 70)]), (51, [(53, 56), (60, 63)])]


def variant(original, hands, mask, reflected):
    lines = original.read_text().splitlines()
    bonds = [(int(row[:3]), int(row[3:6])) for row in lines[110:215]]
    for index, (_, pairs) in enumerate(GATES):
        for near, far in pairs:
            if (hands[near] == hands[far]) == bool(mask & (1 << index)):
                continue
            adjacent = [b if a == far else a for a, b in bonds if far in (a, b)]
            cl, = [i+3 for i in adjacent if lines[i+3][31:34].strip() == "Cl"]
            h, = [i+3 for i in adjacent if lines[i+3][31:34].strip() == "H"]
            lines[cl], lines[h] = lines[h][:30]+lines[cl][30:], lines[cl][:30]+lines[h][30:]
    if reflected:
        for i in range(4, 110):
            lines[i] = f"{-Decimal(lines[i][:10]):10.4f}" + lines[i][10:]
    return "\n".join(lines) + "\n"


def check(molecule, trace, mask, base_hands):
    words, hands, root, stage = derive(molecule)
    for index, (gate, pairs) in enumerate(GATES):
        require_equal(hands[gate], base_hands[gate])
        for near, far in pairs:
            require_equal(hands[near] == hands[far], bool(mask & (1 << index)))
    observations = re.findall(r"^creating aux ([RSrs]) for C(\d+) = C36-.*$", trace, re.MULTILINE)
    require_equal(sorted((int(i), h) for h, i in observations), sorted(hands.items()))
    require_equal(root_words(trace), {k: v for k, v in words.items() if stage != 6 or k[0] == 6})
    labels = dict(hands)
    if root:
        labels[36] = root
    require_equal(public_labels(trace), labels)
    summary = re.findall(r"^\s*C36-N(17|39)\t\(R\)[lu]+[^\n]*\n"
                         r"\s*(4b|5)\n\s*C36-N(17|39)\t\(R\)[lu]+", trace, re.MULTILINE)
    if stage is None:
        require_equal(summary, [])
    else:
        winner, loser = sorted((17, 39), key=lambda arm: words[stage, arm, "R"])
        require_equal(summary, [(str(winner), "4b" if stage == 6 else "5", str(loser))])
    return stage, root


def main():
    counts = Counter()
    with TemporaryDirectory() as scratch:
        directory = Path(scratch)
        jar, corpus, _ = pinned_inputs(directory)
        original, _ = molecule_record(corpus, "VS242", directory)
        _, base_hands, _, _ = derive(original)
        for mask in range(16):
            for reflected in (False, True):
                molecule = directory / f"pattern-{mask}-{int(reflected)}.mol"
                molecule.write_text(variant(original, base_hands, mask, reflected))
                trace = trace_geometry(directory, jar, molecule)
                try:
                    stage, root = check(molecule, trace, mask, base_hands)
                except ValueError as error:
                    raise ValueError(f"mask {mask}, reflected {reflected}: {error}") from error
                counts[stage, root] += 1
    require_equal(counts, {(6, "R"): 10, (6, "S"): 10, (8, "R"): 2, (8, "S"): 2, (None, ""): 8})
    print("32 VS242 geometries: Rule 4b (10 R, 10 S), Rule 5 (2 R, 2 S), 8 unassigned")


if __name__ == "__main__":
    main()
