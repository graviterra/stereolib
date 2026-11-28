"""Check C122 of published VS265 and a synthetic cyclopentane on the same arms.

The pinned SDF and Jmol runtime are shared with check_figure14_regeneration.
Atom numbers in the paths are one-based. Run this file with python3.
"""

import argparse
import hashlib
import re
from collections import Counter
from decimal import Decimal
from pathlib import Path
from tempfile import TemporaryDirectory

from check_figure14_regeneration import molecule_record, pinned_inputs, require_equal
from check_vs242_cross_band import public_labels, trace_geometry
from vs242_branch_words import branch_word, tetrahedral_hand

# Coordinates of the remodeled spectator ring and its attached terminal atoms,
# in original one-based numbering. C111, C112, C122 and both compared arms
# retain their published coordinates. C105 and C108 complete a five-member ring;
# their separation is 1.5300 angstroms. Remaining terminal bonds point away
# from the two ring neighbors at each site.
RING_POINTS = {
    105: (-1.8468, 0.4914, -0.1407), 106: (-2.8630, 0.8492, 0.0245),
    107: (-1.1617, 1.0273, 0.5163), 108: (-1.7893, -0.9990, 0.2003),
    109: (-1.0779, -1.1448, 1.0131), 110: (-2.7792, -1.3229, 0.5214),
    126: (-2.2724, 1.2379, -2.1599), 127: (-2.6095, -3.0258, -1.4883),
    128: (-0.4200, -2.3974, -0.8092), 137: (-0.5710, 1.4160, -1.6681),
}


def cyclopentane(lines):
    """Close C105–C108, removing one H at each end; preserve central atom IDs."""
    atoms = lines[4:141].copy()
    for i, xyz in RING_POINTS.items():
        atoms[i-1] = "".join(f"{v:10.4f}" for v in xyz) + atoms[i-1][30:]
    del atoms[132:134]  # H133 on C105 and H134 on C108
    bonds = []
    removed = []
    for row in lines[141:277]:
        a, b = int(row[:3]), int(row[3:6])
        if {a, b} & {133, 134}:
            removed.append(tuple(sorted((a, b))))
            continue
        new_a = a - 2 if a > 134 else a
        new_b = b - 2 if b > 134 else b
        bonds.append(f"{new_a:3}{new_b:3}" + row[6:])
    require_equal(sorted(removed), [(105, 133), (108, 134)])
    bonds.append("105108  1  0  0  0  0 ")
    header = ["VS265-synthetic-cyclopentane", *lines[1:3], "135135" + lines[3][6:]]
    content = "\n".join([*header, *atoms, *bonds, "M  END", ""])
    require_equal(hashlib.sha256(content.encode()).hexdigest(),
                  "910d295cc60ce37de4b967e621719d27f04e345ba13538c38cd86e75a49c19ce")
    return content


def derive(lines, cyclic):
    n, m = int(lines[3][:3]), int(lines[3][3:6])
    require_equal((n, m), (135, 135) if cyclic else (137, 136))
    elements = {i: row[31:34].strip() for i, row in enumerate(lines[4:4+n], 1)}
    points = {i: tuple(int(Decimal(row[k:k+10]) * 10000) for k in (0, 10, 20))
              for i, row in enumerate(lines[4:4+n], 1)}
    graph = {i: set() for i in elements}
    for row in lines[4+n:4+n+m]:
        a, b = int(row[:3]), int(row[3:6])
        require_equal(int(row[6:9]), 1)
        graph[a].add(b)
        graph[b].add(a)
    for i, element in elements.items():
        require_equal(len(graph[i]), {"H": 1, "C": 4, "Cl": 1}[element])

    if cyclic:
        # Check the closing edge before cutting it for the disjoint subtree walk.
        # Connectivity of the cut tree and the bond count prove the cycle unique.
        graph[105].remove(108)
        graph[108].remove(105)
    seen = {122}

    def children(site, parent, expected):
        ids = graph[site] - {parent}
        require_equal(Counter(elements[i] for i in ids), Counter(expected.split()))
        if seen & ids:
            raise ValueError(f"Revisited atom below {site}")
        seen.update(ids)
        return {el: sorted(i for i in ids if elements[i] == el) for el in expected.split()}

    def path_hand(path, frame, lower=False):
        h = tetrahedral_hand(points, frame)
        hands[path] = h.lower() if lower else h
        return hands[path]

    root = children(122, None, "C C C C")
    require_equal(root["C"], [111, 112, 114, 119])
    # C111 wins by its directly attached chlorine.
    ch = children(111, 122, "Cl C H")
    methyl, = ch["C"]
    require_equal(methyl, 108)
    children(methyl, 111, "H H" if cyclic else "H H H")
    ethyl, = children(112, 122, "C H H")["C"]
    require_equal(ethyl, 105)
    children(ethyl, 112, "H H" if cyclic else "H H H")
    chlorine_hand = tetrahedral_hand(points, [*ch["Cl"], 122, methyl, *ch["H"]])
    words, hands = {}, {}
    for arm in (114, 119):
        path = (122, arm)
        for _ in range(3):
            child, = children(path[-1], path[-2], "C H H")["C"]
            path += (child,)
        first = children(path[-1], path[-2], "C C H")
        groups, rows, far_sites = [], [], []
        for stem in first["C"]:
            gate, = children(stem, path[-1], "C H H")["C"]
            gate_path = (*path, stem, gate)
            split = children(gate, stem, "C C H")
            branches = []
            for near in split["C"]:
                ch = children(near, gate, "Cl C H")
                far, = ch["C"]
                end = children(far, near, "Cl C H")
                methyl, = end["C"]
                children(methyl, far, "H H H")
                near_hand = path_hand((*gate_path, near), [*ch["Cl"], far, gate, *ch["H"]])
                far_hand = path_hand((*gate_path, near, far), [*end["Cl"], near, methyl, *end["H"]])
                branches.append((near_hand, far_hand, near))
                far_sites.append((near_hand, (*gate_path, near, far)))
            branches.sort()
            require_equal([h for h, _, _ in branches], ["R", "S"])
            require_equal({h for _, h, _ in branches}, {"R", "S"})
            # The enantiomorphic chlorinated arms outrank the CH2 stem.
            gate_hand = path_hand(gate_path, [*(n for _, _, n in branches), stem, *split["H"]], True)
            rows.extend((gate_hand, a, b) for a, b, _ in branches)
            groups.append((branches[0][0] == branches[0][1], stem))
        require_equal(Counter(g for g, _, _ in rows), Counter("rrss"))
        # At the first donor, both forward CH2 groups lead to CH(CHCl)2,
        # outranking the returning chain of CH2 groups. The same-hand distal
        # pair has Rule 4b word lulu against luul for the opposite-hand pair.
        groups.sort(reverse=True)
        require_equal([agree for agree, _ in groups], [True, False])
        first_hand = path_hand(path, [*(stem for _, stem in groups), path[-2], *first["H"]])
        for stage in (6, 8):
            for ref in "RS":
                prefix = "l" if first_hand == ref else "u"
                words[stage, arm, ref] = prefix + branch_word(rows, ref, stage)
        for ref in "RS":
            # In the r band the near donor like to this reference ranks first.
            # Its own distal child occupies the first index of sphere eight.
            first_distal, = [p for near_h, p in far_sites if hands[p[:-2]] == "r" and near_h == ref]
            require_equal(first_distal[-3], 7 if arm == 114 else 38)
            require_equal(hands[first_distal] == ref, arm == 114)
        depths = Counter(len(p) - 1 for p, h in hands.items() if p[1] == arm and h in "RS")
        require_equal(depths, {4: 1, 7: 4, 8: 4})
    require_equal(seen, set(elements))
    for ref in "RS":
        require_equal(words[6, 114, ref], words[6, 119, ref])
        a, b = (words[8, arm, ref] for arm in (114, 119))
        require_equal(a[:5], b[:5])
        require_equal((a[5], b[5]), ("l", "u"))
    labels = {path[-1]: h for path, h in hands.items()}
    labels[111] = chlorine_hand
    # The ring route through C112 reaches chlorine while the paired arms
    # still reach carbon. In the open structure the ethyl route ends first.
    order = [111, 112, 114, 119] if cyclic else [111, 114, 119, 112]
    labels[122] = tetrahedral_hand(points, order)
    return words, hands, labels


def read_word(raw):
    """Jmol compacts consecutive like indices as inclusive ranges."""
    indices = []
    for token in raw.split():
        first, *last = map(int, token.split(":"))
        if len(last) > 1 or not 0 <= first <= (last[0] if last else first) < 9:
            raise ValueError(f"Invalid VS265 like-index token {token}")
        indices.extend(range(first, (last[0] if last else first) + 1))
    require_equal(indices, sorted(set(indices)))
    return "".join("l" if i in indices else "u" for i in range(9))


def check(directory, jar, molecule, expected, cyclic):
    words, hands, labels = derive(molecule.read_text().splitlines(), cyclic)
    require_equal(labels, expected)
    trace = trace_geometry(directory, jar, molecule)
    require_equal(public_labels(trace, 135 if cyclic else 137), labels)
    root_block, = re.findall(r"^C122\n\n(.+?)\n\n", trace, re.MULTILINE | re.DOTALL)
    order = re.findall(r"^\tC(\d+)\t-+$", root_block, re.MULTILINE)
    require_equal(order, ["111", "112", "114", "119"] if cyclic else ["111", "114", "119", "112"])
    observed_hands = []
    for h, atom, raw_path in re.findall(r"^creating aux ([RSrs]) for C(\d+) = (C122-(?:C114|C119)-\S+)$",
                                        trace, re.MULTILINE):
        path = tuple(int(v[1:]) for v in raw_path.split("-"))
        require_equal(path[-1], int(atom))
        observed_hands.append((path, h))
    require_equal(sorted(observed_hands), sorted(hands.items()))
    readings = []
    for stage, arm, r, s in re.findall(r"^getBest (\d+) C(114|119) \(\{([^}]*)\}\)\(\{([^}]*)\}\) C122-C\2$",
                                       trace, re.MULTILINE):
        readings.extend([((int(stage), int(arm), ref), read_word(raw)) for ref, raw in zip("RS", (r, s))])
    require_equal(sorted(readings), sorted(words.items()))
    summary = re.findall(r"^\s*C122-C114\t\(R\)([lu]+)  \(S\)([lu]+)\n\s*5\n\s*C122-C119\t\(R\)([lu]+)  \(S\)([lu]+)$",
                         trace, re.MULTILINE)
    require_equal(summary, [tuple(words[8, arm, ref] for arm in (114, 119) for ref in "RS")])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export-cyclic", type=Path, metavar="FILE", help="write the synthetic V2000 molfile")
    args = parser.parse_args()
    with TemporaryDirectory() as scratch:
        directory = Path(scratch)
        jar, corpus, _ = pinned_inputs(directory)
        molecule, fields = molecule_record(corpus, "VS265", directory)
        labels = {int(i): h for i, h in re.findall(r"(\d+)([RSrs])", fields.split("> <CIP_LABELS>\n")[1].splitlines()[0])}
        require_equal((len(labels), labels[122]), (24, "S"))
        synthetic = directory / "VS265-cyclopentane.mol"
        content = cyclopentane(molecule.read_text().splitlines())
        synthetic.write_text(content)
        for model, cyclic in ((molecule, False), (synthetic, True)):
            check(directory, jar, model, labels, cyclic)
            lines = model.read_text().splitlines()
            for i in range(4, 4 + int(lines[3][:3])):
                lines[i] = f"{-Decimal(lines[i][:10]):10.4f}" + lines[i][10:]
            mirror = directory / "mirror.mol"
            mirror.write_text("\n".join(lines) + "\n")
            reflected = {i: h.translate(str.maketrans("RS", "SR")) for i, h in labels.items()}
            check(directory, jar, mirror, reflected, cyclic)
        if args.export_cyclic:
            args.export_cyclic.write_bytes(content.encode())
    print("Published VS265 and synthetic cyclopentane: 96 labels; depths 4, 7, 8; Rule 5 at depth 8; C122 S/R")


if __name__ == "__main__":
    main()
