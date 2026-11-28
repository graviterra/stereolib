"""Exact coordinate and branch-count calculation for the two-layer VS242 scaffold.

For this tree, Rule 4b pools the two gates and Rule 5 visits r before s.
Within each band, like near donors precede unlike near donors. Each near
donor has one distal donor; within each near class like distal donors precede
unlike ones. These ordering conventions are inputs to the calculation.
"""

from collections import Counter
from decimal import Decimal

from check_figure14_regeneration import require_equal


def tetrahedral_hand(points, carriers):
    """Compute the hand of four carriers listed in decreasing priority."""
    a, b, c, d = (points[i] for i in carriers)
    a, b, c = ([x - y for x, y in zip(point, d)] for point in (a, b, c))
    det = sum(a[i] * (b[(i + 1) % 3] * c[(i + 2) % 3]
                      - b[(i + 2) % 3] * c[(i + 1) % 3]) for i in range(3))
    if det == 0:
        raise ValueError(f"Coplanar carriers {carriers}")
    return "R" if det < 0 else "S"


def branch_word(rows, ref, stage):
    """Count matches on each sphere independently and concatenate spheres."""
    bands = [rows] if stage == 6 else [[row for row in rows if row[0] == g] for g in "rs"]
    near, distal = [], []
    for band in bands:
        for like in (True, False):
            children = [far for _, parent, far in band if (parent == ref) == like]
            near.append(("l" if like else "u") * len(children))
            matches = children.count(ref)
            distal.append("l" * matches + "u" * (len(children) - matches))
    return "".join(near + distal)


def derive(molecule):
    """Return the independent reference words, root-relative hands and C36 hand."""
    lines = molecule.read_text().splitlines()
    require_equal((int(lines[3][:3]), int(lines[3][3:6])), (106, 105))
    atoms = {i: row[31:34].strip() for i, row in enumerate(lines[4:110], 1)}
    # The pinned V2000 coordinates have four decimal places. Integer determinants
    # preserve their sign after multiplication by the same positive scale.
    points = {i: tuple(int(Decimal(row[k:k+10]) * 10000) for k in (0, 10, 20))
              for i, row in enumerate(lines[4:110], 1)}
    adj = {i: set() for i in atoms}
    for row in lines[110:215]:
        a, b = int(row[:3]), int(row[3:6])
        require_equal(int(row[6:9]), 1)
        adj[a].add(b)
        adj[b].add(a)

    # Visit the entire graph exactly once to exclude returns and shared donors.
    seen = {36}

    def children(site, parent, expected):
        ids = adj[site] - {parent}
        require_equal(Counter(atoms[i] for i in ids), Counter(expected))
        if ids & seen:
            raise ValueError(f"Overlapping branches at atom {site}")
        seen.update(ids)
        return {el: sorted(i for i in ids if atoms[i] == el) for el in set(expected)}

    root = children(36, None, ["O", "N", "N", "H"])
    require_equal(root["N"], [17, 39])
    oxygen, = root["O"]
    children(oxygen, 36, ["H"])
    words, hands = {}, {}
    for arm in root["N"]:
        rows = []
        for stem in children(arm, 36, ["C", "C"])["C"]:
            gate, = children(stem, arm, ["C", "H", "H"])["C"]
            split = children(gate, stem, ["C", "C", "H"])
            branches = []
            for near in split["C"]:
                first = children(near, gate, ["Cl", "C", "H"])
                far, = first["C"]
                last = children(far, near, ["Cl", "C", "H"])
                methyl, = last["C"]
                children(methyl, far, ["H", "H", "H"])
                # Cl wins. At each donor, the adjacent chlorinated carbon wins
                # over the other carbon. At the gate the chlorinated arms win
                # over CH2N, and the R arm wins over its S counterpart.
                hands[near] = tetrahedral_hand(points, [*first["Cl"], far, gate, *first["H"]])
                hands[far] = tetrahedral_hand(points, [*last["Cl"], near, methyl, *last["H"]])
                branches.append((near, far))
            branches.sort(key=lambda pair: hands[pair[0]])
            require_equal([hands[a] for a, _ in branches], ["R", "S"])
            # The two arms also have opposite distal hands, so the pair is
            # enantiomorphic. This is required for a lowercase gate descriptor.
            require_equal({hands[b] for _, b in branches}, {"R", "S"})
            hands[gate] = tetrahedral_hand(points, [*(a for a, _ in branches), stem, *split["H"]]).lower()
            rows.extend((hands[gate], hands[a], hands[b]) for a, b in branches)
        require_equal(Counter(row[0] for row in rows), Counter("rrss"))
        for stage in (6, 8):
            for ref in "RS":
                words[stage, arm, ref] = branch_word(rows, ref, stage)
    require_equal(seen, set(atoms))
    for atom, element in atoms.items():
        if element in {"Cl", "H"}:
            require_equal(len(adj[atom]), 1)
    for stage in (6, 8):
        for arm in root["N"]:
            require_equal(words[stage, arm, "R"], words[stage, arm, "S"])
        left, right = (words[stage, arm, "R"] for arm in root["N"])
        if left != right:
            # Python orders l before u, so the smaller word wins.
            arms = [17, 39] if left < right else [39, 17]
            hand = tetrahedral_hand(points, [oxygen, *arms, *root["H"]])
            return words, hands, hand, stage
    return words, hands, "", None
