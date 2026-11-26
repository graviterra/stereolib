"""Measure Jmol's C27 assignment for every ordered pair of VS262 arm orbits."""

import argparse
import hashlib
import re
import subprocess
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory

from figure8_geometry import hand
from figure8_stereoisomers import enumerate_arm, motif_model
from hanson_figure8_sdf import ARM_PATHS, read_record, require

JMOL = "6d760b21af0c87ba5e6b6304f7c37b96f7412700a40e07b524402cc22914cf07"
LAUNCHER = "159385595e2936abe9373c4ef5e61f95a406860fb5054b42a51d30a5bb9e3423"
SYMBOL = {1: "H", 6: "C", 7: "N", 8: "O", 17: "Cl"}


@dataclass
class ArmFamily:
    signatures: list
    mirror: list[int]
    coordinates: list[dict]
    priorities: list
    raw_branches: list[tuple]
    branch_types: list[tuple[int, int]]


def branch_observations(atoms, graph, route, hands, points):
    """Translate physical hands into the two branch codes used by the Lean theorem."""
    nitrogen = route[-1]
    codes = []
    raw = []

    def only_element(neighbors, z):
        v, = [j for j in neighbors if atoms[j - 1] == z]
        return v

    def negative(order):
        return int(hand(order, points) == "R")

    for proximal in graph[nitrogen]:
        if proximal == route[-2]:
            continue
        middle, = (v for v in graph[proximal] if atoms[v - 1] == 6)
        tip_ids = sorted(v for v in graph[middle] if v != proximal and atoms[v - 1] == 6)
        tips = [hands[v] for v in tip_ids]
        proximal_sign = negative([nitrogen, only_element(graph[proximal], 17),
                                  only_element(graph[proximal], 1), middle])
        central_sign = negative([proximal, only_element(graph[middle], 1), *tip_ids])
        distal_signs = []
        for tip in tip_ids:
            children = [w for w in graph[tip] if w != middle]
            distal_signs.append(negative([middle, only_element(children, 17),
                                          only_element(children, 1), only_element(children, 6)]))
        raw.append((proximal_sign, central_sign, *distal_signs))
        require(len(tips) == 2 and all(h in ("R", "S") for h in tips), "Unexpected distal frame")
        if tips[0] == tips[1]:
            require(middle not in hands, "Identical distal arms carry a middle descriptor")
            distal = int(tips[0] == "R")
        else:
            distal = {"r": 2, "s": 3}[hands[middle]]
        codes.append(4 * int(hands[proximal] == "R") + distal)
    a, b = sorted(codes)
    return tuple(raw), (a, b)


def representatives(atoms, graph, xyz, route):
    root, start = route[:2]
    vertices, rows = enumerate_arm(atoms, graph, start, root)
    assignments = {}
    mirrors = {}
    for values, key, mirror in rows:
        assignments.setdefault(key, values)
        mirrors[key] = mirror
    keys = sorted(assignments)
    index = {key: i for i, key in enumerate(keys)}
    parent = {start: root}
    traversal = [start]
    for v in traversal:
        children = [w for w in graph[v] if w != parent[v]]
        parent.update((w, v) for w in children)
        traversal.extend(children)

    def subtree_swap(points, a, b):
        require(atoms[a - 1] == atoms[b - 1], "Subtrees have different elements")
        points[a - 1], points[b - 1] = points[b - 1], points[a - 1]
        def children(v):
            return sorted((w for w in graph[v] if w != parent[v]),
                          key=lambda w: (atoms[w - 1], len(graph[w]), w))
        left, right = children(a), children(b)
        require(len(left) == len(right), "Subtrees have different degrees")
        for x, y in zip(left, right):
            subtree_swap(points, x, y)

    def orientation(points, v):
        frame = [parent[v], *sorted(w for w in graph[v] if w != parent[v])]
        return -1 if hand(frame, points) == "R" else 1

    physical_hands, motif = motif_model(atoms, graph)
    priorities = []
    types = []
    raw_branches = []
    geometries = []
    for key in keys:
        wanted = dict(zip(vertices, assignments[key]))
        points = xyz.copy()
        for v in traversal:
            if v not in wanted or orientation(points, v) == wanted[v]:
                continue
            children = [w for w in graph[v] if w != parent[v]]
            leaves = [w for w in children if atoms[w - 1] in (1, 17)]
            if len(leaves) == 2:
                require({atoms[w - 1] for w in leaves} == {1, 17}, "Expected H and Cl")
                a, b = leaves
                points[a - 1], points[b - 1] = points[b - 1], points[a - 1]
            else:
                carbons = [w for w in children if atoms[w - 1] == 6]
                require(len(carbons) == 2, "Expected two equivalent terminal branches")
                subtree_swap(points, *carbons)
        require(all(orientation(points, v) == wanted[v] for v in vertices),
                "Coordinates do not encode the selected representative")
        hands = physical_hands(start, root, vertices, assignments[key])
        priorities.append(motif(start, root, hands)[0])
        raw, branch_types = branch_observations(atoms, graph, route, hands, points)
        raw_branches.append(raw)
        types.append(branch_types)
        geometries.append({v: points[v - 1] for v in traversal})
    return ArmFamily(keys, [index[mirrors[key]] for key in keys], geometries, priorities, raw_branches, types)


def mol_block(atoms, graph, xyz, title):
    edges = [(a, b) for a in graph for b in graph[a] if a < b]
    lines = [title, "  VS262             3D", "",
             f"{len(atoms):3}{len(edges):3}  0  0  0  0            999 V2000"]
    for z, pos in zip(atoms, xyz):
        coords = "".join(f"{x/10000:10.4f}" for x in pos)
        lines.append(f"{coords} {SYMBOL[z]:<3} 0  0  0  0  0  0  0  0  0  0  0  0")
    lines.extend(f"{a:3}{b:3}  1  0  0  0  0" for a, b in edges)
    return "\n".join([*lines, "M  END", ""])


def run(sdf, jar, launcher, log, lean_scores=None):
    for file, digest in ((jar, JMOL), (launcher, LAUNCHER)):
        require(hashlib.sha256(file.read_bytes()).hexdigest() == digest, f"Unexpected {file}")
    atoms, graph, xyz, _ = read_record(sdf)
    left = representatives(atoms, graph, xyz, ARM_PATHS["A"])
    right = representatives(atoms, graph, xyz, ARM_PATHS["B"])
    require(left.signatures == right.signatures and left.mirror == right.mirror and
            len(left.signatures) == 36, "Arm orbit mismatch")
    require(left.priorities == right.priorities and left.branch_types == right.branch_types,
            "Equivalent arm classes differ under motif ranking")
    require(not (left.coordinates[0].keys() & right.coordinates[0].keys()), "The tested arms overlap")
    mirror = left.mirror
    with TemporaryDirectory(prefix="vs262-orbits-") as name:
        tmp = Path(name)
        commands = []
        for i, a in enumerate(left.coordinates):
            for j, b in enumerate(right.coordinates):
                points = xyz.copy()
                for v, p in (a | b).items():
                    points[v - 1] = p
                filename = f"pair-{i}-{j}.mol"
                (tmp / filename).write_text(mol_block(atoms, graph, points, filename))
                commands.extend([f'load "{filename}"', 'calculate chirality',
                                 f'print "VS262_PAIR {i} {j} [" + {{atomno=27}}.chirality + "]"'])
        (tmp / 'orbit.spt').write_text('\n'.join(commands + ['quit']) + '\n')
        with log.open('w') as out:
            subprocess.run(['java', '-Xmx256m', '-Djava.awt.headless=true', '-cp', str(jar.resolve()),
                            str(launcher.resolve()), '-nos', 'orbit.spt'], check=True, cwd=tmp,
                           stdout=out, stderr=subprocess.STDOUT)
    observed = {}
    for line in log.read_text().splitlines():
        match = re.fullmatch(r'VS262_PAIR (\d+) (\d+) \[([^\]]*)\]', line.strip())
        if match:
            i, j, letter = match.groups()
            pair = int(i), int(j)
            require(pair not in observed, f"Repeated pair {pair}")
            observed[pair] = letter
    require(set(observed) == {(i, j) for i in range(36) for j in range(36)},
            f"Expected 1296 measurements, found {len(observed)}")
    print("All ordered pairs", dict(Counter(observed.values())))
    for kind, pred in [('isomorphic', lambda i, j: i == j),
                       ('distinct mirror partners', lambda i, j: i != j and mirror[i] == j),
                       ('other distinct pairs', lambda i, j: i != j and mirror[i] != j)]:
        print(kind, dict(Counter(label for (i,j), label in observed.items() if pred(i,j))))
    assert_directions(atoms, graph, xyz, mirror, left.priorities, observed)
    if lean_scores is not None:
        table = {}
        branches = {}
        for row in lean_scores.read_text().splitlines():
            kind, *values = row.split()
            *indices, value = map(int, values)
            storage = {"branch": branches, "arm": table}[kind]
            key = tuple(indices)
            require(key not in storage, "Repeated Lean table entry")
            storage[key] = value
        require(len(branches) == 16, "Incomplete Lean branch table")
        for family in (left, right):
            decoded = [tuple(sorted(branches[b] for b in arm)) for arm in family.raw_branches]
            require(decoded == family.branch_types, "Determinant sign frames disagree with Lean branch codes")
        require(len(table) == 36 and set(left.branch_types) == set(table), "Incomplete Lean score table")
        print("Checking the Lean priority for all represented pairs")
        assert_directions(atoms, graph, xyz, mirror, [table[t] for t in left.branch_types], observed)
    return observed


def assert_directions(atoms, graph, xyz, mirror, priority, observed):
    root, a = ARM_PATHS["A"][:2]
    _, b = ARM_PATHS["B"][:2]
    oxygen, = (i for i in graph[root] if atoms[i - 1] == 8)
    hydrogen, = (i for i in graph[root] if atoms[i - 1] == 1)
    arm_a_first = hand([oxygen, a, b, hydrogen], xyz)
    arm_b_first = hand([oxygen, b, a, hydrogen], xyz)
    wrong = []
    for (i, j), actual in observed.items():
        require((actual == "") == (i == j), f"Orbit equivalence mismatch at {(i, j)}")
        require(actual.islower() == (i != j and mirror[i] == j),
                f"Mirror-pair casing mismatch at {(i, j)}")
        predicted = ""
        if priority[i] != priority[j]:
            a_wins = priority[i] > priority[j]
            predicted = arm_a_first if a_wins else arm_b_first
            if a_wins != (priority[mirror[i]] > priority[mirror[j]]):
                predicted = predicted.lower()
        if actual != predicted:
            wrong.append((i, j, predicted, actual))
    print(f"Exact root label comparison: {len(wrong)} disagreements in {len(observed)} rows")
    require(not wrong, f"First mismatches (A, B, model, Jmol): {wrong[:12]}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("sdf", "jar", "launcher", "log"):
        parser.add_argument(arg, type=Path)
    parser.add_argument("--lean-scores", type=Path, help="Table emitted by FigureEightScores.lean")
    args = parser.parse_args()
    run(args.sdf, args.jar, args.launcher, args.log, args.lean_scores)
