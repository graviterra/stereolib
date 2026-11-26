"""Check Hanson Figure 8 against the pinned VS262 molecular tree.

Derive the published root assignment from elements, bonds and coordinates.
Expected labels and the published four readings are checked only after scoring.
"""

import argparse
import hashlib
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

from figure8_geometry import derive_partial, hand

SDF_HASH = "28a000b36506dabe5a45f6d7672451c61c6e34f3e0f027f2599000d850273325"
RECORD_HASH = "c1fa20db87de07b69df9b9890d81d803f7f90acf89b1a3073d015a158da197c0"
ATOMIC_NUMBERS = {"H": 1, "C": 6, "N": 7, "O": 8, "Cl": 17}
ARM_PATHS = {"A": (27, 87, 24, 10), "B": (27, 89, 29, 31)}
EXPECTED = {
    ("A", "S"): ([7, 11, 20, 3, 16, 58], 40),
    ("A", "R"): ([7, 11, 3, 20, 16, 58], 27),
    ("B", "S"): ([41, 32, 46, 54, 37, 50], 24),
    ("B", "R"): ([41, 32, 54, 46, 37, 50], 43),
}


def require(condition: bool, message: str) -> None:
    """Enforce a validation check, including under Python -O."""
    if not condition:
        raise ValueError(message)


Point = tuple[int, int, int]

def read_record(path: Path) -> tuple[list[int], dict[int, list[int]], list[Point], str]:
    """Read and authenticate the corpus once, then validate its VS262 tree."""
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == SDF_HASH,
            "SDF hash differs from the pinned authors' validation corpus")
    records = [record for record in data.split(b"$$$$") if b"\nVS262\n" in record]
    require(len(records) == 1, "Expected exactly one VS262 record")
    record = records[0]
    require(hashlib.sha256(record).hexdigest() == RECORD_HASH, "VS262 record hash mismatch")
    lines = record.decode("ascii").strip("\n").splitlines()
    n, m = int(lines[3][:3]), int(lines[3][3:6])
    require((n, m) == (94, 93), "Expected 94 atoms and 93 bonds")
    atoms = [ATOMIC_NUMBERS[line[31:34].strip()] for line in lines[4:4 + n]]
    adjacency: dict[int, list[int]] = {i: [] for i in range(1, n + 1)}
    for bond in lines[4 + n:4 + n + m]:
        a, b, order = int(bond[:3]), int(bond[3:6]), int(bond[6:9])
        require(a in adjacency and b in adjacency and a != b, "Invalid bond endpoints")
        require(order == 1, "Expected only single bonds")
        require(b not in adjacency[a], "Duplicate bond")
        adjacency[a].append(b)
        adjacency[b].append(a)
    seen: set[int] = set()
    pending = [27]
    while pending:
        vertex = pending.pop()
        if vertex not in seen:
            seen.add(vertex)
            pending.extend(adjacency[vertex])
    require(len(seen) == n, "Expected a connected molecular tree")
    for name, route in ARM_PATHS.items():
        require(all(b in adjacency[a] for a, b in zip(route, route[1:])),
                f"Arm {name} does not follow its actual C27 path")
    def coordinate(field: str) -> int:
        value = Fraction(field.strip()) * 10000
        require(value.denominator == 1, "Expected four-decimal SDF coordinates")
        return int(value)

    xyz = [(coordinate(row[:10]), coordinate(row[10:20]), coordinate(row[20:30]))
           for row in lines[4:4 + n]]
    return atoms, adjacency, xyz, lines[lines.index("> <CIP_LABELS>") + 1]


def read_graph(path: Path) -> tuple[list[int], dict[int, list[int]]]:
    atoms, adjacency, _, _ = read_record(path)
    return atoms, adjacency


def readings(atoms: list[int], adjacency: dict[int, list[int]], hands: dict[int, str],
             paths: dict[str, tuple[int, ...]]) -> dict[tuple[str, str], tuple[list[int], int]]:
    """Rank each reference reading of the two arms from the derived descriptors."""
    @lru_cache(None)
    def constitutional(vertex: int, parent: int) -> tuple:
        return atoms[vertex - 1], tuple(sorted(
            (constitutional(child, vertex) for child in adjacency[vertex] if child != parent),
            reverse=True,
        ))

    @lru_cache(None)
    def through4a(vertex: int, parent: int) -> tuple:
        hand = hands.get(vertex)
        rank = 2 if hand in ("R", "S") else 1 if hand in ("r", "s") else 0
        return rank, tuple(sorted(
            ((constitutional(child, vertex), through4a(child, vertex))
             for child in adjacency[vertex] if child != parent), reverse=True,
        ))

    def walk(arm: int, seed: str) -> list[tuple[int, int]]:
        row = [(arm, root, ())]
        out = []
        while row:
            following = []
            for vertex, parent, route in row:
                hand = hands.get(vertex)
                if hand in ("R", "S"):
                    out.append((vertex, int(hand == seed)))
                for child in adjacency[vertex]:
                    if child != parent:
                        hand = hands.get(child)
                        bit = int(hand == seed) if hand in ("R", "S") else -1
                        key = constitutional(child, vertex), through4a(child, vertex), bit
                        following.append((child, vertex, route + (key,)))
            row = sorted(following, key=lambda entry: entry[2], reverse=True)
        return out

    root = paths["A"][0]
    require(root == paths["B"][0], "Expected a common root")
    a, b = paths["A"][1], paths["B"][1]
    require(constitutional(a, root) == constitutional(b, root), "Arms differ before stereo")
    require(through4a(a, root) == through4a(b, root), "Arms differ before Rule 4b")
    result = {}
    for name, route in paths.items():
        for seed in ("S", "R"):
            out = walk(route[1], seed)
            bits = "".join(str(bit) for _, bit in out)
            result[name, seed] = [vertex for vertex, _ in out], int(bits, 2)
    return result


def evaluate(atoms: list[int], adjacency: dict[int, list[int]], xyz: list[Point],
             paths: dict[str, tuple[int, ...]]):
    hands, deferred = derive_partial(atoms, adjacency, xyz)
    root = paths["A"][0]
    require(deferred == {root}, f"Unexpected unresolved carbons {deferred}")
    scores = readings(atoms, adjacency, hands, paths)
    best = {name: max(scores[name, seed][1] for seed in ("R", "S")) for name in paths}
    require(best["A"] != best["B"], "Root requires a rule beyond Rule 4b")
    carbon_arms = [paths[name][1] for name in sorted(paths, key=best.get, reverse=True)]
    require(sorted(atoms[i - 1] for i in adjacency[root]) == [1, 6, 6, 8] and
            set(carbon_arms) == {i for i in adjacency[root] if atoms[i - 1] == 6},
            "Expected O, two carbon arms and H at the root")
    oxygen, = (i for i in adjacency[root] if atoms[i - 1] == 8)
    hydrogen, = (i for i in adjacency[root] if atoms[i - 1] == 1)
    hands[root] = hand([oxygen, *carbon_arms, hydrogen], xyz)
    return hands, scores


def verify(atoms, adjacency, xyz, annotations):
    hands, scores = evaluate(atoms, adjacency, xyz, ARM_PATHS)
    require(scores == EXPECTED, f"Unexpected Figure 8 readings {scores}")
    expected = {int(label[:-1]): label[-1] for label in annotations.split()}
    require(hands == expected, f"Coordinate-derived labels differ from record: {hands}")
    opposite = {"R": "S", "S": "R", "r": "r", "s": "s"}
    mirror, mirror_scores = evaluate(atoms, adjacency, [(-x, y, z) for x, y, z in xyz], ARM_PATHS)
    require(mirror == {i: opposite[h] for i, h in hands.items()}, "Mirror descriptor mismatch")
    require(mirror_scores == {(arm, opposite[seed]): value for (arm, seed), value in scores.items()},
            "Mirror reference readings disagree")

    def rename(i: int) -> int:
        return len(atoms) + 1 - i

    new_edges = {rename(i): [rename(j) for j in reversed(js)] for i, js in adjacency.items()}
    new_paths = {name: tuple(map(rename, route)) for name, route in ARM_PATHS.items()}
    numbered, numbered_scores = evaluate(atoms[::-1], new_edges, xyz[::-1], new_paths)
    require(numbered == {rename(i): h for i, h in hands.items()}, "Renumbered descriptor mismatch")
    for key, (ids, score) in scores.items():
        new_ids, new_score = numbered_scores[key]
        require(sorted(map(rename, ids)) == sorted(new_ids) and score == new_score and
                [hands[i] for i in ids] == [numbered[i] for i in new_ids],
                f"Renumbering changed the scored occurrence population or word for {key}")
    print("Derived from graph and coordinates:", " ".join(f"{i}{hands[i]}" for i in sorted(hands)))
    for (arm, seed), (ids, score) in scores.items():
        print(f"{arm} {seed}: {ids}, score {score}")
    print(f"Root C27 {hands[27]}, reflected {mirror[27]}. All labels and readings survive renumbering.")


def main() -> int:
    """Validate the explicitly supplied authors' SDF corpus."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sdf", type=Path, help="Path to the authors' compounds_3d.sdf")
    args = parser.parse_args()
    try:
        verify(*read_record(args.sdf))
    except (OSError, ValueError, KeyError, IndexError) as error:
        parser.exit(1, f"validation failed: {error}\n")
    print("sdf_sha256", SDF_HASH)
    print("record_sha256", RECORD_HASH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
