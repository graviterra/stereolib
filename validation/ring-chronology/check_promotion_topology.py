"""Compare focus deletion with actual simple-path ring unfolding on small single-bond graphs."""

from collections import Counter
from itertools import combinations, product


def component(edges, start, excluded=None):
    visited = {start}
    pending = [start]
    while pending:
        for atom in edges[pending.pop()]:
            if atom != excluded and atom not in visited:
                visited.add(atom)
                pending.append(atom)
    return visited


def unfold_arm(edges, root, first):
    atoms = set()
    returns = set()

    def visit(path):
        atom = path[-1]
        atoms.add(atom)
        if atom in path[:-1]:
            if atom == root:
                returns.add(path)
            return
        for neighbor in edges[atom] - {path[-2]}:
            visit((*path, neighbor))

    visit((root, first))
    return atoms, returns


def check_graphs():
    counts = Counter()
    for size in range(2, 7):
        bonds = list(combinations(range(size), 2))
        for mask in range(1 << len(bonds)):
            edges = [set() for _ in range(size)]
            for pos, (a, b) in enumerate(bonds):
                if mask & (1 << pos):
                    edges[a].add(b)
                    edges[b].add(a)
            if max(map(len, edges)) > 4 or len(component(edges, 0)) != size:
                continue
            counts["connected graphs"] += 1
            for root, neighbors in enumerate(edges):
                if len(neighbors) != 4:
                    continue
                counts["four-neighbor roots"] += 1
                returns = set()
                cyclic_arms = 0
                for arm in neighbors:
                    reachable = neighbors & component(edges, arm, excluded=root)
                    atoms, closures = unfold_arm(edges, root, arm)
                    assert atoms & neighbors == reachable
                    assert bool(closures) == (len(reachable) > 1)
                    returns.update(closures)
                    cyclic_arms += bool(closures)
                assert all(p[::-1] in returns and p != p[::-1] for p in returns)
                if len(returns) < 3:
                    counts["roots below three closures"] += 1
                    assert cyclic_arms <= 2
                counts["oriented root closures"] += len(returns)
    return counts


def check_partitions():
    slots = range(4)
    pairs = list(combinations(slots, 2))
    # Restricted growth strings represent each labelled set partition once.
    partitions = [
        p for p in product(slots, repeat=4)
        if p[0] == 0 and all(p[j] <= 1 + max(p[:j]) for j in (1, 2, 3))
    ]
    counts = Counter()
    for blocks, keys in product(partitions, repeat=2):
        cyclic = [blocks.count(blocks[j]) > 1 for j in slots]
        eligible = [j for j in slots if keys.count(keys[j]) > 1]
        if sum(cyclic) > 2 or len(eligible) < 3:
            continue
        compatible = all(keys[a] != keys[b] or cyclic[a] == cyclic[b] for a, b in pairs)
        for mark in eligible:
            outside_tie = any(
                keys[a] == keys[b] and blocks[a] != blocks[mark] and blocks[b] != blocks[mark]
                for a, b in pairs
            )
            if compatible:
                assert outside_tie
                counts["compatible marked cases"] += 1
            elif not outside_tie:
                counts["counterexamples without compatibility"] += 1
    return counts


if __name__ == "__main__":
    graphs = check_graphs()
    partitions = check_partitions()
    assert graphs["roots below three closures"] == 1055
    assert partitions["compatible marked cases"] == 52
    assert partitions["counterexamples without compatibility"] == 48
    for label, count in (graphs | partitions).items():
        print(f"{label}: {count}")
