"""Exhaustive oriented-tree orbits of the two pinned VS262 arms.

This includes a finite Rule 4a/4b/4c/5 motif comparator alongside independent
graph stereoisomer discrimination. It is not a general IUPAC completeness claim. Nitrogen is unoriented (no stable N configuration assumed).
Carbon orientations are determinant signs in neighbor order
[parent, *sorted(children)]: det(p0-p3, p1-p3, p2-p3).
The parent occupies a fixed slot: sorting the other three ligands multiplies
that sign by the permutation parity, including exchanges of child ligands.
"""
import argparse
from collections import Counter
from itertools import product
from functools import lru_cache
from pathlib import Path

from hanson_figure8_sdf import ARM_PATHS, EXPECTED, read_record, readings, require
from figure8_geometry import derive_partial, _det


def parity(values):
    return -1 if sum(a > b for i, a in enumerate(values) for b in values[i + 1:]) % 2 else 1


def enumerate_arm(atoms, adjacency, root, parent):
    """Return raw orientation assignments and canonical rooted decorated trees.

    An odd permutation of equal decorated ligands stabilizes a tetrahedron
    while reversing its orientation sign, so that sign is then immaterial.
    CH2/CH3 orientations are omitted from enumeration as this stabilizer is
    present for every decoration. Remaining carbon signs are all enumerated.
    """
    vertices = []
    def visit(v, p):
        if atoms[v - 1] == 6 and len(adjacency[v]) == 4:
            if sum(atoms[w - 1] == 1 for w in adjacency[v]) < 2:
                vertices.append(v)
        for w in adjacency[v]:
            if w != p:
                visit(w, v)
    visit(root, parent)
    vertices.sort()

    def key(v, p, signs):
        children = sorted(w for w in adjacency[v] if w != p)
        decorated = [key(w, v, signs) for w in children]
        ordered = sorted(decorated)
        orientation = 0
        if v in signs and len(set(decorated)) == len(decorated):
            # Canonical child ordering is unique exactly in this case.
            permutation = [ordered.index(k) for k in decorated]
            orientation = signs[v] * parity(permutation)
        return atoms[v - 1], tuple(ordered), orientation

    rows = []
    for values in product((-1, 1), repeat=len(vertices)):
        signs = dict(zip(vertices, values))
        signature = key(root, parent, signs)
        mirror = key(root, parent, {v: -s for v, s in signs.items()})
        rows.append((values, signature, mirror))
    return vertices, rows



def motif_model(atoms, adjacency):
    """Independent finite motif model; no claim of general CIP implementation.

    Full-path reference ranking preserves the association of each distal pair
    with its proximal carbon. Earlier priorities precede each new observation.
    The only lower-case sites admitted here have two terminal H/Cl/methyl
    enantiomorphic children. Ordinary N inversion is outside the model.
    """
    @lru_cache(None)
    def constitution(v, p):
        return atoms[v-1], tuple(sorted((constitution(w, v) for w in adjacency[v]
                                        if w != p), reverse=True))

    def physical_hands(root, parent, vertices, values):
        signs = dict(zip(vertices, values))
        parents = {}
        def visit(v, p):
            parents[v] = p
            for w in adjacency[v]:
                if w != p:
                    visit(w, v)
        visit(root, parent)
        hands = {}
        def orient(v, order):
            baseline = [parents[v]] + sorted(w for w in adjacency[v] if w != parents[v])
            return 'R' if signs[v] * parity([baseline.index(w) for w in order]) < 0 else 'S'
        for v in vertices:
            order = sorted(adjacency[v], key=lambda w: constitution(w, v), reverse=True)
            if len({constitution(w, v) for w in order}) == 4:
                hands[v] = orient(v, order)
        ordinary = hands.copy()
        for v in vertices:
            if v in ordinary:
                continue
            groups = {}
            for w in adjacency[v]:
                groups.setdefault(constitution(w, v), []).append(w)
            require(sorted(map(len, groups.values())) == [1, 1, 2], 'Outside Figure 8 motif')
            pair = next(g for g in groups.values() if len(g) == 2)
            require(all(w in ordinary for w in pair), 'Nonterminal stereo pair unsupported')
            if ordinary[pair[0]] != ordinary[pair[1]]:
                order = sorted(adjacency[v], key=lambda w: (
                    constitution(w, v), ordinary.get(w) == 'R'), reverse=True)
                hands[v] = orient(v, order).lower()
        return hands

    def keys(root, parent, hands):
        @lru_cache(None)
        def branch(v, p, lower=False):
            # RingStereoSiblingPass: separate shallow and deep rows; only
            # the deep ordering is enqueued. A flattened sphere loses this
            # distinction and can shift silent positions ahead of r/s sites.
            children = [branch(w, v, lower) for w in adjacency[v] if w != p]
            unit = 2 if hands.get(v) in ('R', 'S') else 1 if hands.get(v) in ('r', 's') else 0
            if lower:
                previous = branch(v, p, False)
                value = {'r': 2, 's': 1}.get(hands.get(v), 0)
                head, deep = previous[0], previous[1]
            else:
                value = unit
                head, deep = (atoms[v-1],), (constitution(v, p),)
            shallow = sorted(children, key=lambda b: b[0], reverse=True)
            ordered = sorted(children, key=lambda b: b[1], reverse=True)
            levels = [(tuple(b[2] for b in shallow), tuple(b[2] for b in ordered))]
            for depth in range(max((len(b[3]) for b in ordered), default=0)):
                levels.append(tuple(row for b in ordered if depth < len(b[3]) for row in b[3][depth]))
            word = ((value,),) + tuple(row for level in levels for row in level)
            return head + (value,), deep + (word,), value, tuple(levels), word

        def prior(v, p, lower=False):
            return branch(v, p, lower)[1]

        def walk(seed, lower=False):
            row = [(root, parent, ())]
            out = []
            while row:
                following = []
                for v, p, path in row:
                    if hands.get(v) in ('R', 'S'):
                        out.append(int(hands[v] == seed))
                    for w in adjacency[v]:
                        if w != p:
                            bit = int(hands.get(w) == seed) if hands.get(w) in ('R', 'S') else -1
                            step = (prior(w, v, lower), bit)
                            following.append((w, v, path + (step,)))
                row = sorted(following, key=lambda entry: entry[2], reverse=True)
            return tuple(out)
        r, s = walk('R'), walk('S')
        return (prior(root, parent), max(r, s), branch(root, parent, True)[4], walk('R', True)), (r, s)
    return physical_hands, keys


def motif_key(atoms, adjacency, route, vertices, values):
    """Public finite motif key for determinant signs in parent-first order."""
    physical_hands, keys = motif_model(atoms, adjacency)
    hands = physical_hands(route[1], route[0], vertices, values)
    return keys(route[1], route[0], hands)[0]


def compare_family(atoms, adjacency, xyz):
    physical_hands, keys = motif_model(atoms, adjacency)
    source_hands, _ = derive_partial(atoms, adjacency, xyz)
    for arm, route in ARM_PATHS.items():
        _, (r, s) = keys(route[1], route[0], source_hands)
        require((int(''.join(map(str, r)), 2), int(''.join(map(str, s)), 2)) ==
                (EXPECTED[arm, 'R'][1], EXPECTED[arm, 'S'][1]), 'Independent motif words differ')
    classes = {}
    for arm, route in ARM_PATHS.items():
        vertices, rows = enumerate_arm(atoms, adjacency, route[1], route[0])
        parent_of = {}
        def locate(v, p):
            parent_of[v] = p
            for w in adjacency[v]:
                if w != p:
                    locate(w, v)
        locate(route[1], route[0])
        observed = []
        for v in vertices:
            order = [parent_of[v]] + sorted(w for w in adjacency[v] if w != parent_of[v])
            points = [xyz[w - 1] for w in order]
            volume = _det(*(tuple(p[k] - points[3][k] for k in range(3)) for p in points[:3]))
            require(volume != 0, 'Degenerate motif center')
            observed.append(1 if volume > 0 else -1)
        observed_hands = physical_hands(route[1], route[0], vertices, observed)
        require(observed_hands == {v: source_hands[v] for v in vertices if v in source_hands},
                'Determinant/permutation hands differ from independent coordinate derivation')
        entries = []
        for values, orbit, mirror in rows:
            hands = physical_hands(route[1], route[0], vertices, values)
            key, words = keys(route[1], route[0], hands)
            mirrored_hands = physical_hands(route[1], route[0], vertices, tuple(-v for v in values))
            require(mirrored_hands == {v: {'R':'S', 'S':'R', 'r':'r', 's':'s'}[h]
                    for v, h in hands.items()}, 'Physical descriptor reflection failed')
            reflected_key, reflected_words = keys(route[1], route[0], mirrored_hands)
            require(reflected_key[:3] == key[:3] and reflected_words == words[::-1],
                    'Motif priority reflection failed')
            entries.append((values, orbit, key, hands))
        classes[arm] = entries
    collisions = false_strict = ties = 0
    first = None
    stages = Counter()
    for va, oa, ka, ha in classes['A']:
        for vb, ob, kb, hb in classes['B']:
            equal = ka == kb
            ties += equal
            collisions += equal and oa != ob
            false_strict += not equal and oa == ob
            if equal and oa != ob and first is None:
                first = (va, vb, ha, hb)
            if not equal:
                stages[next(i for i, (a, b) in enumerate(zip(ka, kb), 1) if a != b)] += 1
    print(f'MOTIF comparison: tied={ties}; strict={65536-ties}; '
          f'nonisomorphic ties={collisions}; isomorphic strict={false_strict}; '
          f'first differing stages (4a,4b,4c,5)={dict(sorted(stages.items()))}')
    print('First nonisomorphic tie:', first)
    require(collisions == 0 and false_strict == 0,
            'Finite motif tie classes differ from oriented-tree isomorphism classes')
    print('This finite motif implementation is independently modeled, not verified equivalent to Lean or universal IUPAC.')

def run(path):
    atoms, adjacency, xyz, _ = read_record(path)
    hands, _ = derive_partial(atoms, adjacency, xyz)
    controls = readings(atoms, adjacency, hands, ARM_PATHS)
    require(controls == EXPECTED, 'Four molecular Figure 8 ranked readings differ')
    print('Molecular coordinate-derived controls:', {str(k): v for k, v in controls.items()})
    results = {}
    for arm, route in ARM_PATHS.items():
        vertices, rows = enumerate_arm(atoms, adjacency, route[1], route[0])
        require(len(vertices) == 8, 'Pinned arm must have eight potentially oriented carbons')
        counts = Counter(signature for _, signature, _ in rows)
        mirror = {signature: reflected for _, signature, reflected in rows}
        require(all(mirror[mirror[k]] == k for k in counts), 'Reflection is not an involution')
        self_mirror = sum(k == mirror[k] for k in counts)
        require(len(counts) == 36 and self_mirror == 4, 'Unexpected pinned arm orbit count')
        results[arm] = counts
        print(f'{arm}: oriented carbons={vertices}; raw={len(rows)}; classes={len(counts)}; '
              f'orbit size histogram={dict(sorted(Counter(counts.values()).items()))}; '
              f'self-mirror={self_mirror}; enantiomer pairs={(len(counts)-self_mirror)//2}')
    require(results['A'] == results['B'], 'Arms have different oriented configuration spaces')
    counts = results['A']
    raw_ties = sum(n*n for n in counts.values())
    raw_total = sum(counts.values()) ** 2
    classes = len(counts)
    print(f'Ordered raw arm pairs: isomorphic={raw_ties}, distinct={raw_total-raw_ties}, total={raw_total}')
    print(f'Ordered orbit pairs: isomorphic={classes}, distinct={classes*(classes-1)}, total={classes**2}')
    compare_family(atoms, adjacency, xyz)



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sdf', type=Path)
    args = parser.parse_args()
    run(args.sdf)


if __name__ == '__main__':
    main()
