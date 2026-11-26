"""Exact coordinate derivation for the acyclic, explicit-H Figure 8 model.

This deliberately limited independent checker covers single-bond trees without
isotopes. Atomic-number sphere comparisons derive ordinary tetrahedral carbon
hands. One pair of constitutionally identical, oppositely handed immediate
carbon ligands can then give a pseudoasymmetric descriptor (R precedes S).
The return value records carbons that need later rules, including C27.
Bond orders/isotopes must be checked by the caller before invoking this API.
The inputs are atom numbers, single bonds, and scaled coordinates.
"""

from functools import lru_cache


def _det(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def hand(order: list[int], xyz: list[tuple[int, int, int]]) -> str:
    points = [xyz[i - 1] for i in order]
    vectors = [tuple(p[k] - points[3][k] for k in range(3)) for p in points[:3]]
    volume = _det(*vectors)
    if volume == 0:
        raise ValueError('Degenerate tetrahedral coordinates')
    # With ligand 4 pointing away, clockwise 1->2->3 is R.
    return 'R' if volume < 0 else 'S'


def derive_partial(
    atoms: list[int], adjacency: dict[int, list[int]],
    xyz: list[tuple[int, int, int]],
) -> tuple[dict[int, str], set[int]]:
    """Return independently derived {1-based carbon atom: R/S/r/s}.

    Refuse malformed, cyclic, implicit-H, noninteger-coordinate or unsupported
    element/valence input. Unresolved stereochemical ligand comparisons are
    returned in the second component. This includes the Figure 8 root.
    """
    n = len(atoms)
    if n == 0 or len(xyz) != n or set(adjacency) != set(range(1, n + 1)):
        raise ValueError('Expected matching nonempty atom, adjacency and coordinate arrays')
    valences = {1: 1, 6: 4, 7: 3, 8: 2, 17: 1}
    for i, z in enumerate(atoms, 1):
        if z not in valences or len(adjacency[i]) != valences[z]:
            raise ValueError('Only explicit-H neutral H/C/N/O/Cl single-bond trees supported')
        if len(set(adjacency[i])) != len(adjacency[i]):
            raise ValueError('Duplicate adjacency entry')
        if len(xyz[i - 1]) != 3 or any(type(x) is not int for x in xyz[i - 1]):
            raise ValueError('Coordinates must be exact scaled integers')
        for j in adjacency[i]:
            if j == i or j not in adjacency or i not in adjacency[j]:
                raise ValueError('Invalid or asymmetric adjacency')
    seen, pending = set(), [1]
    while pending:
        i = pending.pop()
        if i not in seen:
            seen.add(i)
            pending.extend(adjacency[i])
    if len(seen) != n or sum(map(len, adjacency.values())) != 2 * (n - 1):
        raise ValueError('Only connected acyclic graphs supported')

    @lru_cache(None)
    def truncated(v, parent, depth):
        return (atoms[v - 1], tuple(sorted(
            (truncated(w, v, depth - 1) for w in adjacency[v] if w != parent),
            reverse=True))) if depth else (atoms[v - 1],)

    @lru_cache(None)
    def constitutional(v, parent):
        # Compare successive spheres before inspecting any deeper sphere.
        return tuple(truncated(v, parent, depth) for depth in range(n))

    hands = {}
    deferred = set()
    candidates = [i for i, z in enumerate(atoms, 1) if z == 6]
    for i in candidates:
        order = sorted(adjacency[i], key=lambda j: constitutional(j, i), reverse=True)
        keys = [constitutional(j, i) for j in order]
        if len(set(keys)) == 4:
            hands[i] = hand(order, xyz)
    ordinary = hands.copy()
    for i in candidates:
        if i in ordinary:
            continue
        groups = {}
        for j in adjacency[i]:
            groups.setdefault(constitutional(j, i), []).append(j)
        if sum(atoms[j - 1] == 1 for j in adjacency[i]) >= 2:
            continue  # Two identical explicit hydrogen ligands.
        if sorted(map(len, groups.values())) != [1, 1, 2]:
            deferred.add(i)
            continue
        pair = next(g for g in groups.values() if len(g) == 2)
        pair_hands = [ordinary.get(j) for j in pair]
        if any(h not in ('R', 'S') for h in pair_hands):
            deferred.add(i)
            continue
        # Restrict pseudo resolution to an immediate enantiomorphic pair.
        # Remaining downstream ordinary centers must agree under reflection;
        # Figure 8's paired terminal centers each have three achiral ligands.
        for j in pair:
            off_pair = [k for k in adjacency[j] if k != i]
            # Figure 8 uses H, Cl and CH3 on each member of this pair.
            # This restriction proves these three ligands are achiral, so an
            # opposite descriptor really does identify enantiomorphic arms.
            if sorted(atoms[k - 1] for k in off_pair) != [1, 6, 17]:
                raise ValueError('Only terminal H/Cl/methyl enantiomorphic pairs supported')
            methyl = next(k for k in off_pair if atoms[k - 1] == 6)
            if any(atoms[k - 1] != 1 for k in adjacency[methyl] if k != j):
                raise ValueError('Only terminal H/Cl/methyl enantiomorphic pairs supported')
        if pair_hands[0] == pair_hands[1]:
            continue  # Isomorphic H/Cl/methyl branches with the same hand.
        order = sorted(adjacency[i], key=lambda j: (
            constitutional(j, i), int(ordinary.get(j) == 'R')), reverse=True)
        hands[i] = hand(order, xyz).lower()
    return hands, deferred
