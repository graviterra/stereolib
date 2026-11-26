"""Generate EqualDistanceSource.lean receipts; --all also verifies every arm numbering."""
import argparse
import json
import os
import subprocess
import sys
from collections import Counter
from itertools import combinations, permutations
from math import prod
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT / "tools" / "centres10"
ARMS = (1, 2, 3, 4)


def request(arms, bridges, mirror):
    # Renumber the same four points. An odd permutation reverses written hand.
    odd = sum(a > b for a, b in combinations(arms, 2)) % 2
    hand = "S" if bool(odd) != mirror else "R"
    edges = [(0, arm) for arm in ARMS]
    for j, arm in enumerate(arms):
        edges.extend([(arm, 5 + j), (5 + j, arms[(j + 1) % 4])])
    lines = ["centres-1.0"]
    lines.extend(f"a {z} 0 0" for z in (6, 7, 7, 7, 7, *bridges))
    lines.extend(f"b {a} {b}" for a, b in edges)
    lines.append(f"f 0 {hand} 1 2 3 4")
    return "\n".join(lines) + "\n"


def check_trial(trial, arms, bridges):
    mark = trial["mark"]
    j = arms.index(mark)
    # At equal distance the paths enter through different bridge elements.
    following, previous = arms[(j + 1) % 4], arms[(j - 1) % 4]
    rank = {mark: 100, following: bridges[j], previous: bridges[(j - 1) % 4],
            arms[(j + 2) % 4]: 0}
    counts = Counter()
    for comparison in trial["comparisons"]:
        a, b = comparison["left"], comparison["right"]
        expected = (rank[a] > rank[b]) - (rank[a] < rank[b])
        if comparison["value"] != expected:
            raise ValueError(f"unexpected comparison for mark {mark}: {comparison}")
        counts["marked comparisons"] += 1
        if {a, b} == {following, previous}:
            counts["equal-distance comparisons"] += 1
    return counts


def run_source(classpath, payload):
    return json.loads(subprocess.check_output(
        [sys.executable, "-I", str(TOOLS / "run_pinned.py"), classpath, "--rule-prefixes"],
        input=payload, text=True))


def swapped_carbon_priority(trace):
    """Recover the unique order consistent with the recorded final comparisons."""
    comparisons = trace["passes"][-1]["trials"][-1]["comparisons"]
    orders = [
        order for order in permutations(ARMS)
        if all((order.index(row["right"]) - order.index(row["left"])) * row["value"] > 0
               for row in comparisons)
    ]
    if len(orders) != 1:
        raise ValueError(f"the final source comparisons allow {orders}")
    return orders[0]


def bond_order_controls(output, classpath, requests):
    """Permute four bond records while retaining IDs, coordinates and all five frames."""
    outcomes = Counter()
    for order in permutations(ARMS):
        pair = []
        for mirror in (False, True):
            lines = requests[mirror].splitlines()
            indices = [i for i, line in enumerate(lines) if line.startswith("b 0 ")]
            if [lines[i] for i in indices] != [f"b 0 {a}" for a in ARMS]:
                raise ValueError("missing canonical spoke bonds")
            for i, a in zip(indices, order):
                lines[i] = f"b 0 {a}"
            payload = "\n".join(lines) + "\n"
            result = run_source(classpath, payload)
            carbon, *nitrogens = result["traces"]
            expected_hands = "RRSS" if mirror else "SSRR"
            if [(n["atom"], n["label"]) for n in nitrogens] != list(enumerate(expected_hands, 1)):
                raise ValueError("bond order changed a nitrogen assignment")
            trial = carbon["passes"][-1]["trials"][-1]
            count = sum(abs(row["value"]) > 1 for row in trial["comparisons"])
            priority = swapped_carbon_priority(carbon)
            if sum(a > b for a, b in combinations(priority, 2)) % 2 != 1:
                raise ValueError(f"bond order changed carbon permutation parity: {priority}")
            pair.append((carbon["label"], count))
            if order in (ARMS, (1, 2, 4, 3)):
                tag = ("mirror" if mirror else "original") + "-spokes-" + "".join(map(str, order))
                (output / f"{tag}.req").write_text(payload)
                (output / f"{tag}.json").write_text(json.dumps(result, separators=(",", ":")))
        outcomes[tuple(pair)] += 1
    expected = {(("s", 1), ("r", 1)): 12, (("S", 2), ("R", 2)): 12}
    if outcomes != expected:
        raise ValueError(f"pinned source bond-order observations changed: {outcomes}")
    print("24 orders of the same four bonds:", dict(outcomes))


def bridgehead_controls(output, classpath, bond_orders):
    """Include the four nitrogen frames and retain the resulting source inventories."""
    swapped_requests = {}
    for swapped in (False, True):
        points = list(range(9))
        if swapped:
            points[7], points[8] = points[8], points[7]
        for mirror in (False, True):
            payload = request(ARMS, (8, 16, 8, 16), mirror)
            hands = []
            for nitrogen, sulfur, oxygen in ((1, 8, 5), (2, 6, 5), (3, 6, 7), (4, 8, 7)):
                # S > O > C > phantom. The center is on the phantom side of
                # the S,O,C plane. For (t,t²,t³), this is minus the Vandermonde.
                priority = (sulfur, oxygen, 0, nitrogen)
                params = [points[i] for i in priority]
                volume = (-1 if not mirror else 1) * prod(b - a for a, b in combinations(params, 2))
                if volume == 0:
                    raise ValueError("planar nitrogen")
                hand = "R" if volume < 0 else "S"
                hands.append(hand)
                payload += f"f {nitrogen} {hand} {sulfur} {oxygen} 0 {nitrogen}\n"
            result = run_source(classpath, payload)
            labels = [(row["atom"], row["label"]) for row in result["traces"]]
            carbon = ("r" if mirror else "s") if swapped else ("S" if mirror else "R")
            if labels != list(enumerate([carbon, *hands])) or len(result["traces"][0]["updates"]) != 28:
                raise ValueError(f"unexpected full-inventory release trace {labels}")
            if swapped:
                swapped_requests[mirror] = payload
                order = swapped_carbon_priority(result["traces"][0])
                expected = (2, 1, 3, 4) if mirror else (4, 3, 1, 2)
                inversions = sum(a > b for a, b in combinations(order, 2))
                if order != expected or inversions % 2 != 1:
                    raise ValueError(f"unexpected swapped carbon priority {order}")
                print("swapped carbon priority", order, "inversions", inversions)
            tag = ("mirror" if mirror else "original") + ("-swap" if swapped else "") + "-bridgeheads"
            (output / f"{tag}.req").write_text(payload)
            (output / f"{tag}.json").write_text(json.dumps(result, separators=(",", ":")))
            print(tag, "".join(letter for _, letter in labels))
    if bond_orders:
        bond_order_controls(output, classpath, swapped_requests)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="directory for the two canonical source receipts")
    parser.add_argument("--all", action="store_true", help="check all 192 source configurations")
    parser.add_argument("--bridgeheads", action="store_true", help="also configure all four nitrogen frames")
    parser.add_argument("--bond-orders", action="store_true", help="test all 24 spoke orders with all frames fixed")
    parser.add_argument("--cache", type=Path, default=ROOT / ".cache" / "centres10")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    classpath = os.pathsep.join(str(args.cache / name) for name in ("classes", "guava.jar"))
    release = json.loads((TOOLS / "release-1.0.json").read_text())["commit"]
    substitutions = [(8, 16), (16, 8), (8, 8), (16, 16)] if args.all else [(8, 16)]
    totals = Counter()
    for first, second in substitutions:
        bridges = (first, second, first, second)
        for arms in permutations(ARMS) if args.all else (ARMS,):
            for mirror in (False, True):
                payload = request(arms, bridges, mirror)
                result = run_source(classpath, payload)
                trace, = result["traces"]
                expected = "-" if first == second else ("S" if (first > second) != mirror else "R")
                if trace["atom"] != 0 or trace["label"] != expected or trace["updates"]:
                    raise ValueError(f"unexpected root result for {bridges}, {arms}, mirror={mirror}")
                counts = Counter()
                for phase in trace["passes"]:
                    for trial in phase["trials"]:
                        if trial["mark"] is not None:
                            counts.update(check_trial(trial, arms, bridges))
                if not counts["equal-distance comparisons"]:
                    raise ValueError("source never compared the equidistant arms")
                totals.update(counts)
                totals["configurations"] += 1
                if (first, second) == (8, 16) and arms == ARMS:
                    receipt = {"release": release, "molecularRequest": payload, "traces": result["traces"]}
                    packet = {"receipt": receipt, "observed": result["observed"]}
                    name = "mirror" if mirror else "original"
                    (args.output / f"{name}.source.json").write_text(json.dumps(packet, separators=(",", ":")))
    print(json.dumps(totals, sort_keys=True))
    if args.bridgeheads or args.bond_orders:
        bridgehead_controls(args.output, classpath, args.bond_orders)


if __name__ == "__main__":
    main()
