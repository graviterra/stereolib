"""Differential screen of explicit neutral single-bond multicyclic Hanson records.

No Lean invocation. Requires compiled CentresPublishedMetric and unchanged pinned core.
Every configured candidate is evaluated as ID zero, preserving bond/neighbor order.
Published labels and unpublished candidate absence are counted separately. Missing
CIP_LABELS fields are recorded; absence is an operational comparison, not a claim
of an authoritative published nonstereogenic assignment.
All nonplanar C/Si degree-four and N/P degree-three/four atoms receive coordinate frames;
three-coordinate N/P uses the center as lone-pair carrier. Published labels never set hands.
"""

import argparse
import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

from figure8_geometry import hand

ELEMENTS = {
    "H": 1,
    "B": 5,
    "C": 6,
    "N": 7,
    "O": 8,
    "F": 9,
    "Si": 14,
    "P": 15,
    "S": 16,
    "Cl": 17,
    "Br": 35,
    "I": 53,
}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("sdf", type=Path)
    p.add_argument("classpath")
    p.add_argument("output", type=Path)
    p.add_argument("--max-heavy", type=int, default=200)
    p.add_argument("--max-cycle-rank", type=int, default=20)
    a = p.parse_args()
    digest = hashlib.sha256(a.sdf.read_bytes()).hexdigest()
    if digest != "28a000b36506dabe5a45f6d7672451c61c6e34f3e0f027f2599000d850273325":
        raise ValueError("SDF differs from pinned Hanson corpus")
    a.output.mkdir(parents=True, exist_ok=True)
    exclusions = Counter()
    results = []
    records = []
    for block in a.sdf.read_text().split("$$$$"):
        lines = block.strip("\n").splitlines()
        if not lines:
            continue
        name = lines[0]
        record = {"name": name}
        try:
            n, m = (int(lines[3][:3]), int(lines[3][3:6]))
            ar = lines[4 : 4 + n]
            br = lines[4 + n : 4 + n + m]
            symbols = [r[31:34].strip() for r in ar]
            bonds = [(int(r[:3]) - 1, int(r[3:6]) - 1, int(r[6:9])) for r in br]
            adj = [[] for _ in ar]
            for x, y, _ in bonds:
                adj[x].append(y)
                adj[y].append(x)
            seen = set()
            stack = [0]
            while stack:
                x = stack.pop()
                if x not in seen:
                    seen.add(x)
                    stack.extend(adj[x])
            labels = (
                lines[lines.index("> <CIP_LABELS>") + 1]
                if "> <CIP_LABELS>" in lines
                else ""
            )
            expected = {
                int(i) - 1: s
                for i, s in re.findall("(\\d+)([RrSs])(?:\\s|$)", labels + " ")
            }
            reason = None
            if len(seen) != n:
                reason = "disconnected"
            elif m - n + 1 < 2:
                reason = "not_multicyclic"
            elif any((o != 1 for _, _, o in bonds)):
                reason = "non_single_bond"
            elif any(int(r[36:39]) for r in ar) or any(
                r.startswith("M  CHG") for r in lines
            ):
                reason = "charge"
            elif any(int(r[34:36]) for r in ar) or any(
                r.startswith("M  ISO") for r in lines
            ):
                reason = "isotope"
            elif any(s not in ELEMENTS for s in symbols):
                reason = "element"
            elif any((s == "C" and len(adj[i]) != 4 for i, s in enumerate(symbols))):
                reason = "implicit_H_or_invalid_carbon"
            elif any(
                (s == "N" and len(adj[i]) not in (3, 4) for i, s in enumerate(symbols))
            ):
                reason = "unsupported_N"
            elif len(expected) != len(labels.split()):
                reason = "non_tetrahedral_published_label"
            elif (
                sum(s != "H" for s in symbols) > a.max_heavy
                or m - n + 1 > a.max_cycle_rank
            ):
                reason = "complexity_cap"
            if reason:
                exclusions[reason] += 1
                record["excluded"] = reason
                records.append(record)
                continue
            xyz = [
                tuple(round(float(r[k : k + 10]) * 10000) for k in (0, 10, 20))
                for r in ar
            ]
            frames = []
            for i, s in enumerate(symbols):
                if s not in ("C", "Si", "N", "P"):
                    continue
                neighbors = adj[i].copy()
                if len(neighbors) == 3 and s in ("N", "P"):
                    neighbors.append(i)
                if len(neighbors) != 4:
                    continue
                try:
                    h = hand([x + 1 for x in neighbors], xyz)
                except ValueError:
                    continue
                frames.append((i, h, neighbors))
            if not set(expected).issubset({f[0] for f in frames}):
                exclusions["unsupported_or_planar_published_frame"] += 1
                record["excluded"] = "unsupported_or_planar_published_frame"
                records.append(record)
                continue
            record.update(atoms=n, cycle_rank=m - n + 1, frames=len(frames))
            records.append(record)
            for root, _, _ in frames:
                published = expected.get(root)
                ids = [root] + [i for i in range(n) if i != root]
                ren = {old: new for new, old in enumerate(ids)}
                payload = "".join(f"a {ELEMENTS[symbols[i]]}\n" for i in ids)
                payload += "".join((f"b {ren[x]} {ren[y]}\n" for x, y, _ in bonds))
                payload += "".join(
                    (
                        f"f {ren[i]} {h} " + " ".join((str(ren[x]) for x in ns)) + "\n"
                        for i, h, ns in frames
                    )
                )
                request = a.output / f"{name}-atom{root + 1}.req"
                request.write_text(payload)
                row = {
                    "name": name,
                    "atom": root + 1,
                    "published": published,
                    "publication_scope": "published" if published else "unpublished",
                    "cip_field_present": "> <CIP_LABELS>" in lines,
                }
                try:
                    run = subprocess.run(
                        [
                            "java",
                            "-Xmx768m",
                            "-cp",
                            a.classpath,
                            "CentresPublishedMetric",
                            str(request),
                        ],
                        capture_output=True,
                        text=True,
                        timeout=20,
                        check=True,
                    )
                    if run.stderr.strip():
                        raise ValueError(
                            "Centres stderr (possibly swallowed exception): "
                            + run.stderr.strip()
                        )
                    native, original, active, comparisons, reversals = (
                        run.stdout.strip().split()
                    )
                    row.update(
                        native=native,
                        original=original,
                        active=active,
                        comparisons=int(comparisons),
                        reversals=int(reversals),
                        calibrated=native == original,
                    )
                    row["status"] = (
                        "calibration_error"
                        if native != original
                        else "positive"
                        if original != active
                        else "unassigned"
                        if original == "unassigned"
                        else "negative"
                    )
                    row["original_matches_expected_or_absence"] = original == (
                        published or "unassigned"
                    )
                    row["active_matches_expected_or_absence"] = active == (
                        published or "unassigned"
                    )
                except (subprocess.SubprocessError, ValueError) as e:
                    row.update(
                        status="error",
                        error=str(e),
                        stderr=str(getattr(e, "stderr", "")),
                    )
                results.append(row)
        except (ValueError, IndexError, KeyError) as e:
            exclusions["parse_error"] += 1
            records.append({"name": name, "excluded": "parse_error", "error": str(e)})
    counts = {
        key: 0
        for key in ("positive", "negative", "unassigned", "error", "calibration_error")
    }
    counts.update(Counter(r["status"] for r in results))
    scope_counts = {
        scope: {
            key: sum(
                r["publication_scope"] == scope and r["status"] == key for r in results
            )
            for key in counts
        }
        for scope in ("published", "unpublished")
    }
    calibration_run = subprocess.run(
        ["java", "-Xmx768m", "-cp", a.classpath, "CentresOriginMetricSpiro", str(Path(__file__).with_name("OriginMetricSpiro.mol"))],
        capture_output=True,
        text=True,
        timeout=20,
        check=True,
    )
    calibration = calibration_run.stdout
    expected_calibration = [
        "reflected=false release=R original=R active=S",
        "reflected=true release=S original=S active=R",
        "abstract handed-frame assignments changed=16 of 32",
    ]
    if (
        calibration_run.stderr.strip()
        or calibration.splitlines() != expected_calibration
    ):
        raise ValueError(
            "Synthetic positive calibration changed: " + calibration_run.stderr
        )
    (a.output / "synthetic-calibration.txt").write_text(calibration)
    report = {
        "synthetic_calibration": calibration.splitlines(),
        "sdf_sha256": hashlib.sha256(a.sdf.read_bytes()).hexdigest(),
        "caps": {"heavy_atoms": a.max_heavy, "cycle_rank": a.max_cycle_rank},
        "record_count": len(records),
        "eligible_records": sum("excluded" not in r for r in records),
        "exclusions": dict(exclusions),
        "counts": counts,
        "scope_counts": scope_counts,
        "records": records,
        "results": results,
    }
    (a.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {k: v for k, v in report.items() if k not in ("records", "results")},
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
