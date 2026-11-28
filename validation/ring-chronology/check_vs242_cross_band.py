"""Replay the published VS242 structure and its reflection with Jmol 14.29.17.

Uses the same SHA-256-pinned jars and compounds_3d.sdf as check_figure14_regeneration.
Run with python3 validation/ring-chronology/check_vs242_cross_band.py.
All atom numbers below are the one-based numbers printed by Jmol.
"""

import re
import subprocess
from decimal import Decimal
from pathlib import Path
from tempfile import TemporaryDirectory

from check_figure14_regeneration import (
    LAUNCHER,
    molecule_record,
    pinned_inputs,
    require_equal,
)
from vs242_branch_words import derive


def trace_geometry(directory, jar, molecule):
    atom_count = int(molecule.read_text().splitlines()[3][:3])
    script = directory / "trace.spt"
    script.write_text(f'''load "{molecule}"
set cipRule6Full false
calculate chirality
for (var j=1; j <= {atom_count}; j++) {{
  var v = {{atomno=j}}.chirality
  if (v != "") {{print "LABEL " + j + v}}
}}
print "VS242_COMPLETE"
''')
    result = subprocess.run(
        ["java", "-Xmx256m", "-Djava.awt.headless=true", "-cp", str(jar),
         str(directory / LAUNCHER), "-nos", str(script)],
        text=True, stdout=subprocess.PIPE, check=True, timeout=120,
    )
    lines = result.stdout.splitlines()
    require_equal(lines.count("VS242_COMPLETE"), 1)
    return result.stdout


def root_words(trace):
    words = {}
    for line in trace.splitlines():
        if not line.startswith("getBest ") or not line.endswith((" C36-N17", " C36-N39")):
            continue
        row = re.fullmatch(r"getBest ([68]) N(17|39) \(\{([\d ]*)\}\)\(\{([\d ]*)\}\) C36-N\2", line)
        if row is None:
            raise ValueError(f"Malformed C36 word trace: {line}")
        for ref, raw in zip("RS", row.groups()[2:]):
            indices = list(map(int, raw.split()))
            require_equal(indices, [i for i in range(8) if i in indices])
            key = int(row[1]), int(row[2]), ref
            if key in words:
                raise ValueError(f"Repeated C36 reference word: {key}")
            words[key] = "".join("l" if i in indices else "u" for i in range(8))
    return words


def public_labels(trace, atom_count=106):
    labels = {}
    for line in trace.splitlines():
        if not line.startswith("LABEL "):
            continue
        row = re.fullmatch(r"LABEL (\d+)([RSrs])", line)
        if row is None or not 1 <= int(row[1]) <= atom_count:
            raise ValueError(f"Malformed public label: {line}")
        atom = int(row[1])
        if atom in labels:
            raise ValueError(f"Repeated public label at atom {atom}")
        labels[atom] = row[2]
    return labels


def check_geometry(directory, jar, molecule, labels):
    trace = trace_geometry(directory, jar, molecule)
    lines = trace.splitlines()
    require_equal([f"{i}{h}" for i, h in public_labels(trace).items()], labels)

    words, hands, root_hand, stage = derive(molecule)
    require_equal(stage, 8)
    require_equal(f"36{root_hand}" in labels, True)
    native_hands = re.findall(r"^creating aux ([RSrs]) for C(\d+) = C36-.*$", trace, re.MULTILINE)
    require_equal(sorted((int(i), h) for h, i in native_hands), sorted(hands.items()))

    observed = root_words(trace)
    require_equal(observed, words)
    for ref in "RS":
        require_equal([observed[6, 17, ref], observed[6, 39, ref]], ["lluululu"] * 2)
        require_equal([observed[8, 17, ref], observed[8, 39, ref]], ["lululuul", "luluullu"])

    # The native root summary identifies the decisive rule and descending arm order.
    root = lines.index("C36")
    index = lines.index("\tN17\t--------------", root, lines.index("\tH37\t--------------", root))
    require_equal([line.strip() for line in lines[index + 1:index + 5]], [
        "C36-N17\t(R)lululuul  (S)lululuul", "5",
        "C36-N39\t(R)luluullu  (S)luluullu", "N39\t--------------",
    ])


def main():
    with TemporaryDirectory() as scratch:
        directory = Path(scratch)
        jar, corpus, _ = pinned_inputs(directory)
        mol, fields = molecule_record(corpus, "VS242", directory)
        labels = fields.split("> <CIP_LABELS>\n")[1].splitlines()[0].split()
        require_equal(len(labels), 21)
        require_equal("36R" in labels, True)
        check_geometry(directory, jar, mol, labels)
        lines = mol.read_text().splitlines()
        require_equal(int(lines[3][:3]), 106)
        for i in range(4, 110):
            lines[i] = f"{-Decimal(lines[i][:10]):10.4f}" + lines[i][10:]
        mirror = directory / "mirror.mol"
        mirror.write_text("\n".join(lines) + "\n")
        check_geometry(directory, jar, mirror, [v.translate(str.maketrans("RS", "SR")) for v in labels])
    print("VS242 and mirror: 42 labels, Rule 4b tie, Rule 5 N17 > N39, C36 R/S")


if __name__ == "__main__":
    main()
