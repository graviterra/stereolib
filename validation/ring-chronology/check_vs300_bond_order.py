"""Reproduce and localize Jmol 14.29.17's VS300 full-mode bond-row dependence."""

from argparse import ArgumentParser
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory

from check_figure14_regeneration import (
    compile_overlay, molecule_record, pinned_inputs, require_equal, rows,
)


def diagnostic(original):
    # The return and the reread are both taken, as in the release. Carry mode
    # substitutes the return only at the two auxiliary occurrences being tested.
    before = "rs = data.checkHandedness(atom1);"
    audit = """
            if (rule == RULE_6 && data.testRule6Full
                && ("C61-C49-C39".equals(myPath) || "C61-C20-C10".equals(myPath))) {
              System.out.println("CARRY " + myPath + " " + atom1.returnedHand + " " + rs);
              if ("carry".equals(System.getProperty("cage.mode"))) rs = atom1.returnedHand;
            }"""
    edits = (
        ("private boolean auxSort(int rule) {",
         "int returnedHand;\n    private boolean auxSort(int rule) {"),
        ("getRule6Descriptor(true) != NO_CHIRALITY",
         "(returnedHand = getRule6Descriptor(true)) != NO_CHIRALITY"),
        (before, before + audit),
    )
    for old, new in edits:
        require_equal(original.count(old), 1)
        original = original.replace(old, new)
    return original


def make_probe(directory, molecule, export=None):
    lines = molecule.read_text().splitlines()
    atoms, bonds = map(int, lines[3][:6].split())
    require_equal((atoms, bonds), (66, 71))
    start = atoms + 4
    block = lines[start:start + bonds]
    require_equal([block[i - 1].split()[:3] for i in (9, 10, 40, 41)],
                  [["9", "10", "1"], ["1", "10", "1"], ["38", "39", "1"], ["30", "39", "1"]])
    commands = ['''function probe(path,name,full) {
  load @path
  set cipRule6Full @full
  calculate chirality
  print "ROW " + name + " " + full + " [" + {atomno=10}.chirality + "," + {atomno=39}.chirality + "," + {atomno=61}.chirality + "]"
}''']
    for swap10, swap39 in product((0, 1), repeat=2):
        changed = block.copy()
        for swap, first in ((swap10, 9), (swap39, 40)):
            if swap:
                changed[first-1], changed[first] = changed[first], changed[first-1]
        name = f"{swap10}{swap39}"
        path = directory / (name + ".mol")
        path.write_text("\n".join(lines[:start] + changed + lines[start+bonds:]) + "\n")
        if export:
            (export / path.name).write_bytes(path.read_bytes())
        for full in ("false", "true"):
            commands.append(f'probe("{path}","{name}",{full})')
    script = directory / "order.spt"
    script.write_text("\n".join(commands) + '\nprint "CHECK_END"\n')
    return script


def expected(mode):
    observations = []
    for swap10, swap39, full in product((0, 1), repeat=3):
        hand39, hand10 = "R", "S"
        if full:
            reread39 = "R" if swap39 else "S"
            reread10 = "S" if swap10 else "R"
            if mode != "carry":
                hand39, hand10 = reread39, reread10
            if mode != "release":
                # Release constants STEREO_R and STEREO_S have values 1 and 2.
                observations.append(f"CARRY C61-C49-C39 1 {1 if reread39 == 'R' else 2}")
        observations.append(f"AUX C61-C49-C39 {hand39}")
        if full and mode != "release":
            observations.append(f"CARRY C61-C20-C10 2 {1 if reread10 == 'R' else 2}")
        observations.append(f"AUX C61-C20-C10 {hand10}")
        center = {("R", "S"): "s", ("S", "R"): "r"}.get((hand39, hand10), "")
        observations.append(f"ROW {swap10}{swap39} {str(bool(full)).lower()} [S,R,{center}]")
    return observations


def single_bond_model(directory, original):
    # Each former alkene endpoint becomes a neutral, three-coordinate nitrogen.
    # Preserve all 66 positions and all 71 pairs of bonded atoms.
    lines = original.read_text().splitlines()
    atoms, bonds = map(int, lines[3][:6].split())
    require_equal((atoms, bonds), (66, 71))
    endpoints = set()
    for row in range(4 + atoms, 4 + atoms + bonds):
        a, b, order = map(int, lines[row][:9].split())
        if order == 2:
            endpoints.update((a, b))
            lines[row] = lines[row][:6] + "  1" + lines[row][9:]
        else:
            require_equal(order, 1)
    require_equal(endpoints, {1, 2, 5, 6, 9, 24, 30, 31, 34, 35, 38, 53})
    for atom in endpoints:
        row = atom + 3
        require_equal(lines[row][31:34].strip(), "C")
        lines[row] = lines[row][:31] + "N" + lines[row][32:]
    lines[0] = "Single-bond VS300 control"
    path = directory / "single.mol"
    path.write_text("\n".join(lines) + "\n")
    return path


def run(directory, export=None):
    jar, corpus, original = pinned_inputs(directory)
    molecule, fields = molecule_record(corpus, "VS300", directory)
    require_equal(fields.split("> <CIP_LABELS>\n")[1].splitlines()[0], "10S 39R 61s")
    overlay = directory / "aux-return"
    compile_overlay(overlay, jar, diagnostic(original))
    for name, model in (("VS300", molecule), ("single-bond", single_bond_model(directory, molecule))):
        work = directory / name
        work.mkdir()
        script = make_probe(work, model, export if name == "single-bond" else None)
        for mode in ("release", "pass", "carry"):
            actual = rows(script, directory, jar, mode, None if mode == "release" else overlay,
                          trace_vs300=True)
            require_equal(actual, expected(mode))
            print(f"{name} {mode}: " + " | ".join(line for line in actual if line.startswith("ROW") and "true [" in line))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--export-single-bond", type=Path, metavar="NEW_DIR",
                        help="write the four derived mol files for the separate Lean admission check")
    export = parser.parse_args().export_single_bond
    if export:
        export.mkdir(parents=True, exist_ok=False)
    with TemporaryDirectory() as work:
        run(Path(work), export)
