"""Test Rule 6 assignment and reassignment on Figure 14, cubane and VS300."""

from hashlib import sha256
from fractions import Fraction
from itertools import combinations, product
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory
from zipfile import ZipFile


ROOT = Path(__file__).resolve().parents[2]
REPLAY = ROOT / ".cache" / "jmol-14.29.17"
FIXTURE = Path(__file__).with_name("Figure14AllOut.mol")
CIP = "org/jmol/symmetry/CIPChirality.java"
LAUNCHER = "org/openscience/jmol/app/JmolData.java"

# Insert immediately after a marked occurrence's geometry has been read, before
# its hand is published to the digraph. Children have already been visited.
HAND_READ = "            rs = data.checkHandedness(atom1);"
INTERVENTION = """
            if (root.rule6refIndex >= 0 && (root.atomIndex == 0 || root.atomIndex == 1)
                && (rs == STEREO_R || rs == STEREO_S)) {
              System.out.println("HAND " + myPath + " " + (rs == STEREO_R ? "R" : "S") + " " + ruleNames[rule]);
              if (atomIndex == 1 - root.atomIndex) {
                String mode = System.getProperty("cage.mode");
                if ("suppress".equals(mode)) rs = NO_CHIRALITY;
                if ("uniformR".equals(mode)) rs = STEREO_R;
                if ("uniformS".equals(mode)) rs = STEREO_S;
                if ("reverse".equals(mode)) rs = (rs == STEREO_R ? STEREO_S : STEREO_R);
              }
            }"""


def require_equal(actual, expected):
    if actual != expected:
        raise ValueError(f"received {actual!r}, expected {expected!r}")


def pinned(path, digest):
    require_equal(sha256(path.read_bytes()).hexdigest(), digest)
    return path.resolve()


def rows(script, directory, jar, mode, overlay=None, trace_vs300=False):
    classpath = os.pathsep.join(map(str, [overlay, jar])) if overlay else str(jar)
    result = subprocess.run(
        ["java", "-Xmx256m", "-Djava.awt.headless=true", f"-Dcage.mode={mode}",
         "-cp", classpath, str(directory / LAUNCHER), "-nos", str(script)],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=120,
    )
    if result.returncode or "CHECK_END" not in result.stdout.splitlines():
        raise ValueError(result.stdout[-2000:])
    observations = []
    for line in result.stdout.splitlines():
        if line.startswith(("ROW ", "HAND ", "RULE ", "CARRY ")):
            observations.append(line)
        elif trace_vs300:
            hit = re.fullmatch(r"creating aux ([RS]) for C(?:10|39) = (C61-C49-C39|C61-C20-C10)", line)
            if hit:
                observations.append(f"AUX {hit[2]} {hit[1]}")
    return observations


def compile_overlay(directory, jar, source_text):
    directory.mkdir()
    source = directory / "CIPChirality.java"
    source.write_text(source_text)
    subprocess.run(["java", "-Xmx256m", "-m", "jdk.compiler/com.sun.tools.javac.Main",
                    "-cp", str(jar), "-d", str(directory), str(source)], check=True, timeout=120)


def molecule_record(corpus, name, directory):
    record, = [record.lstrip("\n") for record in corpus.read_text().split("$$$$")
               if record.lstrip("\n").startswith(name + "\n")]
    mol, fields = record.split("M  END\n")
    path = directory / (name + ".mol")
    path.write_text(mol + "M  END\n")
    return path, fields


def pinned_jmol_inputs(directory):
    """Prepare the pinned Jmol runtime and launcher without requiring a corpus."""
    jar = pinned(Path(os.environ.get("JMOL_JAR", str(REPLAY / "jmol.jar"))), "6d760b21af0c87ba5e6b6304f7c37b96f7412700a40e07b524402cc22914cf07")
    sources = pinned(Path(os.environ.get("JMOL_SOURCES", str(REPLAY / "sources.jar"))), "6298864075f2aa2502b676219db455ba5da4f1f324d22355ae83dfb29b927ae9")
    with ZipFile(sources) as archive:
        launcher = directory / LAUNCHER
        launcher.parent.mkdir(parents=True)
        launcher.write_bytes(archive.read(LAUNCHER))
        original = archive.read(CIP).decode().replace("\r\n", "\n")
    return jar, original


def pinned_inputs(directory):
    jar, original = pinned_jmol_inputs(directory)
    corpus = pinned(Path(os.environ.get("HANSON_SDF", str(ROOT / ".cache" / "compounds_3d.sdf"))),
                    "28a000b36506dabe5a45f6d7672451c61c6e34f3e0f027f2599000d850273325")
    return jar, corpus, original


def run(directory):
    jar, corpus, original = pinned_inputs(directory)
    pinned(FIXTURE, "d2a19341645153a491c14f4377cf2a0b4fab27ace181e4a7c29ac243da675b7d")
    require_equal(original.count(HAND_READ), 1)
    overlay = directory / "distal"
    compile_overlay(overlay, jar, original.replace(HAND_READ, HAND_READ + INTERVENTION))
    check_cage(directory, jar, overlay)
    check_cubane(corpus, directory, jar)
    check_initial_assignment(corpus, directory, jar, original)
    check_cage_bond_orders(directory, jar)


def check_cage(directory, jar, overlay):
    cage = directory / "cage.spt"
    cage_calls = []
    for top, bottom, full in product(("false", "true"), repeat=3):
        cage_calls.append(f"probe({top},{bottom},{full})")
    cage.write_text(f'''function probe(topIn,bottomIn,full) {{
  load "{FIXTURE}"
  if (topIn) {{ {{atomno=9}}.z = 0.27 }}
  if (bottomIn) {{ {{atomno=10}}.z = -0.27 }}
  set cipRule6Full @full
  calculate chirality
  print "ROW " + topIn + " " + bottomIn + " " + full + " [" + {{atomno=1}}.chirality + "," + {{atomno=2}}.chirality + "]"
}}
''' + "\n".join(cage_calls) + '\nprint "CHECK_END"\n')
    for mode in ("release", "pass", "suppress", "uniformR", "uniformS", "reverse"):
        expected = []
        for top, bottom, full in product(("false", "true"), repeat=3):
            letter = ""
            if full == "true":
                if mode != "release":
                    for path, hand in [
                        ("C1-C5-C6-C2", "R" if bottom == "false" else "S"),
                        ("C1-C7-C8-C2", "S" if bottom == "false" else "R"),
                        ("C2-C6-C5-C1", "S" if top == "false" else "R"),
                        ("C2-C8-C7-C1", "R" if top == "false" else "S"),
                    ]:
                        expected.append(f"HAND {path} {hand} 2")
                if mode in ("release", "pass", "reverse"):
                    letter = "r" if (top == bottom) != (mode == "reverse") else "s"
            expected.append(f"ROW {top} {bottom} {full} [{letter},{letter}]")
        actual = rows(cage, directory, jar, mode, None if mode == "release" else overlay)
        require_equal(actual, expected)
        print(f"{mode}: " + " | ".join(line for line in actual if line.startswith("ROW") and "true [" in line))


def check_cubane(corpus, directory, jar):
    cube_file, _ = molecule_record(corpus, "VS009", directory)
    script = directory / "cubane.spt"
    script.write_text(f'''function probe(full) {{
  load "{cube_file}"
  set cipRule6Full @full
  calculate chirality
  for (var i = 1; i <= 8; i++) {{
    print "ROW " + full + " " + i + " [" + {{atomno=i}}.chirality + "]"
  }}
}}
probe(false)
probe(true)
print "CHECK_END"
''')
    expected = [f"ROW {full} {atom} [{letter}]" for full, letter in (("false", ""), ("true", "r"))
                for atom in range(1, 9)]
    require_equal(rows(script, directory, jar, "release"), expected)
    print("VS009: eight unassigned in default mode, eight lowercase r in full mode")


def check_initial_assignment(corpus, directory, jar, original):
    molecule, fields = molecule_record(corpus, "VS300", directory)
    require_equal(fields.split("> <CIP_LABELS>\n")[1].splitlines()[0], "10S 39R 61s")
    gate = "int getRule6Descriptor(boolean isAux) {"
    require_equal(original.count(gate), 1)
    overlay = directory / "initial-aux"
    gate_override = """
      if (isAux) {
        String mode = System.getProperty("cage.mode");
        boolean skip10 = atomIndex == 9 && ("skip10".equals(mode) || "skipBoth".equals(mode));
        boolean skip39 = atomIndex == 38 && ("skip39".equals(mode) || "skipBoth".equals(mode));
        if ("skipAux".equals(mode) || (root.atomIndex == 60 && (skip10 || skip39)))
          return NO_CHIRALITY;
      }"""
    source = original.replace(gate, gate + gate_override)
    root_hand = "rs = data.checkHandedness(cipAtom);"
    require_equal(source.count(root_hand), 1)
    trace = '\n            if (cipAtom.atomIndex == 60) System.out.println("RULE " + ruleNames[currentRule]);'
    compile_overlay(overlay, jar, source.replace(root_hand, root_hand + trace))
    script = directory / "vs300.spt"
    script.write_text(f'''function probe(mirror) {{
  load "{molecule}"
  if (mirror) {{
    for (var i=1; i <= {{*}}.count; i++) {{
      var x = {{atomno=i}}.x
      {{atomno=i}}.x = 0 - x
    }}
  }}
  set cipRule6Full false
  calculate chirality
  print "ROW " + mirror + " [" + {{atomno=10}}.chirality + "," + {{atomno=39}}.chirality + "," + {{atomno=61}}.chirality + "]"
}}
probe(false)
probe(true)
print "CHECK_END"
''')
    for mode, last, mirrored, rule in (("release", "s", "s", ""), ("pass", "s", "s", "5"),
                                       ("skip10", "S", "R", "4a"), ("skip39", "R", "S", "4a"),
                                       ("skipBoth", "", "", ""), ("skipAux", "", "", "")):
        actual = rows(script, directory, jar, mode, None if mode == "release" else overlay)
        decision = [f"RULE {rule}"] if rule else []
        require_equal(actual, [*decision, f"ROW false [S,R,{last}]", *decision, f"ROW true [R,S,{mirrored}]"])
        print(f"VS300 {mode}: " + " | ".join(actual))
    check_ligand_reflections(molecule, directory, jar)


def reflected_ligand(lines, neighbors, anchor):
    """Reflect the component at anchor across a vertical plane through its bond to C61."""
    members = {anchor}
    pending = [anchor]
    while pending:
        fresh = neighbors[pending.pop()] - members - {61}
        members.update(fresh)
        pending.extend(fresh)
    require_equal(len(members), 31)
    require_equal(members.intersection(neighbors[61]), {anchor})

    def point(atom):
        return tuple(Fraction(v) for v in lines[atom + 3][:30].split())

    ax, ay, _ = point(anchor)
    rx, ry, _ = point(61)
    nx, ny = ry - ay, ax - rx
    norm_sq = nx**2 + ny**2
    changes = {}
    for atom in members:
        x, y, z = point(atom)
        scale = 2 * ((x - ax) * nx + (y - ay) * ny) / norm_sq
        position = x - scale * nx, y - scale * ny, z
        xyz = "".join(f"{float(v):10.4f}" for v in position)
        changes[atom + 3] = xyz + lines[atom + 3][30:]
    require_equal(changes[anchor + 3], lines[anchor + 3])
    return changes


def check_ligand_reflections(molecule, directory, jar):
    lines = molecule.read_text().splitlines()
    atoms, bonds = map(int, lines[3][:6].split())
    require_equal((atoms, bonds), (66, 71))
    neighbors = {atom: set() for atom in range(1, atoms + 1)}
    for bond in lines[4 + atoms:4 + atoms + bonds]:
        a, b = map(int, bond[:6].split())
        neighbors[a].add(b)
        neighbors[b].add(a)
    first = reflected_ligand(lines, neighbors, 20)
    second = reflected_ligand(lines, neighbors, 49)
    require_equal(first.keys() & second.keys(), set())
    commands = []
    for name, changes in (("original", {}), ("invert10", first), ("invert39", second),
                          ("invertBoth", first | second)):
        path = directory / (name + ".mol")
        path.write_text("\n".join(changes.get(i, row) for i, row in enumerate(lines)) + "\n")
        commands.extend([f'load "{path}"', 'set cipRule6Full false', 'calculate chirality',
                         f'print "ROW {name} [" + {{atomno=10}}.chirality + "," + '
                         '{atomno=39}.chirality + "," + {atomno=61}.chirality + "]"'])
    script = directory / "ligands.spt"
    script.write_text("\n".join(commands) + '\nprint "CHECK_END"\n')
    actual = rows(script, directory, jar, "release")
    require_equal(actual, ["ROW original [S,R,s]", "ROW invert10 [R,R,]",
                           "ROW invert39 [S,S,]", "ROW invertBoth [R,S,r]"])
    print("VS300 fixed C61 frame: " + " | ".join(actual))


def check_cage_bond_orders(directory, jar):
    """Test every single transposition from each reference bond table in stock full mode."""
    for model in (FIXTURE, directory / "VS009.mol"):
        lines = model.read_text().splitlines()
        atoms, bonds = map(int, lines[3][:6].split())
        start = 4 + atoms
        cage = model == FIXTURE
        commands = ['''function probe(path,label,topIn,bottomIn,count) {
  load @path
  if (topIn) { {atomno=9}.z = 0.27 }
  if (bottomIn) { {atomno=10}.z = -0.27 }
  set cipRule6Full true
  calculate chirality
  var letters = ""
  for (var i=1; i <= count; i++) { letters += {atomno=i}.chirality }
  print "ROW " + label + " [" + letters + "]"
}''']
        expected = []
        subdir = directory / (model.stem + "-transpositions")
        subdir.mkdir()
        for a, b in combinations(range(bonds), 2):
            changed = lines.copy()
            changed[start+a], changed[start+b] = lines[start+b], lines[start+a]
            path = subdir / f"{a}-{b}.mol"
            path.write_text("\n".join(changed) + "\n")
            orientations = product(("false", "true"), repeat=2) if cage else [("false", "false")]
            for top, bottom in orientations:
                label = f"{a+1}-{b+1}-{top}-{bottom}"
                count = 2 if cage else 8
                commands.append(f'probe("{path}","{label}",{top},{bottom},{count})')
                letter = "r" if top == bottom else "s"
                expected.append(f"ROW {label} [{letter * count}]")
        script = subdir / "test.spt"
        script.write_text("\n".join(commands) + '\nprint "CHECK_END"\n')
        require_equal(rows(script, directory, jar, "release"), expected)
        print(f"{model.stem}: {len(expected)} full-mode controls passed over all single bond-row transpositions")


if __name__ == "__main__":
    with TemporaryDirectory() as work:
        run(Path(work))
