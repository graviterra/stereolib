"""Trace both ring-junction choices in Centres 1.0 on the authors' 3D decalin pair.

Pass compounds_3d.sdf, the Centres 1.0 executable jar, and the release's
core/src/main/java/com/simolecule/centres/rules/Sort.java, in that order.
The diagnostic observes each native comparison before its ordinary return.
"""

import hashlib
import os
import re
import subprocess
import sys
from decimal import Decimal
from pathlib import Path
from tempfile import TemporaryDirectory


def checked(path, digest):
    data = Path(path).read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f"Source digest mismatch for {path}")
    return data


def mirror(record):
    lines = record.splitlines()
    for i in range(4, 32):
        lines[i] = f"{-Decimal(lines[i][:10]):10.4f}" + lines[i][10:]
    return "\n".join(lines) + "\n"


def main(sdf, jar, sort):
    corpus = checked(sdf, "28a000b36506dabe5a45f6d7672451c61c6e34f3e0f027f2599000d850273325")
    checked(jar, "99fd24cfbb73a138942cf30012980d2174b5a185c61739550a118b16ba1f03bd")
    source = checked(sort, "b45257bb4fe69ef4dff9bab396e52728acd6e94ed37e7956898bcef35cb5eac3").decode()
    anchor = "if (cmp != 0) {"
    if not (source.count(anchor) == 1):
        raise ValueError("Decalin replay check failed: source.count(anchor) == 1")
    logging = """
      if (node == node.getDigraph().getRoot() && node == node.getDigraph().getCurrRoot()
          && a.isBeg(node) && b.isBeg(node) && deep) {
        int root = node.getDigraph().getMol().getAtomIdx(node.getAtom());
        int x = node.getDigraph().getMol().getAtomIdx(a.getEnd().getAtom());
        int y = node.getDigraph().getMol().getAtomIdx(b.getEnd().getAtom());
        if ((root == 0 && Math.min(x,y) == 2 && Math.max(x,y) == 6) ||
            (root == 1 && Math.min(x,y) == 3 && Math.max(x,y) == 8))
          {
            if (cmp != 0 && rule.getClass().getSimpleName().equals("Rule5New")) {
              traceAux(a.getEnd(), root+"."+x);
              traceAux(b.getEnd(), root+"."+y);
            }
            System.err.printf("TRACE %d %d %d %s %d%n",root,x,y,rule.getClass().getSimpleName(),cmp);
          }
      }
      """
    method = "public final int compareLigands("
    if not (source.count(method) == 1):
        raise ValueError("Decalin replay check failed: source.count(method) == 1")
    trace_aux = """
    private void traceAux(Node<A,B> node, String path) {
      String label = String.valueOf(node.getAux());
      if (label.equals("R") || label.equals("S"))
        System.err.printf("AUX %s %s%n", path, label);
      for (Edge<A,B> edge : node.getEdges()) {
        if (!edge.isBeg(node)) continue;
        Node<A,B> child = edge.getEnd();
        if (!child.isDuplicate() && child.getAtom() != null)
          traceAux(child, path+"."+node.getDigraph().getMol().getAtomIdx(child.getAtom()));
      }
    }
    """
    source = source.replace(method, trace_aux + method)
    opposite_paths = [
        {2: "0.2.4.5.3.1", 6: "0.6.7.9.8.1"},
        {3: "1.3.5.4.2.0", 8: "1.8.9.7.6.0"},
    ]
    stages = ["Rule1a", "Rule1b", "Rule2", "Rule3", "Rule4a", "Rule4b", "Rule4c", "Rule5New"]
    with TemporaryDirectory() as tmp:
        path = Path(tmp)
        java = path / "Sort.java"
        java.write_text(source.replace(anchor, logging + anchor))
        subprocess.run(["java", "-Xmx256m", "-m", "jdk.compiler/com.sun.tools.javac.Main",
                        "-cp", jar, "-d", tmp, str(java)], check=True)
        for name, label, original, reflected in [
            ("VS211", "s", (2, 8), (6, 3)), ("VS212", "r", (6, 8), (2, 3))
        ]:
            record, = (r.lstrip("\r\n") for r in corpus.decode().split("$$$$")
                       if r.lstrip("\r\n").startswith(name + "\n"))
            for geometry, content, winners in [
                ("original", record, original), ("mirror", mirror(record), reflected)
            ]:
                fixture = path / (name + ".sdf")
                fixture.write_text(content + "$$$$\n")
                result = subprocess.run(["java", "-Xmx256m", "-cp", os.pathsep.join((tmp, str(Path(jar).resolve()))),
                                         "com.simolecule.centres.LabelCip", str(fixture)],
                                        check=True, text=True, capture_output=True)
                if not (result.stdout.split() == [f"1{label}", f"2{label}", name]):
                    raise ValueError("Decalin replay check failed: result.stdout.split() == [f\"1{label}\", f\"2{label}\", name]")
                for root, winner in enumerate(winners):
                    rows = re.findall(rf"^TRACE {root} (\d+) (\d+) (\w+) (-?\d+)$",
                                      result.stderr, re.MULTILINE)
                    final = rows[-len(stages):]
                    if not ([r[2] for r in final] == stages):
                        raise ValueError("Decalin replay check failed: [r[2] for r in final] == stages")
                    if not (all(r[3] == "0" for r in final[:-1])):
                        raise ValueError("Decalin replay check failed: all(r[3] == \"0\" for r in final[:-1])")
                    a, b, _, cmp = final[-1]
                    if not (abs(int(cmp)) == 2 and int(a if int(cmp) > 0 else b) == winner):
                        raise ValueError("Decalin replay check failed: abs(int(cmp)) == 2 and int(a if int(cmp) > 0 else b) == winner")
                aux = re.findall(r"^AUX ([0-9.]+) ([RS])$", result.stderr, re.MULTILINE)
                expected_aux = {(path, "R" if arm == winners[root] else "S")
                                for root, paths in enumerate(opposite_paths) for arm, path in paths.items()}
                if not (sorted(aux) == sorted(expected_aux)):
                    raise ValueError("Decalin replay check failed: sorted(aux) == sorted(expected_aux)")
                print(f"{name} {geometry} junctions 0,1: Rule 5 winners {winners}, {label}/{label}")


if __name__ == "__main__":
    main(*sys.argv[1:])
