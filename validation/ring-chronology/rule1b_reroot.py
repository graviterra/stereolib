"""Replay Rule1b reroot behavior using the exact reviewed Centres 1.0 class bytes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[2]
INSTALL = ROOT / ".cache/centres10"
MANIFEST = ROOT / "tools/centres10/release-1.0.json"


def checked(path, digest):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f"Pinned digest mismatch: {path}")
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--roots", action="store_true",
                        help="also compare controlled auxiliary inversions and uniform Rule 1b metrics at a tetrahedral root")
    parser.add_argument("--ecj", type=Path, default=Path(os.environ.get("ECJ_JAR", "/usr/share/java/eclipse-jdt-core-compiler-batch.jar")), help="Eclipse JDT batch compiler jar")
    parser.add_argument("--cache", type=Path, default=INSTALL, help="pinned Centres installation")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    with tempfile.TemporaryDirectory(prefix="rule1b-reroot-") as directory:
        work = Path(directory)
        core = work / "centres.jar"
        with zipfile.ZipFile(core, "w") as jar:
            for name, digest in manifest["classes"].items():
                jar.writestr(name, checked(args.cache / "classes" / name, digest))
        guava = work / "guava.jar"
        guava.write_bytes(checked(args.cache / "guava.jar", manifest["guava_sha256"]))
        cp = os.pathsep.join(map(str, (core, guava)))
        probes = ["CentresRule1bReroot"]
        if args.roots:
            probes.extend(["CentresOxaziridineRoot", "CentresAuxiliaryDistance"])
        sources = [ROOT / "validation/ring-chronology" / f"{name}.java"
                   for name in ["CentresProbe", *probes]]
        env = {"PATH": os.environ.get("PATH", os.defpath), "LANG": "C"}
        subprocess.run(["java", "-Xmx256m", "-jar",
                        str(args.ecj),
                        "-1.8", "-proc:none", "-warn:none", "-cp", cp, "-d", str(work),
                        *map(str, sources)], check=True, env=env)
        print(f"Centres commit={manifest['commit']}; all manifest class hashes verified", flush=True)
        for probe in probes:
            # The upstream labeller can catch an exception and report it on stderr.
            result = subprocess.run(["java", "-Xmx256m", "-cp", os.pathsep.join((str(work), cp)), probe],
                                    capture_output=True, text=True, check=True, env=env)
            if result.stderr:
                raise RuntimeError(f"{probe} wrote to stderr: {result.stderr}")
            print(result.stdout, end="")


if __name__ == "__main__":
    main()
