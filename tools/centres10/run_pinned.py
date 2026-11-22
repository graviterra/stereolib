"""Run the reviewed Centres 1.0 class bytes from a private classpath snapshot."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile


def checked_bytes(path: Path, expected: str, limit: int) -> bytes:
    with path.open("rb") as stream:
        data = stream.read(limit + 1)
    if len(data) > limit or hashlib.sha256(data).hexdigest() != expected:
        raise ValueError(f"Centres release digest mismatch for {path}")
    return data


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("classpath", help="prepared classes directory and Guava 13.0 jar")
    parser.add_argument("--rule-prefixes", action="store_true")
    args = parser.parse_args()
    parts = args.classpath.split(os.pathsep)
    if len(parts) != 2 or not all(parts):
        parser.error("expected a classes directory followed by the pinned dependency jar")
    classes, dependency = map(Path, parts)
    # The public Lean artifact embeds this dictionary and this runner together.
    manifest = globals().get("PINNED_RELEASE")
    if manifest is None:
        manifest = json.loads(Path(__file__).with_name("release-1.0.json").read_text())
    # Only reviewed bytes enter either archive passed to Java. Ignored extra files
    # and changes to the input paths after these reads cannot change the snapshot.
    with tempfile.TemporaryDirectory(prefix="centres-release-") as tmp:
        private = Path(tmp)
        core = private / "centres.jar"
        guava = private / "guava.jar"
        with zipfile.ZipFile(core, "w") as archive:
            for name, digest in manifest["classes"].items():
                archive.writestr(name, checked_bytes(classes / name, digest, 2**20))
        guava.write_bytes(checked_bytes(dependency, manifest["guava_sha256"], 4 * 2**20))
        command = ["/usr/bin/java", "-Xmx768m", "-cp", os.pathsep.join((core.name, guava.name)), "Centres10"]
        if args.rule_prefixes:
            command.append("--rule-prefixes")
        # Use the host JVM with no ambient Java options, agents, or user classpath.
        return subprocess.run(command, cwd=private, env={"PATH": "/usr/bin:/bin", "LANG": "C"},
                              check=False).returncode


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as exc:
        sys.exit(str(exc))
