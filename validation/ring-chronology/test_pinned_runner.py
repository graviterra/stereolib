"""Regression checks for the reviewed Centres byte snapshots. Run after setup.sh."""
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
INSTALL = ROOT / ".cache" / "centres10"
RUNNER = ROOT / "tools" / "centres10" / "run_pinned.py"


class EmbeddedInputsTest(unittest.TestCase):
    def test_bounded_build_key_tracks_both_embedded_inputs(self):
        source = (ROOT / "TetraStereo/Engine/CentresRing.lean").read_text()
        for name in ("release-1.0.json", "run_pinned.py"):
            digest = hashlib.sha256((RUNNER.parent / name).read_bytes()).hexdigest()
            self.assertIn(f"-- {name} SHA-256 {digest}\n", source)


@unittest.skipUnless((INSTALL / "guava.jar").is_file(), "prepare the Centres bytecode first")
class PinnedRunnerTest(unittest.TestCase):
    def test_snapshot_in_temp_path_with_classpath_separator(self):
        with tempfile.TemporaryDirectory() as parent:
            scratch = Path(parent) / "spiro:receipts"
            scratch.mkdir()
            env = dict(os.environ, TMPDIR=str(scratch), JAVA_TOOL_OPTIONS="-XX:InvalidTestOption")
            cp = os.pathsep.join(str(INSTALL / name) for name in ("classes", "guava.jar"))
            p = subprocess.run(["/usr/bin/python3", "-I", str(RUNNER), cp],
                               input=b"centres-1.0\n", capture_output=True, env=env, check=True)
            self.assertEqual(p.stdout, b"[]\n")
            self.assertEqual(p.stderr, b"")
