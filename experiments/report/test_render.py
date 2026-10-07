"""Regression checks for the report driver's verification exit status."""
import contextlib
import importlib.util
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("render_source.py")
spec = importlib.util.spec_from_file_location("publication_renderer", SCRIPT)
renderer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renderer)


class ReportExitTests(unittest.TestCase):
    def exercise(self, passed):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "source").mkdir()
            (root / "runs").mkdir()
            analysis = {"integration_refinement_pass": passed,
                        "conditions": [{"jump_times": [], "returned": {}, "A_sp_recorded": 1.0}]}
            with patch.object(sys, "argv", [str(SCRIPT), "--root", str(root), "--out", str(root / "report")]), \
                    patch.object(renderer, "analyze", return_value=(analysis, {})), \
                    patch.object(renderer, "figures", return_value=[]), \
                    patch.object(renderer, "report"), contextlib.redirect_stdout(io.StringIO()):
                renderer.main()

    def test_success_returns_normally(self):
        self.exercise(True)

    def test_failed_refinement_is_not_success(self):
        with self.assertRaises(SystemExit):
            self.exercise(False)

    def test_optimized_python_is_rejected(self):
        result = subprocess.run([sys.executable, "-O", str(SCRIPT), "--help"],
                                capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("without Python -O", result.stderr)


if __name__ == "__main__":
    unittest.main()
