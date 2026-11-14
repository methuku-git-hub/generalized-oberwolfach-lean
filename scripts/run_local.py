"""Local helper: reuse this host's existing pinned Lean runtime, without modifying it."""
from pathlib import Path
import os,sys,subprocess
root=Path(__file__).resolve().parents[1]
bin=Path('/Users/Methuku/Documents/Codex/2026-09-20/ca/work/lean-audit/lean-4.34.0-darwin_aarch64/bin')
r=subprocess.run([str(bin/'lake'),*sys.argv[1:]],cwd=root,env=dict(os.environ,PATH=str(bin)+':'+os.environ['PATH']))
raise SystemExit(r.returncode)
