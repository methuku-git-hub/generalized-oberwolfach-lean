#!/usr/bin/env python3
"""Observe a pinned verifier on an isolated CI worker. This is not a preflight."""
import csv
import json
import os
from pathlib import Path
import subprocess
import sys
import time

temp = Path(os.environ["RUNNER_TEMP"])
out = temp / "comparator-memory-diagnostic"
out.mkdir(exist_ok=True)
report = temp / "mechanical-report.json"
exports = temp / "palomar" / "exports"
command = [sys.executable, "pipeline/scripts/verify_submission.py", "execute",
           "--work-dir", str(temp / "palomar"), "--output", str(report),
           "--bwrap", os.environ["PALOMAR_BWRAP"], "--bwrap-source-tag", "v0.12.0",
           "--execution-budget-seconds", "19800", "--workflow-url",
           os.environ["GITHUB_SERVER_URL"] + "/" + os.environ["GITHUB_REPOSITORY"]
           + "/actions/runs/" + os.environ["GITHUB_RUN_ID"]]

def processes():
    result = []
    for path in Path("/proc").iterdir():
        if not path.name.isdigit():
            continue
        try:
            fields = {}
            for line in (path / "status").read_text().splitlines():
                key, sep, value = line.partition(":")
                if sep and key in ("Name", "PPid", "VmRSS"):
                    fields[key] = value.strip()
            rss = int(fields.get("VmRSS", "0 kB").split()[0]) * 1024
            if rss:
                result.append((rss, path.name, fields.get("PPid", "?"), fields.get("Name", "?")))
        except (OSError, ValueError, ProcessLookupError):
            continue
    return sorted(result, reverse=True)[:20]

def read(path):
    try:
        return path.read_text().strip()
    except OSError:
        return ""

proc = subprocess.Popen(command)
start = time.monotonic()
stage = "starting"
with (out / "samples.csv").open("w", newline="") as handle:
    writer = csv.writer(handle)
    writer.writerow(["seconds", "stage", "mem_available_kib", "solution_export_bytes",
                     "top_processes_rss_bytes_pid_ppid_name"])
    while proc.poll() is None:
        try:
            current = json.loads(report.read_text()).get("stage", stage)
        except (OSError, ValueError):
            current = stage
        if current != stage:
            stage = current
            print(f"Diagnostic phase: {stage}", flush=True)
        if stage in ("solution-export", "comparator", "con-ron", "resource-exhausted"):
            available = next((x for x in read(Path('/proc/meminfo')).splitlines()
                              if x.startswith('MemAvailable:')), '')
            candidates = list(exports.rglob("solution.export")) if exports.exists() else []
            sizes = []
            for candidate in candidates:
                try:
                    sizes.append(candidate.stat().st_size)
                except OSError:
                    pass
            writer.writerow([round(time.monotonic() - start, 1), stage, available,
                             max(sizes, default=""), json.dumps(processes())])
            handle.flush()
            time.sleep(1)
        else:
            time.sleep(10)
result = {"diagnostic_only": True, "official_palomar_preflight": False,
          "proof_commit": "c0d30d23c6c58dc41c03c9ce126e1ce1d846519a",
          "verifier_exit_code": proc.returncode, "last_observed_stage": stage,
          "elapsed_seconds": round(time.monotonic() - start, 1),
          "limitations": "Samples are approximate. This instrumented, separate job is not Palomar's reusable preflight or a theorem verdict."}
(out / "diagnostic.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2), flush=True)
