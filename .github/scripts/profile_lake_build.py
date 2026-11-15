#!/usr/bin/env python3
"""Collect bounded build diagnostics. This is not a Palomar verification."""
import csv
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import threading
import time

out = Path(os.environ['RUNNER_TEMP']) / 'oberwolfach-build-diagnostic'
out.mkdir(parents=True, exist_ok=True)
duration = int(os.environ.get('DIAGNOSTIC_MAX_SECONDS', '3600'))
sample_interval = float(os.environ.get('DIAGNOSTIC_SAMPLE_SECONDS', '5'))
proc_root = Path(os.environ.get('DIAGNOSTIC_PROC_ROOT', '/proc'))
cgroup_path = Path(os.environ.get('DIAGNOSTIC_CGROUP_MEMORY', '/sys/fs/cgroup/memory.current'))
if not (1 <= duration <= 18000 and 0.1 <= sample_interval <= 60):
    raise ValueError('Invalid diagnostic sampling limits')
minimum_available = 2 * 1024 * 1024 * 1024
started = time.monotonic()
counts = {'completed_modules': 0, 'latest_module': None}
ansi = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
completed = re.compile(r'\[\s*\d+/\d+\]\s+(?:Built|Replayed)\s+(\S+)')
interesting = re.compile(r'\[\s*\d+/\d+\]\s+(?:Built|Replayed|Building)|(?:error|warning|panic):', re.I)

def mem_available():
    for line in (proc_root / 'meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) * 1024
    return None

def cgroup_memory():
    try:
        return int(cgroup_path.read_text().strip())
    except (OSError, ValueError):
        return None

def process_snapshot(root_pid):
    listing = subprocess.run(['ps', '-eo', 'pid=,ppid=,rss=,comm='], capture_output=True, text=True, check=True).stdout
    rows = []
    for line in listing.splitlines():
        parts = line.strip().split(None, 3)
        if len(parts) == 4:
            try:
                rows.append((int(parts[0]), int(parts[1]), int(parts[2]), parts[3]))
            except ValueError:
                pass
    descendants = {root_pid}
    for _ in range(20):
        expanded = descendants | {pid for pid, parent, _, _ in rows if parent in descendants}
        if expanded == descendants:
            break
        descendants = expanded
    selected = [(pid, rss, command) for pid, _, rss, command in rows if pid in descendants]
    lean = [(pid, rss) for pid, rss, command in selected if Path(command).name in ('lean', 'lean.real')]
    top = []
    for pid, rss in sorted(lean, key=lambda row: row[1], reverse=True)[:8]:
        module = 'unknown'
        try:
            for arg in (proc_root / str(pid) / 'cmdline').read_bytes().split(b'\0'):
                value = arg.decode('utf-8', errors='replace')
                if value.endswith('.lean'):
                    match = re.search(r'(Oberwolfach|HadwigerLean|FixedPointTheorems)/[A-Za-z0-9_./\-]+\.lean$', value)
                    module = match.group(0) if match else Path(value).name
                    break
        except OSError:
            pass
        top.append(f'{round(rss / 1024, 1)}MiB:{module}')
    return len(lean), sum(rss for _, rss, _ in selected) * 1024, max((rss for _, rss in lean), default=0) * 1024, '; '.join(top)

def consume(stream):
    with (out / 'module-progress.log').open('w', encoding='utf-8') as log:
        for raw in stream:
            line = ansi.sub('', raw).replace('\r', '').rstrip()
            match = completed.search(line)
            if match:
                counts['completed_modules'] += 1
                counts['latest_module'] = match.group(1)
            if interesting.search(line):
                log.write(f'{time.monotonic()-started:.1f} {line[:2000]}\n')
                log.flush()

proc = subprocess.Popen(['lake', '--no-ansi', '-v', 'build', 'Solution'], stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT, text=True, errors='replace', bufsize=1,
                        start_new_session=True)
reader = threading.Thread(target=consume, args=(proc.stdout,), daemon=True)
reader.start()
reason = None
peak_group = None
try:
    with (out / 'resource-samples.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['elapsed_seconds', 'mem_available_bytes', 'cgroup_current_bytes',
                         'lean_processes', 'process_tree_rss_sum_bytes', 'largest_lean_rss_bytes', 'largest_lean_modules',
                         'completed_modules', 'latest_module'])
        while proc.poll() is None:
            available = mem_available()
            group = cgroup_memory()
            if group is not None:
                peak_group = max(peak_group or 0, group)
            lean_count, rss_sum, largest, top_modules = process_snapshot(proc.pid)
            writer.writerow([round(time.monotonic()-started, 1), available, group, lean_count,
                             rss_sum, largest, top_modules, counts['completed_modules'], counts['latest_module']])
            f.flush()
            if available is not None and available < minimum_available:
                reason = 'stopped_for_low_available_memory'
                break
            if time.monotonic() - started >= duration:
                reason = 'sample_duration_reached'
                break
            time.sleep(sample_interval)
    if reason and proc.poll() is None:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=15)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
    returncode = proc.wait()
    reader.join(timeout=15)
    result = {
        'diagnostic_only': True,
        'palomar_verification': False,
        'proof_source_commit': os.environ.get('DIAGNOSTIC_SOURCE_COMMIT'),
        'diagnostic_workflow_commit': os.environ.get('GITHUB_SHA'),
        'outcome': reason or ('build_completed' if returncode == 0 else 'build_failed'),
        'build_returncode': returncode,
        'elapsed_seconds': round(time.monotonic()-started, 1),
        'completed_modules_observed': counts['completed_modules'],
        'latest_module_observed': counts['latest_module'],
        'peak_runner_cgroup_current_bytes_observed': peak_group,
        'note': 'RSS sum may double-count shared memory. A sampled peak may miss spikes. This is not the Palomar sandbox or a theorem verdict.',
    }
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    summary = os.environ.get('GITHUB_STEP_SUMMARY')
    if summary:
        with open(summary, 'a', encoding='utf-8') as f:
            f.write('## Diagnostic only — not Palomar verification\n\n')
            f.write('This job records a bounded build sample; it does not certify the theorem.\n\n')
            f.write('```json\n' + json.dumps(result, indent=2) + '\n```\n')
    print(json.dumps(result, indent=2), flush=True)
finally:
    if proc.poll() is None:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
