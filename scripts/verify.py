#!/usr/bin/env python3
"""Rebuild and audit the partial development. --require-main enforces full release.
Run using a PATH with the pinned Lean/Lake toolchain. No success is recorded for
an unproved target, a failed command or an unapproved axiom.
"""
import argparse,hashlib,json,os,re,subprocess,sys
from pathlib import Path
from theorem_names import theorem_names
root=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--require-main',action='store_true')
parser.add_argument('--fresh-kernel',action='store_true')
parser.add_argument('--evidence-dir',default='verification',
 help='Evidence directory relative to the project root (use a distinct path for an interrupted-run retry).')
a=parser.parse_args()
v=root/a.evidence_dir;v.mkdir(parents=True,exist_ok=True)
names=sorted({n.strip() for f in (root/'blueprint/src').glob('*.tex')
 for x in re.findall(r'\\lean\{([^}]+)\}',f.read_text()) for n in x.split(',')})
(root/'BlueprintDeclarations.lean').write_text('import Oberwolfach\n'+''.join('#check '+n+'\n' for n in names))
def source_hashes():
 return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
  for p in sorted(root.rglob('*')) if p.is_file() and not p.is_symlink()
  and '.lake' not in p.parts and (p.suffix=='.lean' or p.name in ['lean-toolchain','lake-manifest.json'])}
initial_hashes=source_hashes()
initial_manuscript_hash=hashlib.sha256((root/'source/manuscript.tex').read_bytes()).hexdigest()
verifier_hash=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
steps=[]
def run(args,name,required=True):
 r=subprocess.run(args,cwd=root,capture_output=True,text=True)
 (v/name).write_text(r.stdout+r.stderr)
 steps.append({'command':args,'log':name,'returncode':r.returncode})
 (v/'step-results.json').write_text(json.dumps(steps,indent=2)+'\n')
 if required and r.returncode:
  print(r.stdout+r.stderr);raise SystemExit(f'{args}: failed ({r.returncode})')
 return r
run(['lake','build'],'build.log')
# Check the actual local sources, including any Lake path overrides, rather
# than treating a lockfile string as evidence of the materialized revision.
locked=json.loads((root/'lake-manifest.json').read_text())['packages']
override_file=root/'.lake/package-overrides.json'
overrides={p['name']:p for p in json.loads(override_file.read_text())['packages']} if override_file.exists() else {}
package_revisions={}
for p in locked:
 entry=overrides.get(p['name'],p)
 path=(root/entry['dir']).resolve() if entry['type']=='path' else (root/'.lake/packages'/p['name']).resolve()
 rev=run(['git','-C',str(path),'rev-parse','HEAD'],f"package-{p['name']}-revision.log").stdout.strip()
 if rev != p['rev']:raise SystemExit(f"Pinned revision mismatch for {p['name']}: {rev}")
 run(['git','-C',str(path),'diff','--exit-code','HEAD','--'],f"package-{p['name']}-tracked-diff.log")
 package_revisions[p['name']]=rev
lean_version=run(['lean','--version'],'lean-version.log').stdout.strip()
run(['lake','env','lean','Audit.lean'],'axiom-audit.jsonl')
rows=[json.loads(x) for x in (v/'axiom-audit.jsonl').read_text().splitlines() if x.startswith('{')]
public=[n for f in sorted((root/'Oberwolfach').glob('*.lean'))
 for n in theorem_names(f.read_text())]
assert len(public) == len(set(public)), 'Duplicate public theorem names'
assert all(any(r['name']==n for r in rows) for n in public)
assert all(set(r['axioms']) <= {'propext','Classical.choice','Quot.sound'} for r in rows)
run(['lake','env','lean','BlueprintDeclarations.lean'],'blueprint-declarations.log')
replay=run(['lake','env','leanchecker',*(['--fresh'] if a.fresh_kernel else []),'Oberwolfach'],'kernel-replay.log')
main=run(['lake','env','lean','CheckMain.lean'],'main-release-gate.log',required=False)
files=source_hashes()
if files != initial_hashes:
 raise SystemExit('Verification refused: Lean sources or dependency pins changed during checking.')
if hashlib.sha256((root/'source/manuscript.tex').read_bytes()).hexdigest()!=initial_manuscript_hash:
 raise SystemExit('Verification refused: the manuscript snapshot changed during checking.')
if hashlib.sha256(Path(__file__).read_bytes()).hexdigest()!=verifier_hash:
 raise SystemExit('Verification refused: the verifier changed during checking.')
manifest={'status':'FULL_MAIN_THEOREM_VERIFIED' if main.returncode==0 else 'PARTIAL_FORMALIZATION',
 'main_theorem_proved':main.returncode==0,'public_checked_lemmas':len(public),
 'all_exported_project_theorem_declarations':len(rows),'theorems':[r for r in rows if r['name'] in public],
 'foundational_axioms_allowed':['propext','Classical.choice','Quot.sound'],
 'kernel_replay':'fresh environment, including imports' if a.fresh_kernel else 'project modules against imported environments',
 'kernel_checker':'Lean leanchecker, not an independent kernel implementation',
 'source_sha256':initial_manuscript_hash,
 'source_snapshot_unchanged_during_run':True,'verifier_sha256':verifier_hash,
 'lean_version':lean_version,'actual_package_revisions':package_revisions,'verification_steps':steps,
 'mathlib_revision':next(x['rev'] for x in json.loads((root/'lake-manifest.json').read_text())['packages'] if x['name']=='mathlib'),
 'source_hashes':files,
 'open_obligations':'See blueprint and OPEN_OBLIGATIONS.md; the finite-grid uniformisation theorem does not prove its fixed-set hypothesis.'}
(v/'verification.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(manifest['status'],f"({len(public)} public lemmas checked)")
if a.require_main and main.returncode:raise SystemExit('Full-certificate release refused: main theorem unproved.')
