#!/usr/bin/env python3
"""Dependency-aware local compilation and exact-snapshot verification.

Mathlib and its pinned dependencies use their installed compiled cache. No
unrecorded local Wong artifact is on the verification import path. A prior
fully verified baseline may be seeded only by seed_baseline.py, which checks
every source/artifact hash and the linked historical acceptance reports.
Use --clean to recompile every local module from source without that baseline.
"""
from pathlib import Path
from datetime import datetime, timezone
import os, re, sys, json, hashlib, subprocess, time, shutil

ROOT=Path(__file__).resolve().parent
REPORT=ROOT/'verification'
BUILD=ROOT/'.lake/verified/lib/lean'
REPORT.mkdir(exist_ok=True); BUILD.mkdir(parents=True,exist_ok=True)
if '--clean' in sys.argv:
    shutil.rmtree(BUILD)
    BUILD.mkdir(parents=True)
    (REPORT/'build-progress.json').unlink(missing_ok=True)
VENDOR=Path(os.environ.get('WONG_VENDOR','/Users/rinithpina/Documents/Research/Mitter_Conjecture/vendor'))
LEAN=Path(os.environ.get('WONG_LEAN','/Users/rinithpina/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean'))
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[BUILD,VENDOR/'mathlib4/.lake/build/lib/lean',*sorted((VENDOR/'mathlib-deps').glob('*/.lake/build/lib/lean'))]))

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,x):
    p=REPORT/name; q=p.with_suffix(p.suffix+'.tmp')
    q.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n'); q.replace(p)
def strip(s):
    out=[]; i=depth=0
    while i<len(s):
        if s.startswith('/-',i):depth+=1;i+=2
        elif depth and s.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    return ''.join(out)
def path(m):return ROOT/(m.replace('.','/')+'.lean')

order=[]; deps={}; visited=set(); active=set()
def visit(m):
    p=path(m)
    if not p.is_file():
        if m=='Wong' or m.startswith('Wong.'):raise RuntimeError('Missing local module '+m)
        return
    if m in visited:return
    if m in active:raise RuntimeError('Import cycle '+m)
    active.add(m)
    imports=[d for line in re.findall(r'^\s*import\s+([^\n]+)',strip(p.read_text()),re.M) for d in line.split()]
    deps[m]=[d for d in imports if d=='Wong' or d.startswith('Wong.')]
    for d in imports:visit(d)
    active.remove(m);visited.add(m);order.append(m)
visit('Wong')

prepare='--prepare' in sys.argv
skipped=set()
for m in order:
    if prepare and (m in {'Wong.JacobiVisible','Wong.VisibleHeadContradiction'} or any(d in skipped for d in deps[m])):skipped.add(m)
old_path=REPORT/'build-progress.json'
old=json.loads(old_path.read_text()) if old_path.exists() else {}
records=old.get('modules',{})
report={'passed':False,'prepare_only':prepare,'started_utc':datetime.now(timezone.utc).isoformat(),'compiler':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),'modules':records,'order':order,'skipped':sorted(skipped),'verification_mode':'dependency_checked_incremental' if records else 'full_source_rebuild','historical_baseline':old.get('historical_baseline'),'recompiled_this_run':[]}
save('build-progress.json',report)
for n,m in enumerate(order,1):
    if m in skipped:continue
    p=path(m); source_hash=sha(p)
    code=strip(p.read_text())
    bad=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',code)
    if bad:raise RuntimeError(f'Forbidden declaration/proof escape in {m}: {bad}')
    artifact=BUILD/(m.replace('.','/')+'.olean')
    dep_hashes={d:records[d]['artifact_sha256'] for d in deps[m]}
    prior=records.get(m,{})
    if artifact.exists() and prior.get('source_sha256')==source_hash and prior.get('dependency_artifacts')==dep_hashes and prior.get('artifact_sha256')==sha(artifact):continue
    print(f'[{n}/{len(order)}] {m}',flush=True)
    artifact.parent.mkdir(parents=True,exist_ok=True)
    temporary=artifact.with_suffix('.pending.olean')
    log=REPORT/(m.replace('.','-')+'.log')
    t=time.monotonic()
    with log.open('w') as stream:
        result=subprocess.run([str(LEAN),'-o',str(temporary),str(p.relative_to(ROOT))],cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if result.returncode or not temporary.exists():
        report['failure']={'module':m,'exit_code':result.returncode,'log':log.name};save('build-progress.json',report)
        print(log.read_text(),flush=True);raise SystemExit(result.returncode or 1)
    if sha(p)!=source_hash:raise RuntimeError('Source changed during compilation: '+m)
    temporary.replace(artifact)
    records[m]={'source_sha256':source_hash,'artifact_sha256':sha(artifact),'dependency_artifacts':dep_hashes,'seconds':round(time.monotonic()-t,3),'exit_code':0,'log':log.name}
    report['recompiled_this_run'].append(m)
    save('build-progress.json',report)
if prepare:
    print('PREPARED: unchanged prerequisites compiled; final verification still required.',flush=True)
    raise SystemExit(0)

for m in order:
    if records[m]['source_sha256']!=sha(path(m)):raise RuntimeError('Snapshot changed: '+m)
    if records[m]['artifact_sha256']!=sha(BUILD/(m.replace('.','/')+'.olean')):raise RuntimeError('Artifact changed: '+m)
report['passed']=True
report['finished_utc']=datetime.now(timezone.utc).isoformat()
report['source_inventory']={m:sha(path(m)) for m in order}
report['local_module_count']=len(order)
save('fresh-build.json',report)
save('build-progress.json',report)
print(f'PASS: {len(order)} local modules match the checked dependency snapshot; {len(report["recompiled_this_run"])} recompiled this run.',flush=True)

# Every public theorem/lemma in the retained local source closure is audited.
names=[]
for m in order:
    stack=[]
    for line in strip(path(m).read_text()).splitlines():
        ns=re.match(r'\s*namespace\s+([\w.]+)',line)
        sec=re.match(r'\s*(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$',line)
        end=re.match(r'\s*end(?:\s+([\w.]+))?\s*$',line)
        if ns:stack.append(('ns',ns.group(1)))
        elif sec:stack.append(('section',sec.group(1)))
        elif end:
            if not stack:raise RuntimeError('Unmatched end in '+m)
            stack.pop()
        else:
            prefix='.'.join(n for k,n in stack if k=='ns')
            for name in re.findall(r'\b(?:theorem|lemma)\s+([\w.\u0027]+)',line):names.append((prefix+'.' if prefix else '')+name)
audit=ROOT/'AxiomAudit.lean'
audit.write_text('import Wong\n\n'+''.join('#print axioms '+n+'\n' for n in names))
print(f'Auditing axioms of {len(names)} local theorem/lemma declarations...',flush=True)
r=subprocess.run([str(LEAN),str(audit.relative_to(ROOT))],cwd=ROOT,env=env,capture_output=True,text=True)
output=r.stdout+r.stderr;(REPORT/'axioms.log').write_text(output)
if r.returncode:print(output[-6000:]);raise SystemExit('Axiom audit failed')
allowed={'propext','Classical.choice','Quot.sound'}; found={}
for n in names:
    matches=re.findall(r"'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",output,re.S)
    absent=f"'{n}' does not depend on any axioms" in output
    if not matches and not absent:raise RuntimeError('Missing axiom report for '+n)
    axioms=sorted({x.strip() for match in matches for x in match.split(',') if x.strip()})
    if set(axioms)-allowed:raise RuntimeError('Unexpected axioms for '+n+': '+str(axioms))
    found[n]=axioms
save('axioms.json',{'passed':True,'theorem_count':len(names),'allowed_axioms':sorted(allowed),'declarations':found,'fresh_build_sha256':sha(REPORT/'fresh-build.json'),'audit_source_sha256':sha(audit)})
print('PASS: all local theorem/lemma dependencies use only the three standard foundational axioms.',flush=True)

print('Checking exact theorem types and inspecting actual proof routes...',flush=True)
route=ROOT/'ProofRouteAudit.lean'
r=subprocess.run([str(LEAN),str(route.relative_to(ROOT))],cwd=ROOT,env=env,capture_output=True,text=True)
output=r.stdout+r.stderr;(REPORT/'proof-routes.log').write_text(output)
route_passed=r.returncode==0 and 'PROOF_ROUTE_AUDIT_PASSED' in output
save('proof-routes.json',{'passed':route_passed,'lean_exit_code':r.returncode,'audit_source_sha256':sha(route),'fresh_build_sha256':sha(REPORT/'fresh-build.json'),'diagnostics_log':'proof-routes.log'})
if not route_passed:
    print(output[-6000:]);raise SystemExit('Exact-type/proof-route audit failed')
for m in order:
    if sha(path(m))!=report['source_inventory'][m]:raise RuntimeError('Sources changed during audits: '+m)
save('acceptance.json',{'passed':True,'checked_at_utc':datetime.now(timezone.utc).isoformat(),'source_module_count':len(order),'theorem_count':len(names),'sorry_count':0,'external_mathematical_axioms':[],'allowed_foundational_axioms':sorted(allowed),'main_statement_sha256':sha(ROOT/'Wong/MainStatement.lean'),'build_report_sha256':sha(REPORT/'fresh-build.json'),'axiom_report_sha256':sha(REPORT/'axioms.json'),'proof_route_report_sha256':sha(REPORT/'proof-routes.json'),'verification_script_sha256':sha(Path(__file__)),'source_inventory':report['source_inventory']})
print('PASS: exact original proposition, new Jacobi route, zero placeholders, and normal foundational axiom dependencies.',flush=True)
