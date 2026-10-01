#!/usr/bin/env python3
"""Dependency-aware local compilation and exact-snapshot verification.

Mathlib and its pinned dependencies use their installed compiled cache. No
unrecorded local Wong artifact is on the verification import path. A prior
fully verified baseline is identified by its saved source/artifact hashes and
linked historical acceptance reports. Use --clean to recompile every local
module from source without that baseline. Third-party compiled caches remain
trusted to correspond to their checked source pins; they are not rebuilt or
exhaustively hashed by this script.
"""
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse, os, re, sys, json, hashlib, subprocess, time, shutil, tarfile, fcntl

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--clean',action='store_true')
parser.add_argument('--prepare',action='store_true')
parser.add_argument('--jobs',type=int,default=1,
    help='maximum independent Lean compiler processes (each uses -j1; default: 1)')
args=parser.parse_args()
if args.jobs<1:parser.error('--jobs must be at least 1')

ROOT=Path(__file__).resolve().parent
REPORT=ROOT/'verification'
BUILD=ROOT/'.lake/verified/lib/lean'
REPORT.mkdir(exist_ok=True)

EXPECTED_MAIN_STATEMENT_SHA256='e181c7235f8673ffc967f83ddf8e6299bdabbc79a43fd9cc21bd817168047970'
EXPECTED_LEAN_TOOLCHAIN='leanprover/lean4:v4.35.0-rc2'
EXPECTED_LEAN_RELEASE='4.35.0-rc2'
EXPECTED_LEAN_COMMIT='11acb17ec6b07a8f9e9173e6845197929540936b'
RUN_STARTED_UTC=datetime.now(timezone.utc).isoformat()

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,x):
    p=REPORT/name; q=p.with_suffix(p.suffix+'.tmp')
    q.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n'); q.replace(p)

# Invalidate success before checking the compiler, dependencies, or sources.
# An exception or interruption at any later stage cannot leave old success live.
save('acceptance.json',{'passed':False,'started_utc':RUN_STARTED_UTC,
    'status':'verification_in_progress','verification_script_sha256':sha(Path(__file__))})

if sha(ROOT/'Wong/MainStatement.lean')!=EXPECTED_MAIN_STATEMENT_SHA256:
    raise RuntimeError('The reviewed current MainStatement.lean has changed.')
frozen_statements=json.loads((ROOT/'frozen-statements.json').read_text())
for statement,digest in frozen_statements.items():
    if sha(ROOT/statement)!=digest:
        raise RuntimeError('A reviewed current/PDF proposition has changed: '+statement)

BUILD.mkdir(parents=True,exist_ok=True)
if args.clean:
    shutil.rmtree(BUILD)
    BUILD.mkdir(parents=True)
    (REPORT/'build-progress.json').unlink(missing_ok=True)
VENDOR=Path(os.environ.get('WONG_VENDOR','/Users/rinithpina/Documents/Research/Mitter_Conjecture/vendor'))
LEAN=Path(os.environ.get('WONG_LEAN','/Users/rinithpina/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean'))
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[BUILD,VENDOR/'mathlib4/.lake/build/lib/lean',*sorted((VENDOR/'mathlib-deps').glob('*/.lake/build/lib/lean'))]))

def json_fingerprint(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def git_read(repo,*args):
    git_env=os.environ.copy();git_env['GIT_OPTIONAL_LOCKS']='0'
    return subprocess.check_output(['git','-c','core.fsmonitor=false','-C',str(repo),*args],
        text=True,env=git_env).strip()

def check_clean_git(repo,expected_commit):
    commit=git_read(repo,'rev-parse','HEAD')
    if commit!=expected_commit:
        raise RuntimeError(f'Wrong source commit for {repo}: {commit}, expected {expected_commit}')
    status=git_read(repo,'status','--porcelain=v1','--untracked-files=all')
    if status:
        raise RuntimeError(f'Pinned dependency source tree is dirty: {repo}\n{status[:2000]}')
    return {'commit':commit,'dirty':False}

def check_dependency_archive(name,pin):
    """Verify a pinned archive and every installed file supplied by it.

    Archives are read only, never extracted. Extra generated build files are
    permitted, but additional Lean source files outside .lake/.git are rejected.
    A clean git checkout at the exact revision is an alternative on other hosts.
    """
    installed=VENDOR/'mathlib-deps'/name
    if not installed.is_dir():
        raise RuntimeError(f'Missing installed dependency source directory: {installed}')
    if (installed/'.git').exists():
        return {'mode':'clean_git_source_pin',**check_clean_git(installed,pin['rev'])}
    archive=VENDOR/'mathlib-deps'/(name+'.tar.gz')
    if not archive.is_file():
        raise RuntimeError(f'Need either pinned archive {archive} or a clean git source checkout.')
    archive_hash=sha(archive)
    if archive_hash!=pin['archive_sha256']:
        raise RuntimeError(f'Archive hash mismatch for dependency {name}')
    expected_lean=set();source_entries=[];top=None
    with tarfile.open(archive,'r:gz') as stream:
        for member in stream.getmembers():
            parts=PurePosixPath(member.name).parts
            if not parts or parts[0]=='/' or '..' in parts:
                raise RuntimeError(f'Unexpected archive member in {name}: {member.name}')
            if top is None:top=parts[0]
            if parts[0]!=top:
                raise RuntimeError(f'Multiple archive roots for dependency {name}')
            if len(parts)==1 or member.isdir():continue
            relative=PurePosixPath(*parts[1:]);target=installed.joinpath(*relative.parts)
            if member.issym():
                if not target.is_symlink() or os.readlink(target)!=member.linkname:
                    raise RuntimeError(f'Pinned dependency symlink differs from archive: {target}')
                if not target.resolve().is_relative_to(installed.resolve()):
                    raise RuntimeError(f'Dependency symlink leaves its source tree: {target}')
                source_entries.append([str(relative),'symlink:'+member.linkname])
                if relative.suffix=='.lean':expected_lean.add(str(relative))
                continue
            if not member.isfile():
                raise RuntimeError(f'Unsupported non-regular pinned archive member: {name}/{relative}')
            if not target.is_file() or target.is_symlink():
                raise RuntimeError(f'Missing or symlinked pinned dependency file: {target}')
            archived=stream.extractfile(member)
            if archived is None:raise RuntimeError(f'Unreadable archive member: {member.name}')
            expected=hashlib.sha256(archived.read()).hexdigest()
            if sha(target)!=expected:
                raise RuntimeError(f'Installed dependency differs from pinned archive: {target}')
            source_entries.append([str(relative),expected])
            if relative.suffix=='.lean':expected_lean.add(str(relative))
    actual_lean={str(p.relative_to(installed)) for p in installed.rglob('*.lean')
        if not any(x in {'.lake','.git'} for x in p.relative_to(installed).parts)}
    if actual_lean!=expected_lean:
        raise RuntimeError(f'Unpinned Lean source files in dependency {name}: '
            f'{sorted(actual_lean-expected_lean)[:20]}')
    return {'mode':'archive_and_installed_sources','revision':pin['rev'],
        'archive_sha256':archive_hash,'verified_file_count':len(source_entries),
        'installed_source_inventory_sha256':json_fingerprint(sorted(source_entries))}

def check_environment():
    pins_path=ROOT/'dependencies.json';pins=json.loads(pins_path.read_text())
    if pins.get('lean')!=EXPECTED_LEAN_TOOLCHAIN:
        raise RuntimeError('dependencies.json does not name the fixed Lean toolchain.')
    if (ROOT/'lean-toolchain').read_text().strip()!=EXPECTED_LEAN_TOOLCHAIN:
        raise RuntimeError('lean-toolchain differs from the fixed compiler release.')
    compiler=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
    parsed=re.fullmatch(r'Lean \(version ([^,]+), (.*), commit ([0-9a-f]+), Release\)',compiler)
    if not parsed or parsed.group(1)!=EXPECTED_LEAN_RELEASE or parsed.group(3)!=EXPECTED_LEAN_COMMIT:
        raise RuntimeError('Wrong Lean release/commit (Release build required): '+compiler)
    mathlib=VENDOR/'mathlib4'
    mathlib_state=check_clean_git(mathlib,pins['repositories']['mathlib4']['commit'])
    manifest=mathlib/'lake-manifest.json';manifest_hash=sha(manifest)
    if manifest_hash!=pins['mathlib_manifest_sha256']:
        raise RuntimeError('Mathlib dependency manifest differs from the pinned manifest.')
    manifest_pins={p['name']:p for p in json.loads(manifest.read_text())['packages']}
    dependencies={}
    for name,pin in sorted(pins['manifest_dependency_pins'].items()):
        actual=manifest_pins.get(name,{})
        if actual.get('rev')!=pin['rev'] or actual.get('url')!=pin['url']:
            raise RuntimeError('Dependency pin differs between manifest and dependencies.json: '+name)
        dependencies[name]=check_dependency_archive(name,pin)
    return {'compiler':compiler,'compiler_path':str(LEAN.resolve()),
        'compiler_binary_sha256':sha(LEAN),'lean_toolchain_sha256':sha(ROOT/'lean-toolchain'),
        'vendor_path':str(VENDOR.resolve()),'dependencies_file_sha256':sha(pins_path),
        'mathlib':{**mathlib_state,'manifest_sha256':manifest_hash},
        'dependencies':dependencies,
        'third_party_cache_trust':'Installed compiled caches are trusted to correspond to the checked '
            'pinned source trees; they are not rebuilt or exhaustively hashed.'}

environment=check_environment()
environment_fingerprint=json_fingerprint(environment)
save('environment.json',{'passed':True,'fingerprint':environment_fingerprint,
    'checked_at_utc':datetime.now(timezone.utc).isoformat(),'environment':environment})

def validate_environment_reuse(previous):
    """Reject changed environments; allow one checked legacy-report migration.

    Legacy reports did not contain an environment fingerprint. Migration needs
    the exact compiler string of this accepted incremental run, the historical
    baseline's hashed lean-toolchain, the linked baseline report, and all live
    pinned-source checks above. It adds metadata without recompiling unchanged
    local modules. Future environment differences require --clean.
    """
    if not previous.get('modules'):return None
    prior=previous.get('environment_fingerprint')
    if prior:
        if prior!=environment_fingerprint:
            raise RuntimeError('Verification environment changed; use ./check.sh --clean before reusing modules.')
        return previous.get('environment_migration')
    if previous.get('compiler')!=environment['compiler']:
        raise RuntimeError('Legacy artifact reuse requires the original compiler string; use --clean.')
    baseline_path=REPORT/'baseline/fresh-build.json'
    validation_path=REPORT/'baseline-validation.json'
    baseline=json.loads(baseline_path.read_text());validation=json.loads(validation_path.read_text())
    if not baseline.get('passed') or not validation.get('all_historical_sources_and_artifacts_match'):
        raise RuntimeError('Legacy artifact reuse lacks a validated successful historical baseline.')
    if validation.get('build_report_sha256')!=sha(baseline_path):
        raise RuntimeError('Historical baseline report hash mismatch during environment migration.')
    if validation.get('build_id')!=baseline.get('build_id'):
        raise RuntimeError('Historical baseline build IDs differ.')
    if previous.get('historical_baseline')!=validation:
        raise RuntimeError('Progress report is not linked to this validated historical baseline.')
    if baseline.get('verification_scripts_sha256',{}).get('lean-toolchain')!=environment['lean_toolchain_sha256']:
        raise RuntimeError('Original baseline compiler toolchain pin differs from the checked environment.')
    return {'mode':'checked_legacy_fingerprint_migration','baseline_build_id':baseline['build_id'],
        'baseline_report_sha256':sha(baseline_path),'validation_report_sha256':sha(validation_path),
        'legacy_progress_sha256':sha(REPORT/'build-progress.json'),
        'compiler_identity':environment['compiler'],'pins_checked':True,
        'note':'Original baseline pins the toolchain file; the accepted legacy incremental report '
            'records the exact release/commit compiler string. Existing local artifacts are preserved.'}

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

prepare=args.prepare
skipped=set()
for m in order:
    if prepare and (m in {'Wong.JacobiVisible','Wong.VisibleHeadContradiction'} or any(d in skipped for d in deps[m])):skipped.add(m)
old_path=REPORT/'build-progress.json'
old=json.loads(old_path.read_text()) if old_path.exists() else {}
records=old.get('modules',{})
environment_migration=validate_environment_reuse(old)
report={'passed':False,'prepare_only':prepare,'started_utc':RUN_STARTED_UTC,
    'compiler':environment['compiler'],'environment_fingerprint':environment_fingerprint,
    'environment_report_sha256':sha(REPORT/'environment.json'),
    'environment_migration':environment_migration,'modules':records,'order':order,
    'skipped':sorted(skipped),'verification_mode':'dependency_checked_incremental' if records else 'full_source_rebuild',
    'historical_baseline':old.get('historical_baseline'),'recompiled_this_run':[],
    'compiler_jobs':args.jobs}
save('build-progress.json',report)

def compile_module(m,artifact):
    """Workers write only their own temporary artifact and diagnostic log."""
    artifact.parent.mkdir(parents=True,exist_ok=True)
    temporary=artifact.with_suffix('.pending.olean')
    temporary.unlink(missing_ok=True)
    log=REPORT/(m.replace('.','-')+'.log')
    t=time.monotonic()
    with log.open('w') as stream:
        result=subprocess.run([str(LEAN),'-j1','-o',str(temporary),str(path(m).relative_to(ROOT))],
            cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
    return result.returncode,temporary,log,round(time.monotonic()-t,3)

pending=[m for m in order if m not in skipped]
completed=set()
recompiled=set()
running={}
positions={m:n for n,m in enumerate(order,1)}
current_module=None

# Keep one exclusive compiler lock across the whole scheduler. Within this
# verifier, independent processes may run concurrently; no other cooperating
# verifier/compiler may replace a dependency artifact during a compilation.
with (ROOT/'development/compiler.lock').open('a+') as compiler_lock:
    fcntl.flock(compiler_lock,fcntl.LOCK_EX)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        try:
            while pending or running:
                # Only dependencies accepted in this run may feed a worker.
                # Reusable modules pass the same source/dependency/artifact
                # hash checks as freshly compiled modules.
                for m in list(pending):
                    if not all(d in completed for d in deps[m]):continue
                    current_module=m
                    p=path(m);source_hash=sha(p)
                    code=strip(p.read_text())
                    bad=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|skipKernelTC)\b',code)
                    if bad:raise RuntimeError(f'Forbidden declaration/proof escape in {m}: {bad}')
                    artifact=BUILD/(m.replace('.','/')+'.olean')
                    dep_hashes={d:records[d]['artifact_sha256'] for d in deps[m]}
                    prior=records.get(m,{})
                    if artifact.exists() and prior.get('source_sha256')==source_hash and prior.get('dependency_artifacts')==dep_hashes and prior.get('artifact_sha256')==sha(artifact):
                        pending.remove(m);completed.add(m)
                        continue
                    if len(running)>=args.jobs:continue
                    print(f'[{positions[m]}/{len(order)}] {m}',flush=True)
                    pending.remove(m)
                    future=pool.submit(compile_module,m,artifact)
                    running[future]=(m,source_hash,dep_hashes,artifact)

                if not running:
                    if pending:raise RuntimeError('No dependency-ready module: '+', '.join(pending))
                    break
                finished,_=wait(running,return_when=FIRST_COMPLETED)
                for future in sorted(finished,key=lambda item:positions[running[item][0]]):
                    m,source_hash,dep_hashes,artifact=running.pop(future)
                    current_module=m
                    returncode,temporary,log,seconds=future.result()
                    if returncode or not temporary.exists():
                        report['failure']={'module':m,'exit_code':returncode,'log':log.name}
                        print(log.read_text(),flush=True)
                        raise RuntimeError('Lean compilation failed: '+m)
                    if sha(path(m))!=source_hash:
                        raise RuntimeError('Source changed during compilation: '+m)
                    for d,digest in dep_hashes.items():
                        if records[d]['source_sha256']!=sha(path(d)):
                            raise RuntimeError('Dependency source changed during compilation: '+d)
                        if sha(BUILD/(d.replace('.','/')+'.olean'))!=digest:
                            raise RuntimeError('Dependency artifact changed during compilation: '+d)
                    temporary.replace(artifact)
                    records[m]={'source_sha256':source_hash,'artifact_sha256':sha(artifact),
                        'dependency_artifacts':dep_hashes,'seconds':seconds,'exit_code':0,'log':log.name}
                    completed.add(m);recompiled.add(m)
                    # Preserve deterministic topological order in the report,
                    # irrespective of process completion order.
                    report['recompiled_this_run']=[d for d in order if d in recompiled]
                    save('build-progress.json',report)
        except BaseException as error:
            for future in running:future.cancel()
            report.setdefault('failure',{'module':current_module,'error':str(error)})
            save('build-progress.json',report)
            raise
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
with (ROOT/'development/compiler.lock').open('a+') as compiler_lock:
    fcntl.flock(compiler_lock,fcntl.LOCK_EX)
    r=subprocess.run([str(LEAN),'-j1',str(audit.relative_to(ROOT))],cwd=ROOT,env=env,capture_output=True,text=True)
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
with (ROOT/'development/compiler.lock').open('a+') as compiler_lock:
    fcntl.flock(compiler_lock,fcntl.LOCK_EX)
    r=subprocess.run([str(LEAN),'-j1',str(route.relative_to(ROOT))],cwd=ROOT,env=env,capture_output=True,text=True)
output=r.stdout+r.stderr;(REPORT/'proof-routes.log').write_text(output)
route_passed=r.returncode==0 and 'PROOF_ROUTE_AUDIT_PASSED' in output
save('proof-routes.json',{'passed':route_passed,'lean_exit_code':r.returncode,'audit_source_sha256':sha(route),'fresh_build_sha256':sha(REPORT/'fresh-build.json'),'diagnostics_log':'proof-routes.log'})
if not route_passed:
    print(output[-6000:]);raise SystemExit('Exact-type/proof-route audit failed')
for m in order:
    if sha(path(m))!=report['source_inventory'][m]:raise RuntimeError('Sources changed during audits: '+m)
    if sha(BUILD/(m.replace('.','/')+'.olean'))!=records[m]['artifact_sha256']:
        raise RuntimeError('Local artifacts changed during audits: '+m)
if sha(ROOT/'Wong/MainStatement.lean')!=EXPECTED_MAIN_STATEMENT_SHA256:
    raise RuntimeError('Reviewed current statement changed during verification.')
for statement,digest in frozen_statements.items():
    if sha(ROOT/statement)!=digest:
        raise RuntimeError('Reviewed current/PDF proposition changed during verification: '+statement)
if json_fingerprint(check_environment())!=environment_fingerprint:
    raise RuntimeError('Pinned verification environment changed during compilation or audits.')
save('acceptance.json',{'passed':True,'checked_at_utc':datetime.now(timezone.utc).isoformat(),'source_module_count':len(order),'theorem_count':len(names),'sorry_count':0,'external_mathematical_axioms':[],'allowed_foundational_axioms':sorted(allowed),'main_statement_sha256':sha(ROOT/'Wong/MainStatement.lean'),'build_report_sha256':sha(REPORT/'fresh-build.json'),'axiom_report_sha256':sha(REPORT/'axioms.json'),'proof_route_report_sha256':sha(REPORT/'proof-routes.json'),'verification_script_sha256':sha(Path(__file__)),'source_inventory':report['source_inventory'],
    'environment_fingerprint':environment_fingerprint,'environment_report_sha256':sha(REPORT/'environment.json'),
    'verified_targets':['mainClaim','ShiYau2020MitterClaim','ShiYau2020QuadraticClaim','ShiYau2020WongQuadraticClaim','UnconditionalMainClaim'],
    'frozen_statements':frozen_statements,
    'third_party_cache_trust':environment['third_party_cache_trust']})
print('PASS: exact reviewed proposition, new Jacobi route, zero placeholders, and normal foundational axiom dependencies.',flush=True)
