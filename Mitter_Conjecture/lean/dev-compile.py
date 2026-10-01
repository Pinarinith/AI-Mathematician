#!/usr/bin/env python3
"""Serial development compilation; these artifacts are NOT final certificates."""
from pathlib import Path
import os,sys,fcntl,subprocess,time,hashlib,json
ROOT=Path(__file__).resolve().parent
module=sys.argv[1]
assert module in {'Wong','ProofRouteAudit','AxiomAudit'} or module.startswith('Wong.')
source=ROOT/(module.replace('.','/')+'.lean')
build=ROOT/'.lake/development/lib/lean'
vendor=Path('/Users/rinithpina/Documents/Research/Mitter_Conjecture/vendor')
compiler=Path('/Users/rinithpina/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean')
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[build,vendor/'mathlib4/.lake/build/lib/lean',*sorted((vendor/'mathlib-deps').glob('*/.lake/build/lib/lean'))]))
print('QUEUED '+module,flush=True)
with (ROOT/'development/compiler.lock').open('a+') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX)
    stamp=time.strftime('%Y%m%dT%H%M%S')
    log=ROOT/'development'/(module.replace('.','-')+'-'+stamp+'.log')
    artifact=build/(module.replace('.','/')+'.olean')
    artifact.parent.mkdir(parents=True,exist_ok=True)
    pending=artifact.with_suffix('.pending.olean')
    digest=hashlib.sha256(source.read_bytes()).hexdigest()
    print('START '+module+' '+str(log),flush=True)
    started=time.monotonic()
    with log.open('w') as out:
        p=subprocess.run([str(compiler),'-j1','-o',str(pending),str(source.relative_to(ROOT))],cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
    changed=hashlib.sha256(source.read_bytes()).hexdigest()!=digest
    passed=p.returncode==0 and not changed and pending.exists()
    record={'module':module,'passed':passed,'exit_code':p.returncode,'source_changed':changed,'source_sha256':digest,'seconds':round(time.monotonic()-started,3),'log':str(log.relative_to(ROOT)),'status':'development_only_not_certified'}
    if passed:
        pending.replace(artifact)
        record['artifact_sha256']=hashlib.sha256(artifact.read_bytes()).hexdigest()
    log.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record),flush=True)
    if not passed:
        lines=log.read_text().splitlines()
        print('\n'.join(lines[:75]),flush=True)
        if len(lines)>75:print('... read full diagnostics in '+str(log),flush=True)
    sys.exit(0 if passed else (p.returncode or 1))
