#!/usr/bin/env python3
"""Import only a hash-verified, previously fully rebuilt local baseline."""
from pathlib import Path
import hashlib,json,re,shutil
ROOT=Path(__file__).resolve().parent
BASE=Path('/Users/rinithpina/Documents/Research/Mitter_Conjecture')
SOURCE=BASE/'lean_wong_main_verified_2026-09-18'
AUDIT=BASE/'audit_unconditional_core_2026-09-18'
DEST=ROOT/'.lake/verified/lib/lean'
REPORT=ROOT/'verification'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
b=json.loads((AUDIT/'fresh-build.json').read_text())
a=json.loads((AUDIT/'fresh-axioms.json').read_text())
m=json.loads((AUDIT/'main-verification.json').read_text())
s=json.loads((AUDIT/'fresh-sources.json').read_text())
assert b['passed'] and a['passed'] and m['main_claim_proved'] and s['passed']
assert b['accepted_modules']==b['build_order']
assert a['fresh_build_sha256']==sha(AUDIT/'fresh-build.json')
assert m['fresh_build_sha256']==sha(AUDIT/'fresh-build.json')
assert m['fresh_axioms_sha256']==sha(AUDIT/'fresh-axioms.json')
assert b['fresh_sources_sha256']==sha(AUDIT/'fresh-sources.json')
assert set(a['allowed_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert not a['unexpected_axioms'] and not a['missing_declarations']
records={};changed=[]
for module in b['build_order']:
    rel=Path(module.replace('.','/')+'.lean')
    artifact=Path(module.replace('.','/')+'.olean')
    original=SOURCE/rel
    compiled=SOURCE/'.lake/build/lib/lean'/artifact
    assert sha(original)==b['source_sha256'][module],module+' source mismatch'
    assert sha(compiled)==b['artifact_sha256'][module],module+' artifact mismatch'
    if not (ROOT/rel).exists() or sha(ROOT/rel)!=sha(original):changed.append(module)
    target=DEST/artifact;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(compiled,target)
    deps=[d for line in re.findall(r'^import\s+([^\n]+)',original.read_text(),re.M) for d in line.split() if d in b['artifact_sha256']]
    records[module]={'source_sha256':sha(original),'artifact_sha256':sha(compiled),'dependency_artifacts':{d:b['artifact_sha256'][d] for d in deps},'origin':'hash_verified_historical_full_build','historical_build_id':b['build_id']}
REPORT.mkdir(exist_ok=True)
history=REPORT/'baseline';history.mkdir(exist_ok=True)
for name in ['fresh-build.json','fresh-axioms.json','fresh-sources.json','main-verification.json']:
    shutil.copy2(AUDIT/name,history/name)
baseline={'source_root':str(SOURCE),'audit_root':str(AUDIT),'build_id':b['build_id'],'build_report_sha256':sha(AUDIT/'fresh-build.json'),'verified_modules':len(records),'changed_modules_requiring_recompile':changed,'all_historical_sources_and_artifacts_match':True}
(REPORT/'baseline-validation.json').write_text(json.dumps(baseline,indent=2)+'\n')
(REPORT/'build-progress.json').write_text(json.dumps({'passed':False,'historical_baseline':baseline,'modules':records},indent=2)+'\n')
print(f'Validated {len(records)} complete historical source/artifact pairs; changed local sources: {changed}. Final rebuild and audits still required.')
