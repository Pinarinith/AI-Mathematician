from pathlib import Path
import re
from datetime import datetime, timezone
from verification_common import ROOT, CAMPAIGN, source_inventory, digest, write_report

report_path = CAMPAIGN / 'fresh-sources.json'
report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'passed': False}
write_report(report_path, report)

def strip_comments(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s.startswith('/-',i): depth+=1;i+=2
        elif depth and s.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif s.startswith('--',i):
            end=s.find('\n',i);i=len(s) if end<0 else end
        else:out.append(s[i]);i+=1
    return ''.join(out)

all_names=[]
declarations={}
for p in sorted((ROOT / 'Wong').glob('**/*.lean')):
    code=strip_comments(p.read_text())
    if re.search(r'\b(sorry|admit|unsafe|native_decide|implemented_by)\b',code):
        raise SystemExit(f'Forbidden proof escape in {p}')
    if re.search(r'\baxiom\b',code):
        raise SystemExit(f'Unconditional verification forbids external mathematical axioms: {p}')
    scopes=[]
    for line in code.splitlines():
        ns=re.match(r'\s*namespace\s+([\w.]+)',line)
        section=re.match(r'\s*(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$',line)
        end=re.match(r'\s*end(?:\s+([\w.]+))?\s*$',line)
        if ns:
            scopes.append(('namespace',ns.group(1)))
        elif section:
            scopes.append(('section',section.group(1)))
        elif end:
            if not scopes:
                raise SystemExit(f'Unmatched scope end in {p}: {line}')
            scopes.pop()
        else:
            namespace='.'.join(name for kind,name in scopes if kind=='namespace')
            for kind,name in re.findall(r'\b(def|abbrev|structure|inductive|theorem|lemma|axiom)\s+([\w.]+)',line):
                full_name=namespace+'.'+name if namespace else name
                if full_name in declarations:
                    raise SystemExit(f'Duplicate declaration {full_name}: {declarations[full_name]} and {p}')
                declarations[full_name]=str(p)
            for name in re.findall(r'\b(?:theorem|lemma)\s+([\w.]+)',line):
                all_names.append(namespace+'.'+name if namespace else name)
(ROOT / 'AxiomAudit.lean').write_text('import Wong\n\n'+''.join('#print axioms '+n+'\n' for n in all_names))
report.update({'passed': True, 'theorem_names': all_names,
               'theorem_count': len(all_names),
               'source_inventory_sha256': source_inventory(),
               'audit_script_sha256': digest(ROOT / 'audit_sources.py')})
write_report(report_path, report)
print(f'Source audit passed: {len(all_names)} theorem declarations; no proof escapes; '
      'no external mathematical axioms are permitted.')
