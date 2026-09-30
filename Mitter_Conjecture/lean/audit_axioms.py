#!/usr/bin/env python3
"""Audit every listed theorem against the accepted fresh build snapshot."""
from datetime import datetime, timezone
import json
import re
import subprocess
from verification_common import ROOT, CAMPAIGN, load_build, recheck_build, write_report

report_path = CAMPAIGN / 'fresh-axioms.json'
report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'passed': False}
write_report(report_path, report)
try:
    build, build_hash = load_build()
    report.update({'build_id': build['build_id'], 'fresh_build_sha256': build_hash,
                   'axiom_manifest_sha256': build['source_inventory_sha256']['AxiomAudit.lean']})
    requested = re.findall(r'^#print axioms (\S+)\s*$',
                           (ROOT / 'AxiomAudit.lean').read_text(), re.M)
    if not requested or len(requested) != len(set(requested)):
        raise RuntimeError('Axiom manifest is empty or contains duplicate declarations.')
    complete_sources = json.loads((CAMPAIGN / 'fresh-sources.json').read_text())
    if requested != complete_sources['theorem_names']:
        raise RuntimeError('Axiom manifest is not the complete source-audited theorem list.')
    result = subprocess.run([str(ROOT / 'run-lean.sh'), 'AxiomAudit.lean'],
                            cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    (CAMPAIGN / 'fresh-axioms.log').write_text(output)
    print(output, end='')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    audited = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S):
        if name in audited:
            raise RuntimeError('Duplicate axiom output: ' + name)
        audited[name] = {a.strip() for a in axioms.split(',') if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        if name in audited:
            raise RuntimeError('Duplicate axiom output: ' + name)
        audited[name] = set()
    unexpected = {name: sorted(axioms - allowed) for name, axioms in audited.items()
                  if axioms - allowed}
    missing = sorted(set(requested) - set(audited))
    extra = sorted(set(audited) - set(requested))
    # Both source and artifact snapshots must also survive the compiler run.
    recheck_build(build, build_hash)
    report.update({
        'lean_exit_code': result.returncode,
        'requested_theorem_count': len(requested),
        'audited_theorem_count': len(audited),
        'allowed_axioms': sorted(allowed),
        'unexpected_axioms': unexpected,
        'missing_declarations': missing,
        'extra_declarations': extra,
        'theorem_axioms': {name: sorted(axioms) for name, axioms in audited.items()},
        'passed': result.returncode == 0 and not unexpected and not missing and not extra,
    })
    if not report['passed']:
        raise RuntimeError('Complete permitted-dependency axiom audit did not pass.')
except Exception as error:
    report.update({'passed': False, 'failure': str(error)})
    write_report(report_path, report)
    raise SystemExit('FAIL: ' + str(error))
write_report(report_path, report)
print(f"PASS: {len(audited)} theorems audited with the recorded permitted dependencies.")
