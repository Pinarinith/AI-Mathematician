#!/usr/bin/env python3
"""Require the frozen original mainClaim on the fully audited fresh snapshot."""
from pathlib import Path
from datetime import datetime, timezone
import json
import re
import subprocess
import sys
import tempfile
from verification_common import (ROOT, CAMPAIGN, digest, load_build,
                                 recheck_build, write_report)

report_path = CAMPAIGN / 'main-verification.json'
theorem = sys.argv[1] if len(sys.argv) > 1 else 'Wong.SmoothModel.main_theorem'
report = {
    'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'requested_type': 'Wong.SmoothModel.mainClaim',
    'candidate_declaration': theorem,
    'main_claim_proved': False,
    'proof_scope': 'not_verified',
}
# Invalidate any older success even when a prerequisite fails immediately.
write_report(report_path, report)
try:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", theorem):
        raise RuntimeError('Expected a fully qualified Lean declaration name.')
    frozen_hash = 'e9f51310ade6a4539e43c3074a1b35ed35e34bd85946761d53c93183d842a5cc'
    statement_hash = digest(ROOT / 'Wong/MainStatement.lean')
    report['original_statement_sha256'] = statement_hash
    if statement_hash != frozen_hash:
        raise RuntimeError('The frozen original MainStatement.lean has changed.')
    build, build_hash = load_build()
    axioms_path = CAMPAIGN / 'fresh-axioms.json'
    axiom_report_hash = digest(axioms_path)
    axiom_report = json.loads(axioms_path.read_text())
    if not axiom_report.get('passed') or axiom_report.get('build_id') != build['build_id'] \
            or axiom_report.get('fresh_build_sha256') != build_hash:
        raise RuntimeError('A complete axiom audit of this exact fresh build is required.')
    report.update({'build_id': build['build_id'], 'fresh_build_sha256': build_hash,
                   'fresh_axioms_sha256': axiom_report_hash})
    published = 'Wong.Published.shi_yau_affinity'
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    with tempfile.TemporaryDirectory(prefix='wong-main-verification-') as temporary:
        lean_file = Path(temporary) / 'Check.lean'
        stage = 'declaration_lookup'
        lean_file.write_text(f'import Wong\n#check {theorem}\n')
        result = subprocess.run([str(ROOT / 'run-lean.sh'), str(lean_file)],
                                cwd=ROOT, capture_output=True, text=True)
        if result.returncode == 0:
            stage = 'exact_type_and_axioms'
            lean_file.write_text('import Wong\n\n'
                f'theorem verifiedOriginalMainClaim : Wong.SmoothModel.mainClaim := {theorem}\n'
                '#print axioms verifiedOriginalMainClaim\n')
            result = subprocess.run([str(ROOT / 'run-lean.sh'), str(lean_file)],
                                    cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    print(output, end='')
    matches = re.findall(r"'verifiedOriginalMainClaim' depends on axioms:\s*\[([^]]*)\]", output, re.S)
    axioms = {a.strip() for match in matches for a in match.split(',') if a.strip()}
    no_axioms = "'verifiedOriginalMainClaim' does not depend on any axioms" in output
    recheck_build(build, build_hash)
    if digest(axioms_path) != axiom_report_hash:
        raise RuntimeError('Complete axiom audit report changed during the main check.')
    passed = result.returncode == 0 and bool(matches or no_axioms) and axioms <= allowed
    report.update({
        'last_check_stage': stage, 'lean_exit_code': result.returncode,
        'main_claim_proved': passed,
        'proof_scope': ('foundations_only' if passed else 'not_verified'),
        'published_input_used': published in axioms,
        'axioms': sorted(axioms), 'unexpected_axioms': sorted(axioms - allowed),
        'diagnostics': output,
    })
    if not passed:
        raise RuntimeError('No audited proof of the original mainClaim was verified.')
except Exception as error:
    report.update({'main_claim_proved': False, 'proof_scope': 'not_verified',
                   'failure': str(error)})
    write_report(report_path, report)
    raise SystemExit('FAIL: ' + str(error))
write_report(report_path, report)
print('PASS: the frozen original mainClaim is proved with foundations only on the audited fresh snapshot.')
