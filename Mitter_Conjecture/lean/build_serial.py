#!/usr/bin/env python3
"""Rebuild the local import closure with one compiler and record its snapshot.

Failed elaborations never replace an accepted artifact.  The shared wrapper
also serializes this build against other campaign jobs on the 8 GB host.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import uuid
from verification_common import source_inventory, verification_scripts, write_report

root = Path(__file__).resolve().parent
sys.path.insert(0, str(root))
# Keep comment stripping local: importing audit_sources would run its audit.
def without_comments(text):
    output = []
    index = depth = 0
    while index < len(text):
        if text.startswith('/-', index):
            depth += 1
            index += 2
        elif depth and text.startswith('-/', index):
            depth -= 1
            index += 2
        elif depth:
            index += 1
        elif text.startswith('--', index):
            end = text.find('\n', index)
            index = len(text) if end < 0 else end
        else:
            output.append(text[index])
            index += 1
    return ''.join(output)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def local_path(module):
    path = root / (module.replace('.', '/') + '.lean')
    return path if path.is_file() else None

audit = root.parent / 'audit_unconditional_core_2026-09-18'
audit.mkdir(parents=True, exist_ok=True)
report_path = audit / 'fresh-build.json'
report = {
    'started_at_utc': datetime.now(timezone.utc).isoformat(),
    'build_id': str(uuid.uuid4()),
    'passed': False,
    'accepted_modules': [],
    'artifact_sha256': {},
}
def save():
    write_report(report_path, report)
save()

source_report_path = audit / 'fresh-sources.json'
source_report = json.loads(source_report_path.read_text())
if not source_report.get('passed') or not source_report.get('theorem_names'):
    raise SystemExit('A successful nonempty complete source audit is required first.')
if source_report['source_inventory_sha256'] != source_inventory() or \
        source_report['audit_script_sha256'] != digest(root / 'audit_sources.py'):
    raise SystemExit('Source audit does not match the current sources and script.')
report['fresh_sources_sha256'] = digest(source_report_path)
if not (root / 'Wong.lean').is_file():
    raise SystemExit('The public Wong.lean entry module is missing.')

order, visiting, visited = [], set(), set()
def visit(module):
    if module in visited:
        return
    if module in visiting:
        raise SystemExit(f'Local import cycle at {module}')
    path = local_path(module)
    if path is None:
        if module == 'Wong' or module.startswith('Wong.'):
            raise SystemExit(f'Missing local source dependency: {module}')
        return
    visiting.add(module)
    code = without_comments(path.read_text())
    for imports in re.findall(r'^\s*import\s+([^\n]+)', code, re.M):
        for dependency in imports.split():
            visit(dependency)
    visiting.remove(module)
    visited.add(module)
    order.append(module)

visit('Wong')
if not order or order[-1] != 'Wong':
    raise SystemExit('The local Wong import closure is empty or incomplete.')
snapshot = {module: digest(local_path(module)) for module in order}
report.update({
    'compiler_concurrency': 1,
    'entry_module': 'Wong',
    'source_sha256': snapshot,
    'build_order': order,
    'source_inventory_sha256': source_inventory(),
    'verification_scripts_sha256': verification_scripts(),
})
save()

for index, module in enumerate(order, start=1):
    path = local_path(module)
    if digest(path) != snapshot[module]:
        report['failure'] = f'Source changed before elaboration: {module}'
        save()
        raise SystemExit(report['failure'])
    target = root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    log_path = audit / ('fresh-' + module.replace('.', '-') + '.log')
    print(f'[{index}/{len(order)}] {module}', flush=True)
    with tempfile.TemporaryDirectory(prefix='wong-accepted-artifact-') as temporary:
        temporary_output = Path(temporary) / 'Checked.olean'
        with log_path.open('w') as log:
            result = subprocess.run([
                str(root / 'run-lean.sh'), '-o', str(temporary_output),
                str(path.relative_to(root)),
            ], cwd=root, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode or not temporary_output.is_file():
            report['failure'] = module
            report['lean_exit_code'] = result.returncode
            report['failure_log'] = str(log_path)
            save()
            print(log_path.read_text(), end='')
            raise SystemExit(result.returncode or 1)
        if digest(path) != snapshot[module]:
            report['failure'] = f'Source changed during elaboration: {module}'
            save()
            raise SystemExit(report['failure'])
        # Reading then atomically replacing works across different filesystems.
        staging = target.with_suffix('.accepted-olean')
        staging.write_bytes(temporary_output.read_bytes())
        staging.replace(target)
    report['accepted_modules'].append(module)
    report['artifact_sha256'][module] = digest(target)
    save()

changed = [module for module in order if digest(local_path(module)) != snapshot[module]]
if source_inventory() != report['source_inventory_sha256']:
    changed.append('complete source inventory or axiom manifest')
if verification_scripts() != report['verification_scripts_sha256']:
    changed.append('verification scripts')
if digest(source_report_path) != report['fresh_sources_sha256']:
    changed.append('complete source audit report')
for module, expected in report['artifact_sha256'].items():
    target = root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
    if digest(target) != expected:
        changed.append('accepted artifact ' + module)
report['finished_at_utc'] = datetime.now(timezone.utc).isoformat()
report['changed_sources'] = changed
report['passed'] = not changed
save()
if changed:
    raise SystemExit('Sources changed during the build: ' + ', '.join(changed))
print('PASS: the complete local import closure was rebuilt from the recorded snapshot.')
