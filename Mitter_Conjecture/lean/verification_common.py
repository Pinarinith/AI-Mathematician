"""Snapshot checks shared by the final build and both verification gates."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
CAMPAIGN = ROOT.parent / 'audit_unconditional_core_2026-09-18'
CAMPAIGN.mkdir(parents=True, exist_ok=True)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_report(path, report):
    path = Path(path)
    temporary = path.with_name(path.name + '.pending')
    temporary.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    temporary.replace(path)


def source_inventory():
    return {str(p.relative_to(ROOT)): digest(p)
            for p in sorted([ROOT / 'Wong.lean', ROOT / 'AxiomAudit.lean',
                             *ROOT.glob('Wong/**/*.lean')])}


def verification_scripts():
    return {name: digest(ROOT / name) for name in (
        'verification_common.py', 'audit_sources.py', 'build_serial.py',
        'audit_axioms.py', 'verify_main.py', 'check.sh', 'run-lean.sh',
        'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
            if (ROOT / name).is_file()}


def validate_build(build):
    if not build.get('passed'):
        raise RuntimeError('A successful fresh serial source build is required first.')
    if not build.get('build_id') or not build.get('artifact_sha256'):
        raise RuntimeError('Fresh build lacks a bound artifact snapshot.')
    if build['accepted_modules'] != build['build_order']:
        raise RuntimeError('Fresh build did not accept its complete import closure.')
    if source_inventory() != build['source_inventory_sha256']:
        raise RuntimeError('Lean sources or axiom manifest changed after the fresh build.')
    if verification_scripts() != build['verification_scripts_sha256']:
        raise RuntimeError('Verification scripts changed after the fresh build.')
    source_report_path = CAMPAIGN / 'fresh-sources.json'
    if digest(source_report_path) != build['fresh_sources_sha256']:
        raise RuntimeError('Complete source audit changed after the fresh build.')
    source_report = json.loads(source_report_path.read_text())
    if not source_report.get('passed') or not source_report.get('theorem_names'):
        raise RuntimeError('Complete source audit is unsuccessful or empty.')
    if source_report['source_inventory_sha256'] != build['source_inventory_sha256']:
        raise RuntimeError('Source audit and build describe different source snapshots.')
    for module, expected in build['source_sha256'].items():
        source = ROOT / (module.replace('.', '/') + '.lean')
        if digest(source) != expected:
            raise RuntimeError(f'Source changed after fresh build: {module}')
    if set(build['artifact_sha256']) != set(build['build_order']):
        raise RuntimeError('Fresh build artifact list does not match its import closure.')
    for module, expected in build['artifact_sha256'].items():
        artifact = ROOT / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
        if digest(artifact) != expected:
            raise RuntimeError(f'Accepted artifact changed after fresh build: {module}')


def load_build():
    path = CAMPAIGN / 'fresh-build.json'
    build_hash = digest(path)
    build = json.loads(path.read_text())
    validate_build(build)
    return build, build_hash


def recheck_build(build, build_hash):
    if digest(CAMPAIGN / 'fresh-build.json') != build_hash:
        raise RuntimeError('Fresh build report changed during verification.')
    validate_build(build)
