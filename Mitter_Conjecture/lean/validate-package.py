#!/usr/bin/env python3
"""Read-only final Shi--Yau package validator; never invokes Lean or verify.py.

Default: validate the completed clean-source certificate and, if present, the
package manifest. --manifest writes only PACKAGE_MANIFEST.json, atomically,
after every certificate/snapshot check has passed. No baseline is accepted.
The reviewed constants below deliberately make this a snapshot validator,
not a general verifier of arbitrary replacement Lean programs or statements.
Third-party compiled caches retain the verifier's disclosed trust boundary.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
import tarfile
import tempfile


_HERE = Path(__file__).resolve().parent
DEFAULT_PACKAGE = (_HERE.parent if _HERE.name == "01_lean_verification" else
                   _HERE if (_HERE / "01_lean_verification").is_dir() else
                   _HERE.parent / "outputs/wong_shiyau2020_2026-09-29")
MANIFEST_NAME = "PACKAGE_MANIFEST.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_COUNTS = (165, 1661)
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
EXPECTED_RELEASE = "4.35.0-rc2"
EXPECTED_COMMIT = "11acb17ec6b07a8f9e9173e6845197929540936b"
REVIEWED_HASHES = {
    "verify.py": "c6dce04be2ef42326d5716b3d5baf82a9643bc8151f9dea5649ba7b73259037c",
    "ProofRouteAudit.lean": "ed18a23ce93f2b506cb664da61308e76f74a04c57e174ec317944ed8138d81fa",
    "frozen-statements.json": "2db1c6c3b8daa3c8b6b4386f00ec93e50b59ad3904a39b8d6251e509d7b92054",
    "dependencies.json": "06c830c7b31cce6134431a0a8937f0bd8e2f9ceae3e11f81f9232f0d279b2bd1",
    "Wong/FunctionQuadraticRankConstraints.lean": "6fbc7e3ccc516f7a0ec8843360bf873e430d1d264d4f755f8349d4b905e164b3",
    "Wong/PolynomialSmooth.lean": "f42507202c76f4b225fc6263fb8bf3a3197546931bcb10e43e10578a98d6156a",
    "Wong/UnconditionalMainProof.lean": "2219437f3403ab716766ddfaf7014bd6898ddc116e60117a9d24181e29ae1c47",
}
FROZEN = {
    "Wong/MainStatement.lean": "e181c7235f8673ffc967f83ddf8e6299bdabbc79a43fd9cc21bd817168047970",
    "Wong/ShiYau2020ModelReduction.lean": "bcf8cb8811bddfd83f842f55808651993dc6576c92bb3ba7fd28f8ea3f30b42f",
    "Wong/ShiYau2020IntroductionStatement.lean": "e5f3523cc7333fae63835f4248acfdee34459f14fc5621bfee96cc139f2e6b4b",
}
TARGETS = {
    "ShiYau2020MitterClaim", "ShiYau2020QuadraticClaim",
    "ShiYau2020WongQuadraticClaim", "UnconditionalMainClaim", "mainClaim",
}
NS = "Wong.SmoothModel."
MAIN = NS + "main_theorem"
CONDITIONAL = NS + "quadraticFree_main_theorem"
QUADRATIC_FREE = NS + "quadraticFree_of_finiteDimensional_rank_two"
MITTER = NS + "shiYau2020_mitter_theorem"
INTEGRATED = NS + "unconditional_main_theorem"
VISIBLE = NS + "VisibleHeads.visible_slopes_zero"
NORMALIZED = NS + "VisibleHeads.normalized_slope_zero_by_jacobi"
JACOBI = "Wong.JacobiVisible.second_identity"
OBSOLETE = {
    NS + "VisibleHeads.head00", NS + "VisibleHeads.head11",
    NS + "VisibleHeads.head01", NS + "VisibleHeads.δ_δ_Y",
    "Wong.Visible.singleAxisElimination",
}
REQUIRED_ROUTES = {
    MITTER: {NS + "classification_model_functionElementsAffine", NS + "actual_quadratic_function_cases"},
    INTEGRATED: {MITTER, MAIN, JACOBI},
    MAIN: {MITTER, QUADRATIC_FREE, CONDITIONAL, JACOBI},
    CONDITIONAL: {JACOBI, NORMALIZED},
    QUADRATIC_FREE: {MITTER},
    VISIBLE: {JACOBI, NORMALIZED},
    NORMALIZED: {JACOBI, NORMALIZED},
}
FORBIDDEN_ROUTES = {
    MITTER: {MAIN, INTEGRATED, CONDITIONAL, QUADRATIC_FREE},
    INTEGRATED: set(), MAIN: set(),
    CONDITIONAL: OBSOLETE | {MITTER, MAIN, INTEGRATED},
    QUADRATIC_FREE: {MAIN, INTEGRATED, CONDITIONAL},
    VISIBLE: OBSOLETE, NORMALIZED: OBSOLETE,
}
TARGET_THEOREMS = {
    MAIN, MITTER, INTEGRATED, CONDITIONAL, QUADRATIC_FREE, NS + "shiYau2020_quadratic_theorem",
    NS + "shiYau2020_wong_quadratic_theorem", NS + "omega12_constant_without_quadraticFree",
}


class Invalid(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def integer_equal(value, expected):
    return type(value) is int and value == expected


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_json(data, label):
    try:
        value = json.loads(data, object_pairs_hook=unique_object)
    except (ValueError, UnicodeError) as exc:
        raise Invalid(f"Invalid JSON in {label}: {exc}") from exc
    require(isinstance(value, dict), f"JSON object required: {label}")
    return value


def relative_path(value):
    require(isinstance(value, str) and bool(value), "Missing relative file path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and ".." not in path.parts and str(path) == value,
            f"Noncanonical or unsafe relative path: {value}")
    return path


def signature(st):
    return st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns


def regular_hash(path):
    try:
        before = path.lstat()
        require(stat.S_ISREG(before.st_mode), f"Not a regular, non-symlink file: {path}")
        h = hashlib.sha256()
        with path.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                h.update(block)
        after = path.lstat()
    except OSError as exc:
        raise Invalid(f"Cannot read {path}: {exc}") from exc
    require(signature(before) == signature(after), f"File changed while hashing: {path}")
    return h.hexdigest()


class Snapshot:
    def __init__(self, root):
        self.root = root
        self.observed = {}

    def path(self, relative):
        rel = relative_path(relative)
        current = self.root
        for part in rel.parts:
            current = current / part
            require(not current.is_symlink(), f"Package symlink rejected: {current}")
        return current

    def hash(self, relative):
        path = self.path(relative)
        digest = regular_hash(path)
        if relative in self.observed:
            require(self.observed[relative] == digest, f"Snapshot changed: {relative}")
        self.observed[relative] = digest
        return digest

    def text(self, relative):
        digest = self.hash(relative)
        data = self.path(relative).read_bytes()
        require(hashlib.sha256(data).hexdigest() == digest, f"Snapshot changed during read: {relative}")
        return data.decode("utf-8")

    def json(self, relative):
        return parse_json(self.text(relative), relative)

    def bind(self, relative, expected):
        require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected),
                f"Missing/invalid digest for {relative}")
        require(self.hash(relative) == expected, f"Hash binding mismatch: {relative}")


def strip_comments(source):
    """Remove nested Lean comments, preserving newlines and quoted strings."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i): depth += 1; out.extend("  "); i += 2
            elif source.startswith("-/", i): depth -= 1; out.extend("  "); i += 2
            else: out.append("\n" if source[i] == "\n" else " "); i += 1
        elif quoted:
            out.append(source[i])
            if source[i] == "\\" and i + 1 < len(source):
                i += 1; out.append(source[i])
            elif source[i] == '"': quoted = False
            i += 1
        elif source.startswith("/-", i): depth = 1; out.extend("  "); i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            out.extend(" " * (end - i)); i = end
        else:
            quoted = source[i] == '"'
            out.append(source[i]); i += 1
    require(depth == 0 and not quoted, "Unterminated Lean comment or string")
    return "".join(out)


def source_closure(snapshot, prefix):
    order, dependencies, codes = [], {}, {}
    visited, active = set(), set()

    def visit(module):
        if module in visited: return
        require(module not in active, f"Local import cycle: {module}")
        require(module == "Wong" or module.startswith("Wong."), f"Unexpected local namespace: {module}")
        require(re.fullmatch(r"[A-Za-z0-9_.]+", module), f"Invalid module name: {module}")
        active.add(module)
        filename = prefix + module.replace(".", "/") + ".lean"
        code = strip_comments(snapshot.text(filename))
        require('"' not in code, f"Unexpected string/metaprogramming surface in mathematical module: {module}")
        bad = re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|skipKernelTC|run_cmd|run_tac|elab|macro|initialize|addDecl|private|opaque)\b", code)
        require(not bad, f"Forbidden/unaudited source construct in {module}: {bad}")
        imports = [name for line in re.findall(r"^\s*import\s+([^\n]+)", code, re.M) for name in line.split()]
        local = []
        for name in imports:
            if name == "Wong" or name.startswith("Wong."):
                local.append(name); visit(name)
            else:
                require(not snapshot.path(prefix + name.replace(".", "/") + ".lean").exists(),
                        f"Untracked non-Wong local import: {name}")
        dependencies[module] = local
        codes[module] = code
        active.remove(module); visited.add(module); order.append(module)

    visit("Wong")
    folder = snapshot.path(prefix + "Wong")
    all_sources = {"Wong"} | {
        "Wong." + str(p.relative_to(folder).with_suffix("")).replace(os.sep, ".")
        for p in folder.rglob("*.lean")
    }
    require(set(order) == all_sources, "Mathematical sources outside the actual Wong import closure")
    declarations = []
    for module in order:
        stack = []
        for line in codes[module].splitlines():
            ns = re.match(r"\s*namespace\s+([\w.]+)", line)
            section = re.match(r"\s*(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$", line)
            end = re.match(r"\s*end(?:\s+([\w.]+))?\s*$", line)
            if ns: stack.append(("ns", ns.group(1)))
            elif section: stack.append(("section", section.group(1)))
            elif end:
                require(bool(stack), f"Unmatched namespace/section end in {module}")
                stack.pop()
            else:
                namespace = ".".join(name for kind, name in stack if kind == "ns")
                for name in re.findall(r"\b(?:theorem|lemma)\s+([\w.']+)", line):
                    full = namespace + "." + name if namespace else name
                    require(full.startswith("Wong."), f"Untraversed theorem namespace: {full}")
                    declarations.append(full)
        # Lean closes remaining file-local sections at EOF (many modules use
        # an unclosed `noncomputable section`); the next module starts fresh.
    require(len(set(declarations)) == len(declarations), "Duplicate derived theorem/lemma name")
    require((len(order), len(declarations)) == EXPECTED_COUNTS,
            f"Reviewed snapshot counts changed: derived {len(order)}/{len(declarations)}, expected {EXPECTED_COUNTS}")
    return order, dependencies, declarations


def require_clean_log(text, label):
    require(not re.search(r"error:|sorryAx|uncaught exception|Segmentation fault|stack overflow", text, re.I),
            f"Failure marker in {label}")


def parse_axioms(output):
    found = {}
    for match in re.finditer(r"'(\S+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", output, re.S):
        name, block = match.groups()
        require(name not in found, f"Duplicate axiom output for {name}")
        values = sorted({x.strip() for x in (block or "").split(",") if x.strip()})
        require(set(values) <= ALLOWED, f"Non-foundational axiom in output for {name}: {values}")
        found[name] = values
    return found


def check_routes(output):
    require_clean_log(output, "proof-routes.log")
    require("PASS public mainClaim/main_theorem: finite-dimensional and rank-two only" in output,
            "Missing literal public main theorem type check")
    require("PASS derived QuadraticFree: finite-dimensional and rank-two only" in output,
            "Missing literal derived quadratic-freeness type check")
    require(output.count("PROOF_ROUTE_AUDIT_PASSED") == 1, "Missing/duplicate final proof-route marker")
    begins = re.findall(r"LOCAL_REACHABILITY_BEGIN root=(\S+) count=(\d+)", output)
    ends = re.findall(r"LOCAL_REACHABILITY_END root=(\S+)", output)
    require(len(begins) == len(REQUIRED_ROUTES) and {r for r, _ in begins} == set(REQUIRED_ROUTES),
            "Wrong proof-route roots")
    require(len(ends) == len(REQUIRED_ROUTES) and set(ends) == set(REQUIRED_ROUTES), "Missing route end markers")
    reached = {root: [] for root in REQUIRED_ROUTES}
    for root, declaration in re.findall(r"LOCAL_REACHABLE root=(\S+) declaration=(\S+)", output):
        require(root in reached and declaration.startswith("Wong."), "Unexpected route declaration/root")
        reached[root].append(declaration)
    for root, count in begins:
        values = reached[root]
        require(len(values) == len(set(values)) == int(count) and root in values, f"Malformed route closure for {root}")
        require(REQUIRED_ROUTES[root] <= set(values), f"Missing required proof route: {root}")
        require(not (FORBIDDEN_ROUTES[root] & set(values)), f"Forbidden/circular proof route: {root}")
        for name in REQUIRED_ROUTES[root]:
            require(f"PASS required route: {root} -> {name}" in output, f"Missing explicit route check: {root} -> {name}")
        for name in FORBIDDEN_ROUTES[root]:
            require(f"PASS forbidden route absent: {root} -/-> {name}" in output, f"Missing forbidden-route check: {root}")


def git_read(repo, *arguments):
    env = os.environ.copy(); env["GIT_OPTIONAL_LOCKS"] = "0"
    try:
        return subprocess.check_output(["git", "-c", "core.fsmonitor=false", "-C", str(repo), *arguments],
                                       env=env, text=True, stderr=subprocess.PIPE, timeout=60).strip()
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise Invalid(f"Read-only Git source-pin check failed for {repo}: {exc}") from exc


def check_git(repo, commit):
    require(git_read(repo, "rev-parse", "HEAD") == commit, f"Dependency commit changed: {repo}")
    require(not git_read(repo, "status", "--porcelain=v1", "--untracked-files=all"), f"Dirty pinned dependency: {repo}")
    return {"commit": commit, "dirty": False}


def check_environment(snapshot, prefix, report):
    require(report.get("passed") is True, "Environment report is not passed")
    environment = report.get("environment")
    require(isinstance(environment, dict), "Missing environment object")
    require(report.get("fingerprint") == fingerprint(environment), "Environment fingerprint is not canonical")
    snapshot.bind(prefix + "dependencies.json", environment.get("dependencies_file_sha256"))
    snapshot.bind(prefix + "lean-toolchain", environment.get("lean_toolchain_sha256"))
    pins = snapshot.json(prefix + "dependencies.json")
    require(pins.get("lean") == EXPECTED_TOOLCHAIN and snapshot.text(prefix + "lean-toolchain").strip() == EXPECTED_TOOLCHAIN,
            "Wrong pinned Lean toolchain")
    pattern = rf"Lean \(version {re.escape(EXPECTED_RELEASE)}, [^,]+, commit {EXPECTED_COMMIT}, Release\)"
    require(re.fullmatch(pattern, environment.get("compiler", "")), "Wrong Lean release/commit/build type")
    compiler = Path(environment.get("compiler_path", ""))
    require(compiler.is_absolute() and regular_hash(compiler) == environment.get("compiler_binary_sha256"), "Compiler binary changed")
    vendor = Path(environment.get("vendor_path", ""))
    require(vendor.is_absolute(), "Missing absolute vendor path")
    mathlib = vendor / "mathlib4"
    git_state = check_git(mathlib, pins["repositories"]["mathlib4"]["commit"])
    manifest_path = mathlib / "lake-manifest.json"
    require(regular_hash(manifest_path) == pins["mathlib_manifest_sha256"], "Mathlib dependency manifest changed")
    require(environment.get("mathlib") == {**git_state, "manifest_sha256": pins["mathlib_manifest_sha256"]}, "Mathlib environment binding differs")
    manifest = parse_json(manifest_path.read_text(), manifest_path)
    manifests = {p["name"]: p for p in manifest["packages"]}
    require(len(manifests) == len(manifest["packages"]), "Duplicate dependency manifest name")
    live = {}
    for name, pin in sorted(pins["manifest_dependency_pins"].items()):
        require(manifests.get(name, {}).get("rev") == pin["rev"] and manifests[name].get("url") == pin["url"], f"Manifest pin mismatch: {name}")
        installed = vendor / "mathlib-deps" / name
        require(installed.is_dir(), f"Missing dependency source directory: {name}")
        if (installed / ".git").exists():
            live[name] = {"mode": "clean_git_source_pin", **check_git(installed, pin["rev"])}
            continue
        archive = vendor / "mathlib-deps" / (name + ".tar.gz")
        require(regular_hash(archive) == pin["archive_sha256"], f"Dependency archive changed: {name}")
        entries, lean_files, seen, top = [], set(), set(), None
        with tarfile.open(archive, "r:gz") as stream:
            for member in stream.getmembers():
                parts = PurePosixPath(member.name).parts
                require(parts and parts[0] != "/" and ".." not in parts, f"Unsafe archive member: {member.name}")
                top = parts[0] if top is None else top
                require(parts[0] == top, f"Multiple dependency archive roots: {name}")
                if len(parts) == 1 or member.isdir(): continue
                relative = PurePosixPath(*parts[1:]); key = str(relative)
                require(key not in seen, f"Duplicate dependency archive file: {name}/{key}")
                seen.add(key); target = installed.joinpath(*relative.parts)
                if member.issym():
                    require(target.is_symlink() and os.readlink(target) == member.linkname, f"Dependency symlink changed: {target}")
                    require(target.resolve().is_relative_to(installed.resolve()), f"Dependency symlink escapes source tree: {target}")
                    entries.append([key, "symlink:" + member.linkname])
                else:
                    require(member.isfile(), f"Unsupported dependency archive entry: {name}/{key}")
                    reader = stream.extractfile(member)
                    require(reader is not None, f"Unreadable archive entry: {name}/{key}")
                    digest = hashlib.sha256(reader.read()).hexdigest()
                    require(regular_hash(target) == digest, f"Installed dependency source changed: {target}")
                    entries.append([key, digest])
                if relative.suffix == ".lean": lean_files.add(key)
        installed_lean = {str(p.relative_to(installed)) for p in installed.rglob("*.lean")
                          if not any(x in {".lake", ".git"} for x in p.relative_to(installed).parts)}
        require(installed_lean == lean_files, f"Extra/missing Lean dependency source: {name}")
        live[name] = {"mode": "archive_and_installed_sources", "revision": pin["rev"],
                      "archive_sha256": pin["archive_sha256"], "verified_file_count": len(entries),
                      "installed_source_inventory_sha256": fingerprint(sorted(entries))}
    require(environment.get("dependencies") == live, "Live dependency sources differ from the bound environment")
    trust = environment.get("third_party_cache_trust", "")
    require("not rebuilt or exhaustively hashed" in trust, "Third-party cache trust boundary missing")
    return environment


def full_inventory(root):
    result = {}
    for base, directories, files in os.walk(root, followlinks=False):
        for name in directories:
            require(not (Path(base) / name).is_symlink(), f"Directory symlink rejected: {Path(base)/name}")
        for name in files:
            path = Path(base) / name
            require(not path.is_symlink(), f"File symlink rejected: {path}")
            relative = path.relative_to(root).as_posix()
            if relative == MANIFEST_NAME: continue
            digest = regular_hash(path)
            result[relative] = {"sha256": digest, "size": path.stat().st_size}
    return dict(sorted(result.items()))


def validate(root, generate_manifest=False):
    require(root.is_dir() and not root.is_symlink(), f"Invalid package directory: {root}")
    snapshot = Snapshot(root)
    p = "01_lean_verification/"
    v = p + "verification/"
    acceptance = snapshot.json(v + "acceptance.json")
    require(acceptance.get("passed") is True, f"Acceptance is pending or failed: {acceptance.get('status', 'no passed certificate')}")
    require("status" not in acceptance or acceptance["status"] not in {"verification_in_progress", "pending"}, "Contradictory pending acceptance")
    bindings = {"fresh-build.json": "build_report_sha256", "axioms.json": "axiom_report_sha256",
                "proof-routes.json": "proof_route_report_sha256", "environment.json": "environment_report_sha256"}
    for filename, key in bindings.items(): snapshot.bind(v + filename, acceptance.get(key))
    snapshot.bind(p + "verify.py", acceptance.get("verification_script_sha256"))
    for filename, digest in {**REVIEWED_HASHES, **FROZEN}.items(): snapshot.bind(p + filename, digest)
    frozen = snapshot.json(p + "frozen-statements.json")
    require(frozen == FROZEN == acceptance.get("frozen_statements"), "Frozen proposition mapping differs from reviewed originals")
    require(acceptance.get("main_statement_sha256") == FROZEN["Wong/MainStatement.lean"], "Original main statement binding differs")
    require(integer_equal(acceptance.get("sorry_count"), 0) and acceptance.get("external_mathematical_axioms") == [], "Placeholder/external mathematical axiom reported")
    require(acceptance.get("allowed_foundational_axioms") == sorted(ALLOWED), "Wrong accepted foundational axiom set")
    require(isinstance(acceptance.get("verified_targets"), list) and len(acceptance["verified_targets"]) == len(TARGETS)
            and set(acceptance["verified_targets"]) == TARGETS, "Missing/extra 2020 or unconditional target")

    order, dependencies, names = source_closure(snapshot, p)
    build = snapshot.json(v + "fresh-build.json")
    require(build.get("passed") is True and build.get("prepare_only") is False and build.get("skipped") == [], "Incomplete/preparation-only build")
    require(build.get("verification_mode") == "full_source_rebuild", "Not an uninterrupted clean-source rebuild")
    require(build.get("historical_baseline") is None and build.get("environment_migration") is None, "Historical baseline/environment migration is forbidden")
    require(build.get("order") == order and build.get("recompiled_this_run") == order, "Clean campaign did not freshly compile the entire current closure")
    require(build.get("local_module_count") == acceptance.get("source_module_count") == len(order), "Module counts disagree")
    records = build.get("modules", {})
    require(set(records) == set(order), "Build record set differs from actual source closure")
    source_hashes = {m: snapshot.hash(p + m.replace(".", "/") + ".lean") for m in order}
    require(build.get("source_inventory") == acceptance.get("source_inventory") == source_hashes, "Source inventories disagree")
    artifact_prefix = p + ".lake/verified/lib/lean/"
    expected_artifacts = {artifact_prefix + m.replace(".", "/") + ".olean" for m in order}
    for module in order:
        record = records[module]
        require(integer_equal(record.get("exit_code"), 0) and "origin" not in record and "historical_build_id" not in record,
                f"Non-fresh/unsuccessful module record: {module}")
        require(record.get("source_sha256") == source_hashes[module], f"Module source hash differs: {module}")
        snapshot.bind(artifact_prefix + module.replace(".", "/") + ".olean", record.get("artifact_sha256"))
        expected_deps = {d: records[d]["artifact_sha256"] for d in dependencies[module]}
        require(record.get("dependency_artifacts") == expected_deps, f"Direct dependency artifact bindings differ: {module}")
        log = module.replace(".", "-") + ".log"
        require(record.get("log") == log, f"Unexpected compile log path: {module}")
        require_clean_log(snapshot.text(v + log), log)
    actual_artifacts = {str(f.relative_to(root)).replace(os.sep, "/")
                        for f in snapshot.path(artifact_prefix.rstrip("/")).rglob("*") if f.is_file() or f.is_symlink()}
    require(actual_artifacts == expected_artifacts, "Unrecorded/missing files on the verified local import path")
    require(snapshot.json(v + "build-progress.json") == build, "Final progress and successful build snapshots differ")

    axioms = snapshot.json(v + "axioms.json")
    routes = snapshot.json(v + "proof-routes.json")
    for label, report in [("axioms", axioms), ("proof routes", routes)]:
        require(report.get("passed") is True, f"Incomplete {label} audit")
        require(report.get("fresh_build_sha256") == snapshot.hash(v + "fresh-build.json"), f"Stale {label} build binding")
    require(axioms.get("theorem_count") == acceptance.get("theorem_count") == len(names), "Theorem/lemma counts disagree")
    require(axioms.get("allowed_axioms") == sorted(ALLOWED), "Wrong axiom audit allowance")
    declarations = axioms.get("declarations", {})
    require(set(declarations) == set(names) and TARGET_THEOREMS <= set(declarations), "Axiom audit omits declarations/targets")
    for name, values in declarations.items():
        require(isinstance(values, list) and values == sorted(set(values)) and set(values) <= ALLOWED, f"Invalid/non-foundational axiom list: {name}")
    audit = "import Wong\n\n" + "".join("#print axioms " + name + "\n" for name in names)
    require(snapshot.text(p + "AxiomAudit.lean") == audit, "Axiom audit source does not enumerate exactly the derived declarations")
    snapshot.bind(p + "AxiomAudit.lean", axioms.get("audit_source_sha256"))
    output = snapshot.text(v + "axioms.log")
    require_clean_log(output, "axioms.log")
    require(parse_axioms(output) == declarations, "Axiom log and bound declaration audit disagree")
    require(integer_equal(routes.get("lean_exit_code"), 0) and routes.get("diagnostics_log") == "proof-routes.log", "Invalid proof-route completion")
    snapshot.bind(p + "ProofRouteAudit.lean", routes.get("audit_source_sha256"))
    check_routes(snapshot.text(v + "proof-routes.log"))

    environment_report = snapshot.json(v + "environment.json")
    environment = check_environment(snapshot, p, environment_report)
    require(build.get("compiler") == environment["compiler"], "Build compiler differs from environment")
    require(build.get("environment_report_sha256") == acceptance["environment_report_sha256"], "Build environment report binding differs")
    require(build.get("environment_fingerprint") == acceptance.get("environment_fingerprint") == environment_report["fingerprint"], "Environment fingerprints disagree")
    require(acceptance.get("third_party_cache_trust") == environment["third_party_cache_trust"], "Cache trust disclosure differs")
    start = datetime.fromisoformat(build["started_utc"])
    finish = datetime.fromisoformat(build["finished_utc"])
    accepted = datetime.fromisoformat(acceptance["checked_at_utc"])
    require(start.tzinfo and finish.tzinfo and accepted.tzinfo and start <= finish <= accepted, "Invalid build/acceptance chronology")
    require(start.date().isoformat() >= "2026-09-29", "Historical campaign substituted for this clean build")

    inventory = full_inventory(root)
    for relative, digest in snapshot.observed.items():
        require(inventory.get(relative, {}).get("sha256") == digest, f"Package changed during validation: {relative}")
    require(expected_artifacts <= set(inventory), "Verified Lean artifacts absent from full inventory")
    manifest_path = root / MANIFEST_NAME
    require(not manifest_path.is_symlink(), "Manifest target is a symlink")
    validator_hash = regular_hash(Path(__file__).resolve())
    summary = {"source_module_count": len(order), "theorem_count": len(names),
               "acceptance_sha256": snapshot.observed[v + "acceptance.json"],
               "environment_fingerprint": environment_report["fingerprint"],
               "verification_mode": "full_source_rebuild", "verified_targets": sorted(TARGETS)}
    existing_manifest_hash = None
    if manifest_path.exists() and not generate_manifest:
        existing_manifest_hash = regular_hash(manifest_path)
        manifest = parse_json(manifest_path.read_text(), manifest_path)
        require(manifest.get("schema") == "shiyau2020-package-manifest-v1", "Unknown package manifest schema")
        require(manifest.get("excludes") == [MANIFEST_NAME], "Unexpected manifest exclusion")
        require(manifest.get("validator_sha256") == validator_hash, "Manifest was made by a different validator snapshot")
        require(manifest.get("validation") == summary, "Manifest certificate summary differs")
        require(manifest.get("third_party_cache_trust") == environment["third_party_cache_trust"], "Manifest cache trust disclosure differs")
        require(manifest.get("files") == inventory and manifest.get("file_count") == len(inventory), "Package manifest inventory differs")
        require(manifest.get("inventory_sha256") == fingerprint(inventory), "Manifest inventory fingerprint differs")
    require(full_inventory(root) == inventory, "Package changed during final inventory pass")
    if existing_manifest_hash is not None:
        require(regular_hash(manifest_path) == existing_manifest_hash, "Manifest changed during validation")
    if generate_manifest:
        payload = {"schema": "shiyau2020-package-manifest-v1", "created_at_utc": datetime.now(timezone.utc).isoformat(),
                   "validator_sha256": validator_hash, "validation": summary,
                   "excludes": [MANIFEST_NAME], "file_count": len(inventory),
                   "inventory_sha256": fingerprint(inventory), "files": inventory,
                   "scope": "All regular package files, including .lake/verified; manifest excludes itself. No file or directory symlinks.",
                   "third_party_cache_trust": environment["third_party_cache_trust"]}
        temp_name = None
        try:
            with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=root, prefix=".PACKAGE_MANIFEST.", suffix=".tmp", delete=False) as stream:
                temp_name = stream.name
                json.dump(payload, stream, ensure_ascii=False, indent=2); stream.write("\n")
                stream.flush(); os.fsync(stream.fileno())
            os.replace(temp_name, manifest_path)
        finally:
            if temp_name and os.path.exists(temp_name): os.unlink(temp_name)
    return {"passed": True, **summary, "package_file_count": len(inventory),
            "manifest": "written" if generate_manifest else ("validated" if manifest_path.exists() else "absent; read-only validation only")}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", nargs="?", type=Path, default=DEFAULT_PACKAGE, help="Package root R (contains 01_lean_verification)")
    parser.add_argument("--manifest", action="store_true", help="After all checks pass, atomically generate R/PACKAGE_MANIFEST.json")
    args = parser.parse_args(argv)
    try:
        # absolute() preserves symlink components for the explicit rejection.
        root = args.package.expanduser().absolute()
        for parent in (root, *root.parents):
            require(not parent.is_symlink(), f"Package root traverses a symlink: {parent}")
        print(json.dumps(validate(root, args.manifest), ensure_ascii=False, indent=2))
        return 0
    except (Invalid, OSError, KeyError, TypeError, ValueError, tarfile.TarError) as exc:
        print(json.dumps({"passed": False, "error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
