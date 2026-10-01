#!/usr/bin/env python3
"""Convenience Lean invocation on the verified artifact path.

This is not an acceptance check; use check.sh for source, pin, and proof audits.
There is deliberately no fallback to the older .lake/build artifact directory.
"""
from pathlib import Path
import os, sys
root = Path(__file__).resolve().parent
vendor = Path(os.environ.get('WONG_VENDOR', '/Users/rinithpina/Documents/Research/Mitter_Conjecture/vendor'))
paths = [root/'.lake/verified/lib/lean', vendor/'mathlib4/.lake/build/lib/lean']
paths += sorted((vendor/'mathlib-deps').glob('*/.lake/build/lib/lean'))
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, paths))
compiler = Path(os.environ.get('WONG_LEAN', '/Users/rinithpina/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean'))
os.chdir(root)
os.execve(str(compiler), [str(compiler), *sys.argv[1:]], env)
