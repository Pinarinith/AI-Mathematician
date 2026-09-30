#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 audit_sources.py
python3 build_serial.py
python3 audit_axioms.py
python3 verify_main.py
