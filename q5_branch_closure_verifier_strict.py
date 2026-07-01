#!/usr/bin/env python3
"""Strict Q5 branch closure checker.

Runs the strengthened Q5 verifier and then prints a compact closure summary.
"""
from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path
from typing import List

STRICT_VERIFIER = Path(__file__).with_name("cert_verifier_q5_strict.py")


def load_strict_verifier():
    spec = importlib.util.spec_from_file_location("q5_strict_verifier", STRICT_VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load strict verifier from {STRICT_VERIFIER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main(argv: List[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="+", type=Path, help="JSONL certificate files")
    args = parser.parse_args(argv)
    verifier = load_strict_verifier()
    try:
        total, messages = verifier.run_verification(args.certificates, verbose=False)
    except Exception as exc:
        print(f"strict q=5 branch closure check failed: {exc}", file=sys.stderr)
        return 1

    for message in messages:
        print(message)
    if "strict q=5 closure dependencies ok" not in messages:
        print("strict q=5 branch closure check failed: full closure dependencies were not all present", file=sys.stderr)
        return 1
    print("Q5E2 closed")
    print("Q5E1 closed")
    print("Q5N closed")
    print("q=5 branch inventory exhausted")
    print(f"verified {total} certificate record(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
