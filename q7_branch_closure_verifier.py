#!/usr/bin/env python3
"""Master wrapper for the current q=7 branch closure bundle.

The wrapper verifies four layers:
  1. the base q=7 archive and six-child coverage split,
  2. the six strict forced-or-pure frontier closure records,
  3. the explicit q7_branch_coverage_manifest record,
  4. the final branch-exhaustion conclusion.

It intentionally rejects the older weak parametric_q7_tail_closure record type.
"""
from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any, Dict, List

import cert_verifier_q7_strict as strict

EXPECTED_CHILDREN = ['q7_n1','q7_n3','q7_e1','q7_e2','q7_e3','q7_e6']
EXPECTED_FORCED_LEAVES = ['q7_n1_forced','q7_n3_forced','q7_e1_forced','q7_e2_forced','q7_e3_forced','q7_e6_forced']
EXPECTED_STRICT_RECORDS = ['q7_strict_tail_n1','q7_strict_tail_n3','q7_strict_tail_e1','q7_strict_tail_e2','q7_strict_tail_e3','q7_strict_tail_e6']

class WrapperError(Exception):
    pass

def verify_manifest(ids: Dict[str, Dict[str, Any]]) -> None:
    rec = ids.get('q7_current_branch_coverage_manifest')
    if rec is None:
        raise WrapperError('missing q7_current_branch_coverage_manifest')
    if rec.get('type') != 'q7_branch_coverage_manifest':
        raise WrapperError('coverage manifest has wrong type')
    checks = {
        'branch': 'q=7',
        'base_archive': 'q7_archive',
        'coverage_split': 'q7_split_root',
        'expected_children': EXPECTED_CHILDREN,
        'expected_forced_leaves': EXPECTED_FORCED_LEAVES,
        'strict_closure_records': EXPECTED_STRICT_RECORDS,
        'complete': True,
        'conclusion': 'q7_branch_inventory_exhausted_in_current_formal_certificate_system',
    }
    for key, expected in checks.items():
        if rec.get(key) != expected:
            raise WrapperError(f'manifest field {key} mismatch: expected {expected!r}, got {rec.get(key)!r}')
    for rid in ['q7_archive','q7_split_root'] + EXPECTED_STRICT_RECORDS:
        if rid not in ids:
            raise WrapperError(f'manifest references missing record {rid}')

def main(argv: List[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('bundle', type=Path)
    ap.add_argument('--verbose', action='store_true')
    args = ap.parse_args(argv)
    try:
        records = strict.load_records([args.bundle])
        ids = strict.by_id(records)
        strict.verify_base_archive(records)
        count = strict.verify_strict_frontier(records, verbose=args.verbose)
        verify_manifest(ids)
        print('Q7 coverage split complete')
        print(f'Q7 forced/pure frontier closures verified: {count}/6')
        print('q=7 branch inventory exhausted')
        print(f'verified {len(records)} certificate record(s)')
    except (strict.VerifyError, WrapperError) as exc:
        print(f'verification failed: {exc}', file=__import__('sys').stderr)
        return 1
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
