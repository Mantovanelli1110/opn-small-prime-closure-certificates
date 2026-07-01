#!/usr/bin/env python3
"""Strict q=7 forced-or-pure frontier verifier.

This verifier is intentionally narrow.  It verifies the current q=7 archive
frontier together with six strict forced-or-pure tail-closure records.  Unlike
an earlier parametric screen, it does not assume that an odd forced prime >7
always exists.  Each frontier leaf must provide either

  * an impossible pure case plus a forced-prime path,
  * a pure case refuted by the base archive plus a forced-prime path, or
  * a pure kernel already tail-controlled plus a forced-prime path.

All tail inequalities are recomputed exactly as rational numbers.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Iterable, List, Tuple

B_EXPECTED = 59
M_EXPECTED = 18

EXPECTED = {
    'q7_n1_forced': {
        'id':'q7_strict_tail_n1','replaces':'q7_param_tail_n1','source':'p','order':7,
        'cofactor':'C_7(p)=Phi_7(p)/7','source_lower_bound':29,
        'pure_case':'impossible','forced_prime_lower_bound':29,'forced_kernel':[7,29,29]
    },
    'q7_n3_forced': {
        'id':'q7_strict_tail_n3','replaces':'q7_param_tail_n3','source':'p','order':3,
        'cofactor':'C_3(p)=Phi_3(p)/7^v7(Phi_3(p))','source_lower_bound':11,
        'pure_case':'refuted_by_archive','pure_leaf':'q7_n3_pure','forced_prime_lower_bound':13,'forced_kernel':[7,11,13]
    },
    'q7_e1_forced': {
        'id':'q7_strict_tail_e1','replaces':'q7_param_tail_e1','source':'pi','order':7,
        'cofactor':'C_7(pi)=Phi_7(pi)/7','source_lower_bound':29,
        'pure_case':'impossible','forced_prime_lower_bound':29,'forced_kernel':[7,29,29]
    },
    'q7_e2_forced': {
        'id':'q7_strict_tail_e2','replaces':'q7_param_tail_e2','source':'pi','order':2,
        'cofactor':'C_2(pi)=(pi+1)/7^v7(pi+1)','source_lower_bound':13,
        'pure_case':'tail_controlled','pure_kernel':[7,13],
        'forced_prime_lower_bound':11,'forced_kernel':[7,13,11],
        'pure_exception_witness':{'pi':13,'value':2}
    },
    'q7_e3_forced': {
        'id':'q7_strict_tail_e3','replaces':'q7_param_tail_e3','source':'pi','order':3,
        'cofactor':'C_3(pi)=Phi_3(pi)/7^v7(Phi_3(pi))','source_lower_bound':37,
        'pure_case':'refuted_by_archive','pure_leaf':'q7_e3_pure','forced_prime_lower_bound':13,'forced_kernel':[7,37,13]
    },
    'q7_e6_forced': {
        'id':'q7_strict_tail_e6','replaces':'q7_param_tail_e6','source':'pi','order':6,
        'cofactor':'C_6(pi)=Phi_6(pi)/7^v7(Phi_6(pi))','source_lower_bound':17,
        'pure_case':'tail_controlled','pure_kernel':[7,17],
        'forced_prime_lower_bound':13,'forced_kernel':[7,17,13]
    },
}

REQUIRED_LOWER_LEAVES = {
    'q7_leaf_n1_lower', 'q7_leaf_n3_lower', 'q7_leaf_e1_lower',
    'q7_leaf_e2_lower', 'q7_leaf_e3_lower', 'q7_leaf_e6_lower'
}
REQUIRED_PURE_REFUTED = {'q7_leaf_n3_pure', 'q7_leaf_e3_pure'}
EXPECTED_FORCED_LEAF_IDS = { 'q7_leaf_' + node[3:] for node in EXPECTED }

class VerifyError(Exception):
    pass

def H(kernel: List[int]) -> Fraction:
    out = Fraction(1, 1)
    for p in kernel:
        if not isinstance(p, int) or p <= 1:
            raise VerifyError(f'invalid kernel prime entry {p!r}')
        out *= Fraction(p, p - 1)
    return out

def tail_value(kernel: List[int], B: int = B_EXPECTED, M: int = M_EXPECTED) -> Fraction:
    return H(kernel) * Fraction(B, B - 1) ** M

def tail_ok(kernel: List[int], B: int = B_EXPECTED, M: int = M_EXPECTED) -> bool:
    return tail_value(kernel, B, M) < 2

def v_p(n: int, p: int) -> int:
    c = 0
    while n % p == 0:
        c += 1
        n //= p
    return c

def C2_pi(pi: int) -> int:
    n = pi + 1
    return n // (7 ** v_p(n, 7))

def iter_jsonl(path: Path) -> Iterable[Tuple[int, Dict[str, Any]]]:
    with path.open('r', encoding='utf-8') as f:
        for line_no, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError as exc:
                raise VerifyError(f'{path}:{line_no}: invalid JSON: {exc}') from exc
            if not isinstance(obj, dict):
                raise VerifyError(f'{path}:{line_no}: record is not an object')
            yield line_no, obj

def load_records(paths: List[Path]) -> List[Dict[str, Any]]:
    records = []
    for path in paths:
        for _, rec in iter_jsonl(path):
            records.append(rec)
    return records

def by_id(records: List[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    out = {}
    for rec in records:
        rid = rec.get('id')
        if isinstance(rid, str):
            if rid in out:
                raise VerifyError(f'duplicate record id {rid}')
            out[rid] = rec
    return out

def require_leaf(leaf: Dict[str, Dict[str, Any]], leaf_id: str, status: str, reason: str | None = None) -> None:
    rec = leaf.get(leaf_id)
    if rec is None:
        raise VerifyError(f'missing required leaf {leaf_id}')
    if rec.get('type') != 'leaf_status':
        raise VerifyError(f'{leaf_id}: not a leaf_status record')
    if rec.get('status') != status:
        raise VerifyError(f'{leaf_id}: expected status {status}, got {rec.get("status")}')
    if reason is not None and rec.get('reason') != reason:
        raise VerifyError(f'{leaf_id}: expected reason {reason}, got {rec.get("reason")}')

def verify_base_archive(records: List[Dict[str, Any]]) -> None:
    ids = by_id(records)
    archive = ids.get('q7_archive')
    if not archive or archive.get('type') != 'branch_archive':
        raise VerifyError('missing q7_archive branch_archive record')
    split_root = ids.get('q7_split_root')
    if not split_root or split_root.get('type') != 'coverage_split':
        raise VerifyError('missing q7_split_root coverage split')
    expected_children = ['q7_n1','q7_n3','q7_e1','q7_e2','q7_e3','q7_e6']
    if split_root.get('children') != expected_children or split_root.get('complete') is not True:
        raise VerifyError('q7_split_root is not the expected complete six-child split')
    for sid in ['q7_split_n1','q7_split_n3','q7_split_e1','q7_split_e2','q7_split_e3','q7_split_e6']:
        s = ids.get(sid)
        if not s or s.get('type') != 'coverage_split' or s.get('complete') is not True:
            raise VerifyError(f'{sid}: missing or incomplete coverage split')
    for leaf_id in REQUIRED_LOWER_LEAVES:
        require_leaf(ids, leaf_id, 'refuted', 'lower_prime_avoidance')
    for leaf_id in REQUIRED_PURE_REFUTED:
        require_leaf(ids, leaf_id, 'refuted', 'finite_kernel_contradiction')
    for leaf_id in EXPECTED_FORCED_LEAF_IDS:
        require_leaf(ids, leaf_id, 'unresolved_forced')

def verify_inequality_payload(rec: Dict[str, Any], field: str, kernel: List[int]) -> None:
    payload = rec.get(field)
    if not isinstance(payload, dict):
        raise VerifyError(f'{rec.get("id")}: missing {field}')
    if payload.get('kernel') != kernel:
        raise VerifyError(f'{rec.get("id")}: {field}.kernel mismatch')
    val = tail_value(kernel, rec.get('B'), rec.get('M'))
    if payload.get('lhs_num') != val.numerator or payload.get('lhs_den') != val.denominator:
        raise VerifyError(f'{rec.get("id")}: {field} numerator/denominator mismatch')
    if payload.get('holds') is not True or not (val < 2):
        raise VerifyError(f'{rec.get("id")}: {field} does not hold strictly')

def verify_strict_record(rec: Dict[str, Any], ids: Dict[str, Dict[str, Any]]) -> str:
    if rec.get('type') != 'strict_q7_forced_or_pure_tail_closure':
        raise VerifyError(f'{rec.get("id")}: bad strict record type')
    node = rec.get('node')
    if node not in EXPECTED:
        raise VerifyError(f'{rec.get("id")}: unexpected node {node}')
    exp = EXPECTED[node]
    for key, val in exp.items():
        if key in {'pure_exception_witness'}:
            continue
        if rec.get(key) != val:
            raise VerifyError(f'{rec.get("id")}: field {key} expected {val!r}, got {rec.get(key)!r}')
    if rec.get('leaf_status') != 'q7_leaf_' + node[3:]:
        raise VerifyError(f'{rec.get("id")}: leaf_status mismatch')
    if rec.get('B') != B_EXPECTED or rec.get('M') != M_EXPECTED:
        raise VerifyError(f'{rec.get("id")}: expected B=59, M=18')
    if rec.get('lower_prime_alternatives') != [3,5]:
        raise VerifyError(f'{rec.get("id")}: expected lower_prime_alternatives [3,5]')
    if rec.get('lower_prime_alternatives_refuted_by_archive') is not True:
        raise VerifyError(f'{rec.get("id")}: lower-prime alternatives not certified as archive-refuted')
    if rec.get('conclusion') != 'tail_controlled' or rec.get('promotes_leaf_to') != 'resolved:tail_abundance_control':
        raise VerifyError(f'{rec.get("id")}: bad conclusion/promotes_leaf_to')
    verify_inequality_payload(rec, 'forced_endpoint_inequality', rec['forced_kernel'])
    pc = rec['pure_case']
    if pc == 'impossible':
        if 'pure_kernel' in rec:
            raise VerifyError(f'{rec.get("id")}: impossible pure case must not contain pure_kernel')
    elif pc == 'refuted_by_archive':
        pure_leaf = rec.get('pure_leaf')
        require_leaf(ids, 'q7_leaf_' + pure_leaf[3:] if pure_leaf and not pure_leaf.startswith('q7_leaf_') else pure_leaf, 'refuted', 'finite_kernel_contradiction')
    elif pc == 'tail_controlled':
        verify_inequality_payload(rec, 'pure_endpoint_inequality', rec['pure_kernel'])
        # Special arithmetic check for the known Q7E2 pure exception.
        if node == 'q7_e2_forced':
            wit = rec.get('pure_exception_witness')
            if wit != {'pi':13,'cofactor':'C_2(pi)=(pi+1)/7^v7(pi+1)','value':2}:
                raise VerifyError('q7_e2_forced: missing exact pure exception witness pi=13, C2=2')
            if C2_pi(13) != 2:
                raise VerifyError('q7_e2_forced: internal C2(13) check failed')
    else:
        raise VerifyError(f'{rec.get("id")}: unknown pure_case {pc}')
    return f'{rec["id"]}: {node} strict forced-or-pure closure ok'

def verify_strict_frontier(records: List[Dict[str, Any]], verbose: bool = False) -> int:
    ids = by_id(records)
    # Reject the old weak record type in strict bundles.
    old = [r.get('id','<no id>') for r in records if r.get('type') == 'parametric_q7_tail_closure']
    if old:
        raise VerifyError('strict q=7 bundle contains old parametric_q7_tail_closure records: ' + ', '.join(old))
    strict = [r for r in records if r.get('type') == 'strict_q7_forced_or_pure_tail_closure']
    by_node = {r.get('node'): r for r in strict}
    if set(by_node) != set(EXPECTED):
        raise VerifyError('strict q=7 node set mismatch: ' + repr(sorted(by_node)))
    for node in EXPECTED:
        msg = verify_strict_record(by_node[node], ids)
        if verbose:
            print(msg)
    return len(strict)

def main(argv: List[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificates', nargs='+', type=Path)
    ap.add_argument('--verbose', action='store_true')
    args = ap.parse_args(argv)
    try:
        records = load_records(args.certificates)
        verify_base_archive(records)
        count = verify_strict_frontier(records, verbose=args.verbose)
        print('Q7 coverage split complete')
        print(f'Q7 strict forced-or-pure frontier closures verified: {count}/6')
        print('q=7 branch inventory exhausted in the current formal certificate system')
        print(f'verified {len(records)} certificate record(s)')
    except VerifyError as exc:
        print(f'verification failed: {exc}', file=__import__('sys').stderr)
        return 1
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
