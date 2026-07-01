#!/usr/bin/env python3
import argparse, json, sys
from fractions import Fraction
from math import prod

EXPECTED_LEAVES = [
    'q11_n1_forced', 'q11_n5_forced', 'q11_e1_forced',
    'q11_e2_forced', 'q11_e5_forced', 'q11_e10_forced'
]
EXPECTED_FRONTIER_IDS = {
    'q11_n1_forced': 'q11_strict_tail_n1',
    'q11_n5_forced': 'q11_strict_tail_n5',
    'q11_e1_forced': 'q11_strict_tail_e1',
    'q11_e2_forced': 'q11_strict_tail_e2',
    'q11_e5_forced': 'q11_strict_tail_e5',
    'q11_e10_forced': 'q11_strict_tail_e10',
}
EXPECTED_FORCED = {
    'q11_n1_forced': (23, 11, 'Phi11_over_11'),
    'q11_n5_forced': (31, 5, 'Phi5_stripped'),
    'q11_e1_forced': (23, 11, 'Phi11_over_11'),
    'q11_e2_forced': (13, 2, 'Phi2_stripped'),
    'q11_e5_forced': (31, 5, 'Phi5_stripped'),
    'q11_e10_forced': (31, 10, 'Phi10_stripped'),
}
PURE_DEPENDENCIES = {
    'q11_n5_forced': 'q11_order5_phi5_pure_filter',
    'q11_e5_forced': 'q11_order5_phi5_pure_filter',
    'q11_e2_forced': 'q11_e2_phi2_pure_parametric_tail',
    'q11_e10_forced': 'q11_e10_phi10_pure_filter',
}


def H(kernel):
    v = Fraction(1, 1)
    for p in kernel:
        v *= Fraction(p, p - 1)
    return v


def tail(B, M):
    return Fraction(B, B - 1) ** M


def read_jsonl(path):
    out = []
    with open(path, 'r', encoding='utf-8') as f:
        for i, line in enumerate(f, 1):
            s = line.strip()
            if not s:
                continue
            try:
                rec = json.loads(s)
            except Exception as e:
                raise SystemExit(f'json parse error line {i}: {e}')
            rec['_line'] = i
            out.append(rec)
    return out


def endpoint_value(kernel, B, M):
    return H(kernel) * tail(B, M)


def verify_pure(rec, verbose=False):
    rid = rec.get('id')
    typ = rec.get('type')
    status = rec.get('status')
    if rid == 'q11_order5_phi5_pure_filter':
        assert typ == 'q11_pure_diophantine_filter'
        assert status == 'pure_diophantine_refuted_for_q11'
        assert rec.get('known_positive_integer_solutions') == [[3, 2]]
        if verbose:
            print(f'{rid}: Phi5(x)=11^c pure filter ok')
        return True
    if rid == 'q11_e10_phi10_pure_filter':
        assert typ == 'q11_pure_diophantine_filter'
        assert status == 'pure_diophantine_refuted_for_q11'
        assert rec.get('known_positive_integer_solutions') == [[2, 1]]
        if verbose:
            print(f'{rid}: Phi10(x)=11^c pure filter ok')
        return True
    if rid == 'q11_e2_phi2_pure_parametric_tail':
        assert typ == 'q11_e2_pure_parametric_tail'
        assert status == 'pure_family_tail_controlled'
        assert rec.get('endpoint_pi') == 241
        assert rec.get('pure_kernel') == [11, 241]
        B = rec.get('B'); M = rec.get('M')
        val = endpoint_value([11, 241], B, M)
        assert val < 2
        if verbose:
            print(f'{rid}: E2 pure family endpoint ok ({float(val):.16f}<2)')
        return True
    return False


def verify_frontier(rec, pure_ids, verbose=False):
    assert rec.get('type') == 'strict_q11_forced_or_pure_tail_closure'
    assert rec.get('branch') == 'small_11'
    leaf = rec.get('leaf')
    assert leaf in EXPECTED_LEAVES
    assert rec.get('id') == EXPECTED_FRONTIER_IDS[leaf]
    L, order, kind = EXPECTED_FORCED[leaf]
    assert rec.get('cofactor_kind') == kind
    assert rec.get('forced_prime_lower_bound') == L
    assert rec.get('forced_order') == order
    assert rec.get('lower_prime_avoidance') == [3, 5, 7]
    B = rec.get('B'); M = rec.get('M')
    assert B == 59 and M == 18
    forced_val = endpoint_value(rec.get('K_base', []) + [L], B, M)
    assert forced_val < 2
    mode = rec.get('mode')
    if leaf == 'q11_e2_forced':
        assert mode == 'forced_or_pure'
        assert rec.get('pure_kernel') == [11, 241]
        dep = rec.get('pure_dependency')
        assert dep == 'q11_e2_phi2_pure_parametric_tail'
        assert dep in pure_ids
        pure_val = endpoint_value(rec.get('pure_kernel'), B, M)
        assert pure_val < 2
        if verbose:
            print(f'{rec["id"]}: {leaf} forced_or_pure endpoint={float(forced_val):.16f}<2, pure_endpoint={float(pure_val):.16f}<2')
    else:
        assert mode == 'forced'
        dep = rec.get('pure_dependency')
        if dep:
            assert dep in pure_ids
        if verbose:
            print(f'{rec["id"]}: {leaf} forced endpoint={float(forced_val):.16f}<2')
    return leaf


def verify_coverage(rec, frontier_leaves, verbose=False):
    assert rec.get('type') == 'q11_first_input_coverage_wrapper'
    assert rec.get('branch') == 'small_11'
    assert rec.get('coverage_reference') == 'cor:q11-first-input-coverage'
    labels = rec.get('leaves')
    assert labels == EXPECTED_LEAVES
    assert sorted(frontier_leaves) == sorted(EXPECTED_LEAVES)
    if verbose:
        print('Q11 coverage split complete')
        print('Q11 strict frontier closures verified: 6/6')
        print('q=11 branch inventory exhausted')
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('bundle')
    ap.add_argument('--verbose', action='store_true')
    args = ap.parse_args()
    records = read_jsonl(args.bundle)
    by_type = {}
    for r in records:
        by_type.setdefault(r.get('type'), []).append(r)
    pure_ids = set()
    for r in records:
        if verify_pure(r, args.verbose):
            pure_ids.add(r.get('id'))
    if pure_ids != {'q11_order5_phi5_pure_filter', 'q11_e2_phi2_pure_parametric_tail', 'q11_e10_phi10_pure_filter'}:
        raise SystemExit(f'bad pure dependency set: {sorted(pure_ids)}')
    frontier_leaves = []
    for r in by_type.get('strict_q11_forced_or_pure_tail_closure', []):
        frontier_leaves.append(verify_frontier(r, pure_ids, args.verbose))
    if sorted(frontier_leaves) != sorted(EXPECTED_LEAVES) or len(frontier_leaves) != 6:
        raise SystemExit(f'bad frontier leaves: {frontier_leaves}')
    covs = by_type.get('q11_first_input_coverage_wrapper', [])
    if len(covs) != 1:
        raise SystemExit(f'expected exactly one coverage wrapper, found {len(covs)}')
    verify_coverage(covs[0], frontier_leaves, args.verbose)
    if not args.verbose:
        print('q=11 branch inventory exhausted')
    print(f'verified {len(records)} q=11 master record(s)')

if __name__ == '__main__':
    main()
