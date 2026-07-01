#!/usr/bin/env python3
import argparse, json
from fractions import Fraction

EXPECTED_LEAVES = [
    'q13_n1_forced', 'q13_n3_forced', 'q13_e1_forced',
    'q13_e2_forced', 'q13_e3_forced', 'q13_e6_forced'
]
EXPECTED_FRONTIER_IDS = {
    'q13_n1_forced': 'q13_strict_tail_n1',
    'q13_n3_forced': 'q13_strict_tail_n3',
    'q13_e1_forced': 'q13_strict_tail_e1',
    'q13_e2_forced': 'q13_strict_tail_e2',
    'q13_e3_forced': 'q13_strict_tail_e3',
    'q13_e6_forced': 'q13_strict_tail_e6',
}
EXPECTED_FORCED = {
    'q13_n1_forced': (53, 13, 'Phi13_over_13'),
    'q13_n3_forced': (19, 3, 'Phi3_stripped'),
    'q13_e1_forced': (53, 13, 'Phi13_over_13'),
    'q13_e2_forced': (17, 2, 'Phi2_stripped'),
    'q13_e3_forced': (19, 3, 'Phi3_stripped'),
    'q13_e6_forced': (19, 6, 'Phi6_stripped'),
}
PURE_IDS_EXPECTED = {
    'q13_order3_phi3_pure_filter',
    'q13_e2_phi2_pure_parametric_tail',
    'q13_e6_phi6_pure_filter',
}
PURE_DEPENDENCIES = {
    'q13_n3_forced': 'q13_order3_phi3_pure_filter',
    'q13_e2_forced': 'q13_e2_phi2_pure_parametric_tail',
    'q13_e3_forced': 'q13_order3_phi3_pure_filter',
    'q13_e6_forced': 'q13_e6_phi6_pure_filter',
}

def H(kernel):
    v = Fraction(1, 1)
    for p in kernel:
        v *= Fraction(p, p - 1)
    return v

def tail(B, M):
    return Fraction(B, B - 1) ** M

def endpoint_value(kernel, B, M):
    return H(kernel) * tail(B, M)

def read_jsonl(path):
    records = []
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
            records.append(rec)
    return records

def verify_pure(rec, verbose=False):
    rid = rec.get('id')
    typ = rec.get('type')
    status = rec.get('status')
    if rid == 'q13_order3_phi3_pure_filter':
        assert typ == 'q13_pure_exception_filter'
        assert status == 'pure_diophantine_refuted'
        assert rec.get('positive_solutions') == [{'x': 3, 'c': 1}]
        if verbose:
            print(f'{rid}: Phi3(x)=13^c pure filter ok')
        return True
    if rid == 'q13_e6_phi6_pure_filter':
        assert typ == 'q13_pure_exception_filter'
        assert status == 'pure_diophantine_refuted'
        assert rec.get('positive_solutions') == [{'pi': 4, 'c': 1}]
        if verbose:
            print(f'{rid}: Phi6(pi)=13^c pure filter ok')
        return True
    if rid == 'q13_e2_phi2_pure_parametric_tail':
        assert typ == 'q13_e2_pure_parametric_tail'
        assert status == 'pure_rows_listed_and_tail_controlled'
        assert rec.get('first_prime_endpoint') == 337
        assert rec.get('pure_kernel') == [13, 337]
        B = rec.get('B'); M = rec.get('M')
        assert B == 59 and M == 18
        val = endpoint_value([13, 337], B, M)
        assert val < 2
        if verbose:
            print(f'{rid}: E2 pure family endpoint ok ({float(val):.16f}<2)')
        return True
    return False

def verify_frontier(rec, pure_ids, verbose=False):
    assert rec.get('type') == 'strict_q13_forced_or_pure_tail_closure'
    leaf = rec.get('leaf')
    assert leaf in EXPECTED_LEAVES
    assert rec.get('id') == EXPECTED_FRONTIER_IDS[leaf]
    L, order, kind = EXPECTED_FORCED[leaf]
    assert rec.get('cofactor_kind') == kind
    assert rec.get('forced_prime_lower_bound') == L
    assert rec.get('forced_order') == order
    assert rec.get('lower_prime_avoidance') == [3, 5, 7, 11]
    B = rec.get('B'); M = rec.get('M')
    assert B == 59 and M == 18
    forced_val = endpoint_value(rec.get('K_base', []) + [L], B, M)
    assert forced_val < 2
    dep_expected = PURE_DEPENDENCIES.get(leaf)
    dep = rec.get('pure_dependency')
    if dep_expected:
        assert dep == dep_expected
        assert dep in pure_ids
    mode = rec.get('mode')
    if leaf == 'q13_e2_forced':
        assert mode == 'forced_or_pure'
        assert rec.get('pure_kernel') == [13, 337]
        pure_val = endpoint_value(rec.get('pure_kernel'), B, M)
        assert pure_val < 2
        if verbose:
            print(f'{rec["id"]}: {leaf} forced_or_pure endpoint={float(forced_val):.16f}<2, pure_endpoint={float(pure_val):.16f}<2')
    else:
        assert mode == 'forced'
        if verbose:
            print(f'{rec["id"]}: {leaf} forced endpoint={float(forced_val):.16f}<2')
    return leaf

def verify_coverage(rec, frontier_leaves, verbose=False):
    assert rec.get('type') == 'q13_first_input_coverage_wrapper'
    assert rec.get('branch') == 'small_13'
    assert rec.get('coverage_reference') == 'cor:q13-first-input-coverage'
    assert rec.get('leaves') == EXPECTED_LEAVES
    assert sorted(frontier_leaves) == sorted(EXPECTED_LEAVES)
    assert rec.get('frontier_record_type') == 'strict_q13_forced_or_pure_tail_closure'
    if verbose:
        print('Q13 coverage split complete')
        print('Q13 strict frontier closures verified: 6/6')
        print('q=13 branch inventory exhausted')
    return True

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('bundle')
    ap.add_argument('--verbose', action='store_true')
    args = ap.parse_args()
    records = read_jsonl(args.bundle)
    by_type = {}
    for rec in records:
        by_type.setdefault(rec.get('type'), []).append(rec)
    pure_ids = set()
    for rec in records:
        if verify_pure(rec, args.verbose):
            pure_ids.add(rec.get('id'))
    if pure_ids != PURE_IDS_EXPECTED:
        raise SystemExit(f'bad pure dependency set: {sorted(pure_ids)}')
    frontier_leaves = []
    for rec in by_type.get('strict_q13_forced_or_pure_tail_closure', []):
        frontier_leaves.append(verify_frontier(rec, pure_ids, args.verbose))
    if sorted(frontier_leaves) != sorted(EXPECTED_LEAVES) or len(frontier_leaves) != 6:
        raise SystemExit(f'bad frontier leaves: {frontier_leaves}')
    covs = by_type.get('q13_first_input_coverage_wrapper', [])
    if len(covs) != 1:
        raise SystemExit(f'expected exactly one coverage wrapper, found {len(covs)}')
    verify_coverage(covs[0], frontier_leaves, args.verbose)
    if not args.verbose:
        print('q=13 branch inventory exhausted')
    print(f'verified {len(records)} q=13 master record(s)')

if __name__ == '__main__':
    main()
