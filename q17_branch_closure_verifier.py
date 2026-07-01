#!/usr/bin/env python3
import argparse, json
from fractions import Fraction

EXPECTED_LEAVES = [
    'q17_n1_forced',
    'q17_e1_forced',
    'q17_e2_forced',
]

EXPECTED_FRONTIER_IDS = {
    'q17_n1_forced': 'q17_strict_tail_n1',
    'q17_e1_forced': 'q17_strict_tail_e1',
    'q17_e2_forced': 'q17_strict_tail_e2',
}

EXPECTED_FORCED = {
    'q17_n1_forced': (103, 17, 'Phi17_over_17'),
    'q17_e1_forced': (103, 17, 'Phi17_over_17'),
    'q17_e2_forced': (19, 2, 'Phi2_stripped'),
}

PURE_ID = 'q17_e2_phi2_pure_parametric_tail'
ENDPOINT_IDS = {
    'q17_order17_forced_prime_endpoint',
    'q17_e2_pure_first_prime_endpoint',
}


def is_prime(n):
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0:
        return False
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def H(kernel):
    value = Fraction(1, 1)
    for p in kernel:
        value *= Fraction(p, p - 1)
    return value


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
            except Exception as exc:
                raise SystemExit(f'json parse error line {i}: {exc}')
            rec['_line'] = i
            records.append(rec)
    return records


def verify_pure(rec, verbose=False):
    if rec.get('id') != PURE_ID:
        return False
    assert rec.get('type') == 'q17_e2_pure_parametric_tail'
    assert rec.get('status') == 'pure_family_tail_controlled'
    assert rec.get('endpoint_dependency') == 'q17_e2_pure_first_prime_endpoint'
    assert rec.get('first_prime_endpoint') == 577
    assert rec.get('pure_kernel') == [17, 577]
    B = rec.get('B')
    M = rec.get('M')
    assert B == 59 and M == 18
    val = endpoint_value([17, 577], B, M)
    assert val < 2
    if verbose:
        print(f'{PURE_ID}: E2 pure family endpoint ok ({float(val):.16f}<2)')
    return True


def verify_endpoint(rec, verbose=False):
    rid = rec.get('id')
    if rid == 'q17_order17_forced_prime_endpoint':
        assert rec.get('type') == 'q17_endpoint_certificate'
        assert rec.get('endpoint') == 103
        assert rec.get('endpoint_prime') is True
        assert is_prime(103)
        assert rec.get('endpoint_congruence') == [17, 1]
        assert 103 % 17 == 1
        excluded = rec.get('excluded_candidates')
        assert excluded == [35, 52, 69, 86]
        for n in excluded:
            assert n > 17 and n < 103 and n % 17 == 1
            assert not is_prime(n)
        if verbose:
            print(f'{rid}: least prime r>17, r == 1 mod 17, is 103')
        return True
    if rid == 'q17_e2_pure_first_prime_endpoint':
        assert rec.get('type') == 'q17_endpoint_certificate'
        assert rec.get('endpoint_b') == 2
        assert rec.get('endpoint') == 577
        assert rec.get('endpoint_prime') is True
        assert 2 * 17**2 - 1 == 577
        assert is_prime(577)
        excluded = rec.get('excluded_family_values')
        assert excluded == [{'b': 1, 'value': 33, 'factorization': [[3, 1], [11, 1]]}]
        assert 2 * 17 - 1 == 33
        assert 33 == 3 * 11
        if verbose:
            print(f'{rid}: first prime in pi=2*17^b-1 is 577')
        return True
    return False


def verify_frontier(rec, pure_ids, verbose=False):
    assert rec.get('type') == 'strict_q17_forced_or_pure_tail_closure'
    assert rec.get('branch') == 'small_17'
    leaf = rec.get('leaf')
    assert leaf in EXPECTED_LEAVES
    assert rec.get('id') == EXPECTED_FRONTIER_IDS[leaf]
    L, order, kind = EXPECTED_FORCED[leaf]
    assert rec.get('cofactor_kind') == kind
    assert rec.get('forced_prime_lower_bound') == L
    assert rec.get('forced_order') == order
    assert rec.get('lower_prime_avoidance') == [3, 5, 7, 11, 13]
    B = rec.get('B')
    M = rec.get('M')
    assert B == 59 and M == 18
    forced_val = endpoint_value(rec.get('K_base', []) + [L], B, M)
    assert forced_val < 2
    if order == 17:
        assert 'q17_order17_forced_prime_endpoint' in pure_ids
        assert L == 103
    if leaf == 'q17_e2_forced':
        assert is_prime(L) and L == 19
    mode = rec.get('mode')
    if leaf == 'q17_e2_forced':
        assert mode == 'forced_or_pure'
        assert rec.get('pure_dependency') == PURE_ID
        assert PURE_ID in pure_ids
        assert rec.get('pure_kernel') == [17, 577]
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
    assert rec.get('type') == 'q17_first_input_coverage_wrapper'
    assert rec.get('branch') == 'small_17'
    assert rec.get('coverage_reference') == 'cor:q17-first-input-coverage'
    assert rec.get('leaves') == EXPECTED_LEAVES
    assert sorted(frontier_leaves) == sorted(EXPECTED_LEAVES)
    assert rec.get('frontier_record_type') == 'strict_q17_forced_or_pure_tail_closure'
    assert rec.get('conclusion') == 'q17_branch_inventory_exhausted_in_current_formal_certificate_system'
    if verbose:
        print('Q17 coverage split complete')
        print('Q17 strict frontier closures verified: 3/3')
        print('q=17 branch inventory exhausted')
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
        if verify_endpoint(rec, args.verbose):
            pure_ids.add(rec.get('id'))
    if not ENDPOINT_IDS.issubset(pure_ids):
        raise SystemExit(f'bad endpoint dependency set: {sorted(pure_ids)}')
    for rec in records:
        if verify_pure(rec, args.verbose):
            pure_ids.add(rec.get('id'))
    if not ({PURE_ID} | ENDPOINT_IDS).issubset(pure_ids):
        raise SystemExit(f'bad pure dependency set: {sorted(pure_ids)}')
    frontier_leaves = []
    for rec in by_type.get('strict_q17_forced_or_pure_tail_closure', []):
        frontier_leaves.append(verify_frontier(rec, pure_ids, args.verbose))
    if sorted(frontier_leaves) != sorted(EXPECTED_LEAVES) or len(frontier_leaves) != 3:
        raise SystemExit(f'bad frontier leaves: {frontier_leaves}')
    covs = by_type.get('q17_first_input_coverage_wrapper', [])
    if len(covs) != 1:
        raise SystemExit(f'expected exactly one coverage wrapper, found {len(covs)}')
    verify_coverage(covs[0], frontier_leaves, args.verbose)
    if not args.verbose:
        print('q=17 branch inventory exhausted')
    print(f'verified {len(records)} q=17 master record(s)')


if __name__ == '__main__':
    main()
