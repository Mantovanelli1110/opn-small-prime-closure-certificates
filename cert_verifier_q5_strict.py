#!/usr/bin/env python3
"""Strict Q5 verifier layer for the OPN certificate bundle.

This script delegates all ordinary record verification to the current
parametric certificate verifier and then adds theorem-level Q5 consistency
checks that are easy to miss in a purely syntactic record verifier:

* the Q5E1 finite exceptional window is exactly the set of primes
  pi < 1381 with pi == 1 mod 60;
* the Q5N finite exceptional witness window is exactly the set of primes
  p < 211 with p == 1 mod 5;
* the Q5E1 and Q5N Phi_5(x)/5 parametric records use a derived lower bound
  r >= 11 for forced odd support primes, rather than merely accepting a
  supplied lower bound;
* if the full Q5 master bundle is present, Q5E2, Q5E1, and Q5N closure
  dependencies are checked together.

The ordinary verifier remains the source of truth for factorization, order,
valuation, archive, and domain-extension checks.  This layer only strengthens
Q5-specific global and parametric theorem checks.
"""
from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Iterable, List, Tuple

BASE_VERIFIER = Path(__file__).with_name("cert_verifier_domain_extension_parametric_q5_all_q5n.py")


def load_base_verifier():
    spec = importlib.util.spec_from_file_location("q5_base_verifier", BASE_VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load base verifier from {BASE_VERIFIER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def int_field(record: Dict[str, Any], key: str) -> int:
    value = record.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise RuntimeError(f"record {record.get('id', '<unknown>')}: {key} must be an integer")
    return value


def list_int_field(record: Dict[str, Any], key: str) -> List[int]:
    value = record.get(key)
    if not isinstance(value, list):
        raise RuntimeError(f"record {record.get('id', '<unknown>')}: {key} must be a list")
    out: List[int] = []
    for item in value:
        if not isinstance(item, int) or isinstance(item, bool):
            raise RuntimeError(f"record {record.get('id', '<unknown>')}: {key} contains non-integer item")
        out.append(item)
    return out


def by_id(records: Iterable[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    out: Dict[str, Dict[str, Any]] = {}
    for rec in records:
        rid = rec.get("id")
        if isinstance(rid, str):
            out[rid] = rec
    return out


def is_prime(n: int) -> bool:
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


def primes_less_than_with_congruence(bound: int, modulus: int, residue: int) -> List[int]:
    return [p for p in range(2, bound) if is_prime(p) and p % modulus == residue]


def exact_H(primes: Iterable[int]) -> Fraction:
    result = Fraction(1, 1)
    for p in primes:
        require(is_prime(p), f"H-kernel contains non-prime {p}")
        result *= Fraction(p, p - 1)
    return result


def archive_is_closed(rec: Dict[str, Any]) -> bool:
    summary = rec.get("domain_summary", {})
    counts = summary.get("status_counts", {})
    return (
        rec.get("type") == "branch_archive"
        and summary.get("recursive_controlled") is True
        and counts.get("reduced", 0) == 0
        and counts.get("unresolved", 0) == 0
    )


def parametric_ok(rec: Dict[str, Any], expected_type: str, expected_branch: str) -> bool:
    if rec.get("type") != expected_type:
        return False
    if rec.get("branch") != expected_branch:
        return False
    vi = rec.get("verified_inequality", {})
    return isinstance(vi, dict) and vi.get("holds") is True


def verify_lhs(record: Dict[str, Any], lhs: Fraction) -> None:
    supplied = record.get("verified_inequality")
    require(isinstance(supplied, dict), f"{record.get('id')}: verified_inequality must be present")
    if "lhs_num" in supplied:
        require(supplied["lhs_num"] == lhs.numerator, f"{record.get('id')}: lhs_num mismatch")
    if "lhs_den" in supplied:
        require(supplied["lhs_den"] == lhs.denominator, f"{record.get('id')}: lhs_den mismatch")
    if "holds" in supplied:
        require(supplied["holds"] is (lhs < 2), f"{record.get('id')}: holds mismatch")


def check_phi5_over_5_forced_prime_bound(record: Dict[str, Any], variable: str, lower_key: str, modulus: int, residue: int) -> str:
    """Check the Q5 Phi_5(x)/5 theorem-level forced-prime bound.

    The symbolic argument verified here is:
      x prime, x >= lower_bound, x == 1 mod 5;
      C_5(x)=Phi_5(x)/5 is an integer > 1;
      v_5(Phi_5(x))=1 by LTE, so 5 does not divide C_5(x);
      3 does not divide C_5(x), because Phi_5(x) is 2 mod 3 when x == 1 mod 3
        and 1 mod 3 when x == 2 mod 3;
      any prime divisor r of C_5(x) is not x and has ord_r(x)=5, hence
        r == 1 mod 5;
      therefore every odd forced support prime divisor has r >= 11.
    """
    rid = record.get("id", "<unknown>")
    require(record.get("forced_cofactor") == "Phi5_over_5", f"{rid}: forced_cofactor must be Phi5_over_5")
    x_lb = int_field(record, lower_key)
    require(is_prime(x_lb), f"{rid}: {lower_key} must be prime")
    require(x_lb >= 11, f"{rid}: lower bound must be at least 11")

    rec_mod = int_field(record, f"{variable}_congruence_mod")
    rec_rem = int_field(record, f"{variable}_congruence_rem")
    require(rec_mod == modulus and rec_rem == residue, f"{rid}: unexpected {variable} congruence")
    require(x_lb % rec_mod == rec_rem, f"{rid}: lower bound does not satisfy congruence")
    require(x_lb % 5 == 1, f"{rid}: Phi5_over_5 lemma requires {variable} == 1 mod 5")

    claimed_r_lb = int_field(record, "forced_prime_lower_bound")
    # This is the derived theorem-level bound.  A stricter supplied lower bound
    # would need extra proof; a weaker one wastes the theorem.  Require exact 11.
    require(claimed_r_lb == 11, f"{rid}: forced_prime_lower_bound must be the derived value 11")
    require(is_prime(claimed_r_lb) and claimed_r_lb % 5 == 1, f"{rid}: derived lower bound must be a prime == 1 mod 5")

    B = int_field(record, "B")
    M = record.get("M", record.get("tail_count_bound"))
    require(isinstance(M, int) and not isinstance(M, bool), f"{rid}: M must be an integer")
    require(B == 59 and M == 18, f"{rid}: expected B=59 and M=18")

    # Endpoint tail check, monotone in x and r.
    lhs = exact_H([5, x_lb, claimed_r_lb]) * (Fraction(B, B - 1) ** M)
    require(lhs < 2, f"{rid}: endpoint tail-control inequality fails")
    verify_lhs(record, lhs)
    return f"{rid}: strict Phi5_over_5 forced-prime bound derived ({variable}>={x_lb}, r>=11)"


def check_q5e1_finite_window(records_by_id: Dict[str, Dict[str, Any]]) -> str:
    archive = records_by_id.get("q5e1_first_domain")
    param = records_by_id.get("q5e1_pi_ge_1381_parametric_tail_closure")
    require(isinstance(archive, dict), "Q5E1 finite archive q5e1_first_domain missing")
    require(isinstance(param, dict), "Q5E1 parametric record missing")
    pi_lb = int_field(param, "pi_lower_bound")
    expected = primes_less_than_with_congruence(pi_lb, 60, 1)
    bounds = archive.get("bounds", {})
    window = bounds.get("window", {}) if isinstance(bounds, dict) else {}
    candidates = window.get("candidates")
    if candidates is None:
        candidates = archive.get("branch_tag", {}).get("candidate_window")
    require(isinstance(candidates, list), "Q5E1 finite archive does not expose candidate list")
    require(candidates == expected, f"Q5E1 finite window mismatch: expected {expected}, got {candidates}")
    summary = archive.get("domain_summary", {})
    require(summary.get("leaves_checked") == len(expected), "Q5E1 leaves_checked does not equal exact finite window size")
    require(archive_is_closed(archive), "Q5E1 finite archive is not closed")
    return f"Q5E1 finite window exact: {len(expected)} primes pi<={pi_lb - 1}, pi==1 mod 60"


def check_q5n_finite_window(records_by_id: Dict[str, Dict[str, Any]]) -> str:
    archive = records_by_id.get("q5n_first_domain")
    param = records_by_id.get("q5n_p_ge_211_parametric_tail_closure")
    require(isinstance(archive, dict), "Q5N finite archive q5n_first_domain missing")
    require(isinstance(param, dict), "Q5N parametric record missing")
    p_lb = int_field(param, "p_lower_bound")
    expected = primes_less_than_with_congruence(p_lb, 5, 1)
    branch_tag = archive.get("branch_tag", {})
    candidates = branch_tag.get("candidate_window") if isinstance(branch_tag, dict) else None
    require(isinstance(candidates, list), "Q5N finite archive does not expose candidate_window")
    require(candidates == expected, f"Q5N finite witness window mismatch: expected {expected}, got {candidates}")
    summary = archive.get("domain_summary", {})
    require(summary.get("leaves_checked") == len(expected), "Q5N leaves_checked does not equal exact finite window size")
    require(archive_is_closed(archive), "Q5N finite archive is not closed")
    return f"Q5N finite witness window exact: {len(expected)} primes p<{p_lb}, p==1 mod 5"


def check_q5_closure_dependencies(records_by_id: Dict[str, Dict[str, Any]]) -> List[str]:
    messages: List[str] = []
    q5e2_archive_id = "q5_d52_409_41_E40_all_tail_successor_archive"
    if q5e2_archive_id in records_by_id:
        require(archive_is_closed(records_by_id[q5e2_archive_id]), "Q5E2 final finite archive is not closed")
        for rid in [
            "q5e2_349_7_parametric_post_window_closure",
            "q5e2_109_11_parametric_post_window_closure",
            "q5e2_229_23_parametric_post_window_closure",
            "q5e2_409_41_parametric_post_window_closure",
        ]:
            require(parametric_ok(records_by_id.get(rid, {}), "parametric_post_window_closure", "Q5E2"), f"Q5E2 parametric closure missing or invalid: {rid}")
        messages.append("Q5E2 closure dependencies present")

    if "q5e1_first_domain" in records_by_id or "q5e1_pi_ge_1381_parametric_tail_closure" in records_by_id:
        messages.append(check_q5e1_finite_window(records_by_id))
        rec = records_by_id["q5e1_pi_ge_1381_parametric_tail_closure"]
        require(parametric_ok(rec, "parametric_q5e1_pi_window_closure", "Q5E1"), "Q5E1 parametric record failed ordinary checks")
        messages.append(check_phi5_over_5_forced_prime_bound(rec, "pi", "pi_lower_bound", 60, 1))

    if "q5n_first_domain" in records_by_id or "q5n_p_ge_211_parametric_tail_closure" in records_by_id:
        messages.append(check_q5n_finite_window(records_by_id))
        rec = records_by_id["q5n_p_ge_211_parametric_tail_closure"]
        require(parametric_ok(rec, "parametric_q5n_witness_window_closure", "Q5N"), "Q5N parametric record failed ordinary checks")
        messages.append(check_phi5_over_5_forced_prime_bound(rec, "p", "p_lower_bound", 5, 1))

    if (
        q5e2_archive_id in records_by_id
        and "q5e1_first_domain" in records_by_id
        and "q5n_first_domain" in records_by_id
    ):
        messages.append("strict q=5 closure dependencies ok")
    return messages


def run_verification(paths: List[Path], verbose: bool = False) -> Tuple[int, List[str]]:
    verifier = load_base_verifier()
    records: List[Dict[str, Any]] = []
    total = 0
    for path in paths:
        for line_no, record in verifier.iter_jsonl(path):
            result = verifier.verify_record(record)
            records.append(record)
            total += 1
            if verbose:
                print(f"{path}:{line_no}: {result}")
    verifier.verify_generic_archives(records)
    verifier.verify_domain_extensions(records)
    for summary in verifier.domain_archive_summaries(records):
        print(summary)
    messages = check_q5_closure_dependencies(by_id(records))
    return total, messages


def main(argv: List[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="+", type=Path, help="JSONL certificate files")
    parser.add_argument("--verbose", action="store_true", help="print every ordinary verified record")
    args = parser.parse_args(argv)
    try:
        total, messages = run_verification(args.certificates, verbose=args.verbose)
    except Exception as exc:
        print(f"strict q=5 verification failed: {exc}", file=sys.stderr)
        return 1
    for message in messages:
        print(message)
    print(f"strict q=5 checks: {len(messages)} ok")
    print(f"verified {total} certificate record(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
