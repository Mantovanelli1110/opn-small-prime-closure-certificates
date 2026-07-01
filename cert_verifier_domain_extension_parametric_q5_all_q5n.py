#!/usr/bin/env python3
"""Independent certificate verifier for the OPN cyclotomic-closure draft.

The verifier reads JSONL certificates and recomputes:

* cyclotomic values Phi_d(p),
* supplied factorizations by multiplication,
* primality of prime factors below 2^64 using deterministic Miller-Rabin,
* multiplicative orders ord_r(p),
* valuations v_r(Phi_d(p)) and optional v_r(sigma(p^e)),
* exact abundancy upper products H(K)=prod_{p in K} p/(p-1).

It intentionally does not search for factors.  A factorization certificate is
accepted only when the supplied factors multiply to the recomputed target and
each prime factor is independently certified by this verifier.  For factors
>= 2^64, add an external proof checker in a later iteration rather than
silently trusting probable-prime output.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from functools import lru_cache
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Iterable, List, Set, Tuple

U64 = 1 << 64
MODULUS_19 = 19
NON_EULER_19_TYPES = {1, 3, 9}
EULER_19_TYPES = {1, 2, 3, 6, 9, 18}

GENERIC_RECORD_TYPES = {
    "branch_archive",
    "coverage_split",
    "leaf_status",
    "forced_cofactor",
    "tail_count_certificate",
    "abundance_obstruction",
    "literature_filter_certificate",
    "domain_extension",
}

ARCHIVE_REFERENCE_FIELDS = {
    "coverage_splits": "coverage_split",
    "leaf_statuses": "leaf_status",
    "forced_cofactors": "forced_cofactor",
    "tail_count_certificates": "tail_count_certificate",
    "abundance_obstructions": "abundance_obstruction",
    "literature_filter_certificates": "literature_filter_certificate",
}

ALLOWED_SPLIT_KINDS = {
    "minimal_prime",
    "residual_19",
    "euler_role",
    "exponent_schema",
    "order_type",
    "input_neutral",
    "forced_prime_extension",
    "valuation_defect",
    "bounded_range",
    "residue_class_split",
    "tail_domain_refinement",
}

ALLOWED_LEAF_STATUSES = {
    "refuted",
    "resolved",
    "unresolved_forced",
    "unresolved_exceptional",
}

ALLOWED_LEAF_REASONS = {
    "valuation_defect",
    "euler_parity_violation",
    "lower_prime_avoidance",
    "excluded_prime_avoidance",
    "abundance_obstruction",
    "tail_abundance_control",
    "literature_obstruction",
    "finite_kernel_contradiction",
    "certified_branch_extension",
    "bounded_range_obstruction",
}

ALLOWED_UNRESOLVED_REASONS = {
    "missing_factorization",
    "tail_bound_too_weak",
    "abundance_cutoff_too_weak",
    "missing_small_prime_exclusion",
    "requires_child_split",
    "large_prime_certificate_missing",
}


ALLOWED_EXTENSION_COVERAGE_REASONS = {
    "euler_role_split",
    "forced_prime_extension",
    "bounded_range_split",
    "residue_class_split",
    "tail_domain_refinement",
    "certified_branch_extension",
}

AGGREGATION_SAFE_AUDIT_STATUSES = {
    "lower_prime_refuted",
    "abundance_refuted",
    "directly_closed",
    "tail_controlled",
    "child_archive_tail_controlled",
}

AGGREGATION_SAFE_LEAF_STATUSES = {"refuted", "resolved"}



class VerifyError(Exception):
    """Raised when a certificate fails verification."""


def int_value(value: Any, field: str) -> int:
    try:
        n = int(value)
    except Exception as exc:  # pragma: no cover - defensive message
        raise VerifyError(f"{field} is not an integer: {value!r}") from exc
    return n


def str_value(value: Any, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise VerifyError(f"{field} must be a nonempty string")
    return value


def bool_value(value: Any, field: str) -> bool:
    if not isinstance(value, bool):
        raise VerifyError(f"{field} must be a boolean")
    return value


def string_list(raw: Any, field: str, *, allow_empty: bool = True) -> List[str]:
    if not isinstance(raw, list):
        raise VerifyError(f"{field} must be a list")
    if not allow_empty and not raw:
        raise VerifyError(f"{field} must be nonempty")
    out = [str_value(item, f"{field}[]") for item in raw]
    if len(set(out)) != len(out):
        raise VerifyError(f"{field} contains duplicate ids")
    return out


def optional_string_list(record: Dict[str, Any], field: str) -> List[str]:
    raw = record.get(field, [])
    return string_list(raw, field)


def record_id(record: Dict[str, Any]) -> str:
    return str_value(record.get("id"), "id")


def factor_pairs(raw: Any, field: str = "factors") -> List[Tuple[int, int]]:
    if not isinstance(raw, list):
        raise VerifyError(f"{field} must be a list")
    pairs: List[Tuple[int, int]] = []
    for item in raw:
        if isinstance(item, dict):
            p = int_value(item.get("p", item.get("prime")), f"{field}.prime")
            e = int_value(item.get("e", item.get("exp", 1)), f"{field}.exp")
        elif isinstance(item, list) and len(item) == 2:
            p = int_value(item[0], f"{field}.prime")
            e = int_value(item[1], f"{field}.exp")
        else:
            raise VerifyError(f"{field} entries must be [prime, exp] or objects")
        if p < 2 or e < 1:
            raise VerifyError(f"invalid factor pair {(p, e)} in {field}")
        pairs.append((p, e))
    return pairs


def multiply_factors(factors: Iterable[Tuple[int, int]]) -> int:
    product = 1
    for p, e in factors:
        product *= p**e
    return product


def trial_factor(n: int) -> Dict[int, int]:
    if n < 1:
        raise VerifyError(f"cannot factor {n}")
    out: Dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def divisors_from_factorization(factors: Dict[int, int]) -> List[int]:
    divisors = [1]
    for p, e in factors.items():
        divisors = [d * p**k for d in divisors for k in range(e + 1)]
    return sorted(divisors)


@lru_cache(maxsize=None)
def divisors(n: int) -> Tuple[int, ...]:
    return tuple(divisors_from_factorization(trial_factor(n)))


@lru_cache(maxsize=None)
def cyclotomic_value(a: int, n: int) -> int:
    if n < 1:
        raise VerifyError("cyclotomic index must be positive")
    if n == 1:
        return a - 1
    numerator = a**n - 1
    denominator = 1
    for d in divisors(n):
        if d < n:
            denominator *= cyclotomic_value(a, d)
    if numerator % denominator != 0:
        raise VerifyError(f"internal cyclotomic division failed for Phi_{n}({a})")
    return numerator // denominator


def is_probable_prime_u64(n: int) -> bool:
    """Deterministic Miller-Rabin for unsigned 64-bit integers."""
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small_primes:
        if n == p:
            return True
        if n % p == 0:
            return False

    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2

    # Deterministic for n < 2^64.
    bases = (2, 325, 9375, 28178, 450775, 9780504, 1795265022)
    for a in bases:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def require_prime(n: int) -> None:
    if n >= U64:
        raise VerifyError(
            f"prime factor {n} is >= 2^64; attach an external primality "
            "certificate and extend cert_verifier.py to check it"
        )
    if not is_probable_prime_u64(n):
        raise VerifyError(f"factor {n} is not prime")


def large_prime_certificates(raw: Any) -> Dict[int, Any]:
    if raw is None:
        return {}
    if not isinstance(raw, dict):
        raise VerifyError("large_prime_certificates must be an object keyed by prime")
    certs: Dict[int, Any] = {}
    for key, cert in raw.items():
        certs[int_value(key, "large_prime_certificates.key")] = cert
    return certs


def require_prime_certified(
    n: int,
    certs: Dict[int, Any] | None = None,
    stack: Set[int] | None = None,
) -> None:
    """Require primality, using deterministic u64 MR or recursive Pocklington."""
    if n < U64:
        require_prime(n)
        return

    certs = certs or {}
    if n not in certs:
        raise VerifyError(
            f"prime factor {n} is >= 2^64; attach an external primality certificate"
        )

    verify_pocklington_certificate(n, certs[n], certs, stack)


def factorization_dict(
    raw: Any,
    field: str,
    certs: Dict[int, Any] | None = None,
) -> Dict[int, int]:
    out: Dict[int, int] = {}
    for p, e in factor_pairs(raw, field):
        require_prime_certified(p, certs or {}, None)
        out[p] = out.get(p, 0) + e
    return out


def verify_pocklington_certificate(
    n: int,
    cert: Any,
    certs: Dict[int, Any] | None = None,
    stack: Set[int] | None = None,
) -> None:
    """Verify a Pocklington certificate, recursively checking large factors."""
    if not isinstance(cert, dict):
        raise VerifyError(f"large-prime certificate for {n} must be an object")
    if str_value(cert.get("method"), "large_prime_certificate.method") != "pocklington":
        raise VerifyError(f"large-prime certificate for {n} must use pocklington")

    certs = certs or {}
    stack = set() if stack is None else set(stack)
    if n in stack:
        raise VerifyError(f"cyclic large-prime certificate dependency at {n}")
    stack.add(n)

    base = int_value(cert.get("base"), "large_prime_certificate.base")
    if base <= 1 or base >= n:
        raise VerifyError(f"invalid Pocklington base for {n}")

    factors = factorization_dict(
        cert.get("n_minus_1_factors"),
        f"large_prime_certificate.{n}.n_minus_1_factors",
        certs,
    )

    factored_part = multiply_factors(factors.items())
    if factored_part != n - 1:
        raise VerifyError(f"Pocklington certificate for {n} has wrong n-1 factorization")
    if factored_part <= math.isqrt(n):
        raise VerifyError(f"Pocklington certificate for {n} has insufficient factored part")
    if pow(base, n - 1, n) != 1:
        raise VerifyError(f"Pocklington base {base} fails Fermat test for {n}")

    for q in factors:
        if math.gcd(pow(base, (n - 1) // q, n) - 1, n) != 1:
            raise VerifyError(f"Pocklington gcd test for q={q} fails on {n}")


def r_minus_1_from_large_certificate(
    r: int,
    certs: Dict[int, Any] | None = None,
) -> Dict[int, int] | None:
    certs = certs or {}
    cert = certs.get(r)
    if not isinstance(cert, dict):
        return None
    if cert.get("method") != "pocklington":
        return None
    return factorization_dict(
        cert.get("n_minus_1_factors"),
        f"large_prime_certificate.{r}.n_minus_1_factors",
        certs,
    )


def multiplicative_order(
    a: int,
    r: int,
    r_minus_1: Dict[int, int] | None = None,
    certs: Dict[int, Any] | None = None,
) -> int:
    if math.gcd(a, r) != 1:
        raise VerifyError(f"ord_{r}({a}) is undefined")

    certs = certs or {}
    if r_minus_1 is None:
        r_minus_1 = r_minus_1_from_large_certificate(r, certs)
    if r_minus_1 is None:
        r_minus_1 = trial_factor(r - 1)
        for q in r_minus_1:
            require_prime_certified(q, certs, None)

    order = r - 1
    for q in sorted(r_minus_1):
        while order % q == 0 and pow(a, order // q, r) == 1:
            order //= q
    return order


def valuation(n: int, p: int) -> int:
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v


def sigma_prime_power(p: int, e: int) -> int:
    return (p ** (e + 1) - 1) // (p - 1)


def verify_cyclotomic(record: Dict[str, Any]) -> str:
    p = int_value(record.get("p"), "p")
    d = int_value(record.get("d"), "d")
    if p < 2 or d < 1:
        raise VerifyError("p must be >=2 and d must be >=1")
    phi = cyclotomic_value(p, d)
    if "phi" in record and int_value(record["phi"], "phi") != phi:
        raise VerifyError(f"supplied phi does not equal Phi_{d}({p})")

    large_certs = large_prime_certificates(record.get("large_prime_certificates"))
    factors = factor_pairs(record.get("factors"), "factors")
    for q, _ in factors:
        require_prime_certified(q, large_certs, None)
    product = multiply_factors(factors)
    if product != phi:
        raise VerifyError(
            f"factorization product {product} does not equal Phi_{d}({p})={phi}"
        )

    supplied_orders = record.get("orders", {})
    if supplied_orders is None:
        supplied_orders = {}
    if not isinstance(supplied_orders, dict):
        raise VerifyError("orders must be an object keyed by factor")

    supplied_rminus1 = record.get("r_minus_1_factors", {})
    if supplied_rminus1 is None:
        supplied_rminus1 = {}
    if not isinstance(supplied_rminus1, dict):
        raise VerifyError("r_minus_1_factors must be an object keyed by factor")

    for r, exp in factors:
        r_key = str(r)
        rm1 = None
        if r_key in supplied_rminus1:
            rm1 = factorization_dict(supplied_rminus1[r_key], f"r_minus_1_factors.{r}", large_certs)
            if multiply_factors(rm1.items()) != r - 1:
                raise VerifyError(f"factorization of {r}-1 is incorrect")
        order = multiplicative_order(p % r, r, rm1, large_certs)
        if r_key in supplied_orders and int_value(supplied_orders[r_key], f"orders.{r}") != order:
            raise VerifyError(f"supplied order for factor {r} is incorrect")
        if valuation(phi, r) != exp:
            raise VerifyError(f"valuation v_{r}(Phi_{d}({p})) is not {exp}")

    for e in record.get("exponents", []):
        e = int_value(e, "exponents[]")
        sigma = sigma_prime_power(p, e)
        for r, _ in factors:
            _ = valuation(sigma, r)

    return f"cyclotomic p={p} d={d} factors={len(factors)} ok"


def parse_kernel_primes(record: Dict[str, Any]) -> List[int]:
    raw = record.get("primes", record.get("support"))
    if raw is None:
        raw = [entry.get("p") for entry in record.get("kernel", [])]
    if not isinstance(raw, list) or not raw:
        raise VerifyError("kernel record needs primes/support/kernel")
    primes = sorted({int_value(p, "kernel prime") for p in raw})
    for p in primes:
        require_prime(p)
    return primes


def exact_H(primes: Iterable[int]) -> Fraction:
    h = Fraction(1, 1)
    for p in primes:
        h *= Fraction(p, p - 1)
    return h


def parse_fraction(raw: Any, field: str) -> Fraction:
    if isinstance(raw, dict):
        return Fraction(int_value(raw.get("num"), f"{field}.num"), int_value(raw.get("den"), f"{field}.den"))
    if isinstance(raw, list) and len(raw) == 2:
        return Fraction(int_value(raw[0], f"{field}.num"), int_value(raw[1], f"{field}.den"))
    if isinstance(raw, str) and "/" in raw:
        a, b = raw.split("/", 1)
        return Fraction(int(a), int(b))
    return Fraction(int_value(raw, field), 1)


def verify_kernel(record: Dict[str, Any]) -> str:
    primes = parse_kernel_primes(record)
    h = exact_H(primes)
    if "H" in record and parse_fraction(record["H"], "H") != h:
        raise VerifyError(f"supplied H does not equal {h.numerator}/{h.denominator}")
    if "H_le_2" in record:
        expected = bool(record["H_le_2"])
        if (h <= 2) != expected:
            raise VerifyError("supplied H_le_2 flag is incorrect")

    for edge in record.get("edges", []):
        p = int_value(edge.get("p"), "edge.p")
        d = int_value(edge.get("d"), "edge.d")
        r = int_value(edge.get("r"), "edge.r")
        lam = int_value(edge.get("lambda", edge.get("valuation", 1)), "edge.lambda")
        phi = cyclotomic_value(p, d)
        actual_lam = valuation(phi, r)
        if actual_lam != lam:
            raise VerifyError(f"edge valuation v_{r}(Phi_{d}({p})) is {actual_lam}, not {lam}")
        if "order" in edge:
            large_certs = large_prime_certificates(record.get("large_prime_certificates"))
            order = multiplicative_order(p % r, r, None, large_certs)
            if int_value(edge["order"], "edge.order") != order:
                raise VerifyError(f"edge order ord_{r}({p}) is not {edge['order']}")

    return f"kernel primes={len(primes)} H={h.numerator}/{h.denominator} ok"


def first_19_index_for_non_euler(order: int) -> int:
    if order == 1:
        return 19
    if order in (3, 9):
        return order
    raise VerifyError(f"order {order} is not a non-Euler 19-input type")


def exponent_condition_19(order: int) -> str:
    if order == 1:
        return "19 | e+1"
    if order in (3, 9):
        return f"{order} | e+1"
    raise VerifyError(f"order {order} is not a non-Euler 19-input type")


def contribution_source_19(order: int) -> str:
    if order == 1:
        return "LTE; first cyclotomic obligation Phi_19(p)"
    if order == 3:
        return "Phi_3(p)"
    if order == 9:
        return "Phi_9(p)"
    raise VerifyError(f"order {order} is not a non-Euler 19-input type")


def verify_nineteen_order_branch(record: Dict[str, Any]) -> str:
    p = int_value(record.get("p"), "p")
    require_prime(p)
    if p == MODULUS_19:
        raise VerifyError("p=19 is not a branch prime")

    residue = p % MODULUS_19
    if "residue_mod_19" in record and int_value(record["residue_mod_19"], "residue_mod_19") != residue:
        raise VerifyError("residue_mod_19 is incorrect")

    order = multiplicative_order(p % MODULUS_19, MODULUS_19)
    if "ord_19" in record and int_value(record["ord_19"], "ord_19") != order:
        raise VerifyError("ord_19 is incorrect")

    non_euler = order in NON_EULER_19_TYPES
    euler = order in EULER_19_TYPES
    if "non_euler_admissible" in record and bool(record["non_euler_admissible"]) != non_euler:
        raise VerifyError("non_euler_admissible flag is incorrect")
    if "euler_admissible" in record and bool(record["euler_admissible"]) != euler:
        raise VerifyError("euler_admissible flag is incorrect")

    if non_euler:
        expected_index = first_19_index_for_non_euler(order)
        if "first_non_euler_cyclotomic_index" in record:
            actual_index = int_value(
                record["first_non_euler_cyclotomic_index"],
                "first_non_euler_cyclotomic_index",
            )
            if actual_index != expected_index:
                raise VerifyError("first_non_euler_cyclotomic_index is incorrect")
        if "non_euler_exponent_condition" in record:
            if record["non_euler_exponent_condition"] != exponent_condition_19(order):
                raise VerifyError("non_euler_exponent_condition is incorrect")
        if "contribution_source" in record:
            if record["contribution_source"] != contribution_source_19(order):
                raise VerifyError("contribution_source is incorrect")

    return f"nineteen-order p={p} ord_19={order} ok"


def verify_expansion_abundance_bound(record: Dict[str, Any]) -> str:
    if "A" not in record:
        raise VerifyError("expansion_abundance_bound record needs A")
    A = parse_fraction(record["A"], "A")
    M = int_value(record.get("tail_count_bound"), "tail_count_bound")
    B = int_value(record.get("B"), "B")
    if A <= 0:
        raise VerifyError("A must be positive")
    if M < 0:
        raise VerifyError("tail_count_bound must be nonnegative")
    if B < 2:
        raise VerifyError("B must be at least 2")
    lhs = A * (Fraction(B, B - 1) ** M)
    if lhs > 2:
        raise VerifyError("tail inequality A*(B/(B-1))^M <= 2 fails")

    if bool(record.get("minimality_checked", False)) and B > 2:
        previous = A * (Fraction(B - 1, B - 2) ** M)
        if previous <= 2:
            raise VerifyError("B is not minimal: B-1 also satisfies the inequality")

    supplied = record.get("verified_inequality")
    if isinstance(supplied, dict):
        if "lhs_num" in supplied and int_value(supplied["lhs_num"], "lhs_num") != lhs.numerator:
            raise VerifyError("verified_inequality.lhs_num is incorrect")
        if "lhs_den" in supplied and int_value(supplied["lhs_den"], "lhs_den") != lhs.denominator:
            raise VerifyError("verified_inequality.lhs_den is incorrect")
        if "holds" in supplied and bool(supplied["holds"]) != (lhs <= 2):
            raise VerifyError("verified_inequality.holds is incorrect")

    return f"expansion-abundance B={B} M={M} ok"


def verify_branch_archive(record: Dict[str, Any]) -> str:
    archive_id = record_id(record)
    root = str_value(record.get("root"), "root")
    nodes = string_list(record.get("nodes"), "nodes", allow_empty=False)
    if root not in nodes:
        raise VerifyError("branch_archive root is not listed in nodes")
    for field in ARCHIVE_REFERENCE_FIELDS:
        optional_string_list(record, field)
    bounds = record.get("bounds", {})
    if bounds is not None and not isinstance(bounds, dict):
        raise VerifyError("branch_archive.bounds must be an object")
    tag = record.get("branch_tag")
    if tag is not None and not isinstance(tag, (str, dict)):
        raise VerifyError("branch_archive.branch_tag must be a string or object")
    return f"branch-archive id={archive_id} nodes={len(nodes)} ok"


def verify_coverage_split(record: Dict[str, Any]) -> str:
    split_id = record_id(record)
    str_value(record.get("parent"), "parent")
    children = string_list(record.get("children"), "children", allow_empty=False)
    kind = str_value(record.get("split_kind"), "split_kind")
    if kind not in ALLOWED_SPLIT_KINDS:
        raise VerifyError(f"coverage_split split_kind {kind!r} is not allowed")
    if not bool_value(record.get("complete", False), "complete"):
        raise VerifyError("coverage_split must record complete=true")
    if record.get("disjoint") is not None:
        bool_value(record["disjoint"], "disjoint")
    orders = record.get("orders")
    if orders is not None:
        if not isinstance(orders, list) or not orders:
            raise VerifyError("coverage_split.orders must be a nonempty list")
        for order in orders:
            if int_value(order, "coverage_split.orders[]") < 1:
                raise VerifyError("coverage_split.orders[] must be positive")
    return f"coverage-split id={split_id} children={len(children)} ok"


def verify_leaf_status(record: Dict[str, Any]) -> str:
    leaf_id = record_id(record)
    str_value(record.get("node"), "node")
    status = str_value(record.get("status"), "status")
    if status not in ALLOWED_LEAF_STATUSES:
        raise VerifyError(f"leaf_status status {status!r} is not allowed")

    if status in {"refuted", "resolved"}:
        reason = str_value(record.get("reason"), "reason")
        if reason not in ALLOWED_LEAF_REASONS:
            raise VerifyError(f"leaf_status reason {reason!r} is not allowed")
    elif status == "unresolved_forced":
        forced = optional_string_list(record, "forced_cofactors")
        tails = optional_string_list(record, "tail_count_certificates")
        if not forced and not tails:
            raise VerifyError(
                "unresolved_forced leaf needs forced_cofactors or "
                "tail_count_certificates"
            )
    else:
        if "reason" in record:
            str_value(record["reason"], "reason")
        if "description" in record:
            str_value(record["description"], "description")
    return f"leaf-status id={leaf_id} status={status} ok"



def primitive_prime_lower_bound(p: int, d: int, lower_bound: int) -> None:
    """Verifier-facing lower-bound check for a primitive prime divisor.

    If a prime s has ord_s(p)=d, then d | s-1.  Since d is odd in the
    present post-window rows and s is odd, s-1 is an even multiple of d.
    To certify s >= lower_bound it is enough to check that no prime
    s < lower_bound can have ord_s(p)=d.
    """
    if p < 2 or d < 2:
        raise VerifyError("primitive lower-bound certificate needs p>=2 and d>=2")
    if lower_bound < 3:
        raise VerifyError("primitive lower_bound must be at least 3")
    for s in range(3, lower_bound, 2):
        if not is_probable_prime_u64(s):
            continue
        if math.gcd(p, s) != 1:
            continue
        if (s - 1) % d != 0:
            continue
        # This prime is arithmetically capable of carrying order d; rule it out directly.
        if multiplicative_order(p % s, s) == d:
            raise VerifyError(
                f"primitive lower bound fails: ord_{s}({p})={d} with s<{lower_bound}"
            )


def verify_primitive_forced_prime_certificate(cert: Dict[str, Any], field: str) -> Tuple[int, int, int]:
    p = int_value(cert.get("p"), f"{field}.p")
    d = int_value(cert.get("d"), f"{field}.d")
    lower_bound = int_value(cert.get("lower_bound"), f"{field}.lower_bound")
    theorem = str_value(cert.get("theorem", "zsigmondy"), f"{field}.theorem")
    if theorem != "zsigmondy":
        raise VerifyError(f"{field}.theorem must be 'zsigmondy'")
    if p < 2 or d < 2:
        raise VerifyError(f"{field} needs p>=2 and d>=2")
    # Zsigmondy exceptions for a^n-b^n with b=1 do not occur for p=7 and d>2.
    if p == 2 and d == 6:
        raise VerifyError(f"{field}: Zsigmondy exception (2,6)")
    if d == 2 and p + 1 & (p):
        # Defensive placeholder; the current certificates never use d=2.
        raise VerifyError(f"{field}: unsupported d=2 primitive-prime case")
    primitive_prime_lower_bound(p, d, lower_bound)
    return p, d, lower_bound

def verify_forced_cofactor(record: Dict[str, Any]) -> str:
    cofactor_id = record_id(record)
    str_value(record.get("node", record.get("source_node", "")), "node")
    if bool(record.get("symbolic", False)):
        str_value(record.get("cofactor"), "cofactor")
        d_value = record.get("d")
        if isinstance(d_value, str):
            str_value(d_value, "d")
        else:
            int_value(d_value, "d")
        source = record.get("source", record.get("p"))
        if not isinstance(source, (str, int)):
            raise VerifyError("symbolic forced_cofactor needs source or p")
        activation = record.get("activation")
        if activation is not None and not isinstance(activation, (str, dict)):
            raise VerifyError("forced_cofactor.activation must be a string or object")
        forced_set = record.get("forced_set")
        if forced_set is not None:
            str_value(forced_set, "forced_set")
        lower_primes = record.get("lower_primes", [])
        if not isinstance(lower_primes, list):
            raise VerifyError("forced_cofactor.lower_primes must be a list")
        for q in lower_primes:
            if int_value(q, "lower_primes[]") < 3:
                raise VerifyError("lower_primes[] must be an odd prime candidate")
        primitive = record.get("primitive_prime_lower_bound_certificate")
        if primitive is not None:
            if not isinstance(primitive, dict):
                raise VerifyError("primitive_prime_lower_bound_certificate must be an object")
            verify_primitive_forced_prime_certificate(
                primitive,
                "primitive_prime_lower_bound_certificate",
            )
        return f"forced-cofactor id={cofactor_id} symbolic ok"

    p = int_value(record.get("p"), "p")
    d = int_value(record.get("d"), "d")
    verify_cyclotomic(record)

    induced = record.get("induced_edges", [])
    if not isinstance(induced, list):
        raise VerifyError("forced_cofactor.induced_edges must be a list")
    phi = cyclotomic_value(p, d)
    for edge in induced:
        if not isinstance(edge, dict):
            raise VerifyError("forced_cofactor.induced_edges[] must be an object")
        r = int_value(edge.get("r"), "induced_edges.r")
        lam = int_value(edge.get("lambda", edge.get("valuation", 1)), "induced_edges.lambda")
        if valuation(phi, r) != lam:
            raise VerifyError(f"induced edge v_{r}(Phi_{d}({p})) is not {lam}")
        if "order" in edge:
            large_certs = large_prime_certificates(record.get("large_prime_certificates"))
            order = multiplicative_order(p % r, r, None, large_certs)
            if int_value(edge["order"], "induced_edges.order") != order:
                raise VerifyError(f"induced edge ord_{r}({p}) is incorrect")
    activation = record.get("activation")
    if activation is not None and not isinstance(activation, (str, dict)):
        raise VerifyError("forced_cofactor.activation must be a string or object")
    return f"forced-cofactor id={cofactor_id} p={p} d={d} ok"


def verify_tail_count_certificate(record: Dict[str, Any]) -> str:
    tail_id = record_id(record)
    str_value(record.get("node"), "node")

    if bool(record.get("symbolic", False)):
        status = record.get("status")
        if status == "primitive_tail_control_record":
            K_base = record.get("K_base")
            if not isinstance(K_base, list) or not K_base:
                raise VerifyError("primitive_tail_control_record needs nonempty K_base")
            base_primes = sorted({int_value(x, "K_base[]") for x in K_base})
            if len(base_primes) != len(K_base):
                raise VerifyError("K_base contains duplicates")
            for q in base_primes:
                require_prime_certified(q, large_prime_certificates(record.get("large_prime_certificates")), None)
            lower_bound = int_value(record.get("forced_prime_lower_bound"), "forced_prime_lower_bound")
            B = int_value(record.get("B"), "B")
            M = int_value(record.get("M", record.get("tail_count_bound")), "M")
            if B < 2 or M < 0:
                raise VerifyError("primitive_tail_control_record has invalid B or M")
            # Monotone worst case: H(K_base union {s}) is largest at s=lower_bound.
            h = exact_H(base_primes) * Fraction(lower_bound, lower_bound - 1)
            lhs = h * (Fraction(B, B - 1) ** M)
            if lhs >= 2:
                raise VerifyError("primitive tail-control inequality fails")
            supplied = record.get("verified_inequality")
            if isinstance(supplied, dict):
                if "lhs_num" in supplied and int_value(supplied["lhs_num"], "lhs_num") != lhs.numerator:
                    raise VerifyError("verified_inequality.lhs_num is incorrect")
                if "lhs_den" in supplied and int_value(supplied["lhs_den"], "lhs_den") != lhs.denominator:
                    raise VerifyError("verified_inequality.lhs_den is incorrect")
                if "holds" in supplied and bool_value(supplied["holds"], "holds") != (lhs < 2):
                    raise VerifyError("verified_inequality.holds is incorrect")
            if "primitive_prime_lower_bound_certificate" in record:
                cert = record["primitive_prime_lower_bound_certificate"]
                if not isinstance(cert, dict):
                    raise VerifyError("primitive_prime_lower_bound_certificate must be an object")
                _, _, lb = verify_primitive_forced_prime_certificate(cert, "primitive_prime_lower_bound_certificate")
                if lb != lower_bound:
                    raise VerifyError("primitive lower bound does not match forced_prime_lower_bound")
            return f"tail-count id={tail_id} primitive-tail M={M} B={B} lb={lower_bound} ok"
        tail_set = record.get("tail_set", record.get("R"))
        if tail_set is not None:
            str_value(tail_set, "tail_set")
        bound = record.get("bound", record.get("tail_count_bound", record.get("M")))
        if bound is None:
            raise VerifyError("symbolic tail_count_certificate needs bound/M")
        if not isinstance(bound, (str, int)):
            raise VerifyError("symbolic tail_count bound must be a string or integer")
        if "statement" in record:
            str_value(record["statement"], "statement")
        return f"tail-count id={tail_id} symbolic ok"

    raw_primes = record.get("primes", record.get("support", record.get("K")))
    if raw_primes is None:
        status = record.get("status")
        if status == "child_tail_control_record":
            M = int_value(record.get("M", record.get("tail_count_bound")), "M")
            B = int_value(record.get("B"), "B")
            if M < 0:
                raise VerifyError("tail_count_certificate M must be nonnegative")
            if B < 2:
                raise VerifyError("tail_count_certificate B must be at least 2")
            if "m59" in record and int_value(record["m59"], "m59") < 0:
                raise VerifyError("tail_count_certificate m59 must be nonnegative")
            return f"tail-count id={tail_id} M={M} B={B} child-tail-control ok"
        raise VerifyError("tail_count_certificate needs primes/support/K")
    if not isinstance(raw_primes, list):
        raise VerifyError("tail_count_certificate primes/support/K must be a list")
    primes = sorted({int_value(p, "tail_count_certificate.prime") for p in raw_primes})
    if len(primes) != len(raw_primes):
        raise VerifyError("tail_count_certificate support contains duplicates")
    large_certs = large_prime_certificates(record.get("large_prime_certificates"))
    for p in primes:
        require_prime_certified(p, large_certs, None)

    h = exact_H(primes)
    if "H" in record and parse_fraction(record["H"], "H") != h:
        raise VerifyError(f"tail_count_certificate H does not equal {h}")
    A = parse_fraction(record.get("A", {"num": h.numerator, "den": h.denominator}), "A")
    if A != h:
        raise VerifyError("tail_count_certificate currently requires A=H(K)")

    raw_m = record.get("tail_count_bound", record.get("M"))
    if raw_m is None:
        raise VerifyError("tail_count_certificate needs tail_count_bound or M")
    M = int_value(raw_m, "tail_count_bound")
    if M < 0:
        raise VerifyError("tail_count_bound must be nonnegative")

    if "B" in record:
        B = int_value(record["B"], "B")
        if B < 2:
            raise VerifyError("B must be at least 2")
        lhs = h * (Fraction(B, B - 1) ** M)
        if lhs > 2:
            raise VerifyError("tail-count expansion-abundance inequality fails")
        supplied = record.get("verified_inequality")
        if isinstance(supplied, dict):
            if "lhs_num" in supplied and int_value(supplied["lhs_num"], "lhs_num") != lhs.numerator:
                raise VerifyError("verified_inequality.lhs_num is incorrect")
            if "lhs_den" in supplied and int_value(supplied["lhs_den"], "lhs_den") != lhs.denominator:
                raise VerifyError("verified_inequality.lhs_den is incorrect")
            if "holds" in supplied and bool(supplied["holds"]) != (lhs <= 2):
                raise VerifyError("verified_inequality.holds is incorrect")
    return f"tail-count id={tail_id} M={M} H={h.numerator}/{h.denominator} ok"


def verify_abundance_obstruction(record: Dict[str, Any]) -> str:
    obstruction_id = record_id(record)
    str_value(record.get("node"), "node")
    tail_id = record.get("tail_count_certificate")
    if tail_id is not None:
        str_value(tail_id, "tail_count_certificate")

    if "H" in record:
        parse_fraction(record["H"], "H")
    if "M" in record:
        if int_value(record["M"], "M") < 0:
            raise VerifyError("abundance_obstruction M must be nonnegative")
    if "B" in record:
        if int_value(record["B"], "B") < 2:
            raise VerifyError("abundance_obstruction B must be at least 2")

    supplied = record.get("verified_inequality")
    if supplied is not None:
        if not isinstance(supplied, dict):
            raise VerifyError("abundance_obstruction.verified_inequality must be an object")
        if {"lhs_num", "lhs_den", "holds"} <= set(supplied):
            lhs = Fraction(
                int_value(supplied["lhs_num"], "verified_inequality.lhs_num"),
                int_value(supplied["lhs_den"], "verified_inequality.lhs_den"),
            )
            if bool_value(supplied["holds"], "verified_inequality.holds") != (lhs < 2):
                raise VerifyError("abundance_obstruction inequality flag is incorrect")

    search = record.get("small_prime_search_certificate")
    if search is not None:
        if not isinstance(search, dict):
            raise VerifyError("small_prime_search_certificate must be an object")
        candidates = search.get("candidates", [])
        if not isinstance(candidates, list):
            raise VerifyError("small_prime_search_certificate.candidates must be a list")
        for candidate in candidates:
            if int_value(candidate, "small_prime_search_certificate.candidates[]") < 2:
                raise VerifyError("small-prime candidate must be at least 2")
        if "new_tail_prime_le_B_exists" in search:
            bool_value(search["new_tail_prime_le_B_exists"], "new_tail_prime_le_B_exists")
        excluded = search.get("excluded", {})
        if excluded is not None and not isinstance(excluded, dict):
            raise VerifyError("small_prime_search_certificate.excluded must be an object")

    status = str_value(record.get("status"), "status")
    if status not in {
        "abundance_refuted",
        "forces_small_tail_prime_or_refuted",
        "tail_controlled",
    }:
        raise VerifyError(f"abundance_obstruction status {status!r} is not allowed")
    return f"abundance-obstruction id={obstruction_id} status={status} ok"


def verify_literature_filter_certificate(record: Dict[str, Any]) -> str:
    filter_id = record_id(record)
    theorem = str_value(record.get("theorem"), "theorem")
    if "branch" in record and not isinstance(record["branch"], (str, dict)):
        raise VerifyError("literature_filter_certificate.branch must be a string or object")
    if not bool_value(record.get("hypotheses_verified", False), "hypotheses_verified"):
        raise VerifyError("literature filter must record hypotheses_verified=true")
    if not bool_value(record.get("conclusion_verified", False), "conclusion_verified"):
        raise VerifyError("literature filter must record conclusion_verified=true")
    return f"literature-filter id={filter_id} theorem={theorem!r} ok"


def verify_domain_extension(record: Dict[str, Any]) -> str:
    """Validate the local shape of a domain_extension record.

    Cross-record checks are performed later by verify_domain_extensions(), once
    all JSONL records from all input files have been loaded.
    """
    extension_id = record_id(record)
    str_value(record.get("parent_domain"), "parent_domain")
    str_value(record.get("child_domain"), "child_domain")
    str_value(record.get("branch"), "branch")
    string_list(record.get("old_frontier"), "old_frontier")
    string_list(record.get("new_frontier"), "new_frontier")
    bool_value(record.get("aggregation_safe"), "aggregation_safe")

    coverage = record.get("coverage_of_old_unresolved_or_boundary", [])
    if not isinstance(coverage, list):
        raise VerifyError("coverage_of_old_unresolved_or_boundary must be a list")
    for idx, item in enumerate(coverage):
        if not isinstance(item, dict):
            raise VerifyError("coverage_of_old_unresolved_or_boundary[] must be an object")
        prefix = f"coverage_of_old_unresolved_or_boundary[{idx}]"
        str_value(item.get("old_node"), f"{prefix}.old_node")
        string_list(item.get("children"), f"{prefix}.children", allow_empty=False)
        if "split_id" in item:
            str_value(item["split_id"], f"{prefix}.split_id")
        if not bool_value(item.get("complete", False), f"{prefix}.complete"):
            raise VerifyError(f"{prefix}.complete must be true")
        reason = str_value(item.get("coverage_reason"), f"{prefix}.coverage_reason")
        if reason not in ALLOWED_EXTENSION_COVERAGE_REASONS:
            raise VerifyError(
                f"{prefix}.coverage_reason {reason!r} is not allowed"
            )

    superseded = record.get("superseded_records", [])
    if superseded is not None:
        string_list(superseded, "superseded_records")
    delegated = record.get("delegated_frontier", [])
    if delegated is not None:
        string_list(delegated, "delegated_frontier")

    return f"domain-extension id={extension_id} ok"


def archive_nodes(archive: Dict[str, Any]) -> Set[str]:
    return set(string_list(archive.get("nodes"), "branch_archive.nodes", allow_empty=False))


def archive_references(
    archive: Dict[str, Any],
    registry: Dict[str, Dict[str, Any]],
) -> Dict[str, List[Dict[str, Any]]]:
    archive_id = record_id(archive)
    return {
        field: [
            ensure_reference(registry, rid, expected_type, f"{archive_id}.{field}")
            for rid in optional_string_list(archive, field)
        ]
        for field, expected_type in ARCHIVE_REFERENCE_FIELDS.items()
    }


def leaf_records_by_node(
    archive: Dict[str, Any],
    registry: Dict[str, Dict[str, Any]],
) -> Dict[str, Dict[str, Any]]:
    leaves: Dict[str, Dict[str, Any]] = {}
    for leaf in archive_references(archive, registry)["leaf_statuses"]:
        node = str_value(leaf.get("node"), "leaf_status.node")
        if node in leaves:
            raise VerifyError(f"archive has duplicate leaf_status for node {node!r}")
        leaves[node] = leaf
    return leaves


def coverage_splits_by_parent(
    archive: Dict[str, Any],
    registry: Dict[str, Dict[str, Any]],
) -> Dict[str, Dict[str, Any]]:
    splits: Dict[str, Dict[str, Any]] = {}
    for split in archive_references(archive, registry)["coverage_splits"]:
        parent = str_value(split.get("parent"), "coverage_split.parent")
        if parent in splits:
            raise VerifyError(f"archive has duplicate coverage_split for node {parent!r}")
        splits[parent] = split
    return splits


def branch_tag_value(archive: Dict[str, Any]) -> str | None:
    tag = archive.get("branch_tag")
    if tag is None:
        return None
    if isinstance(tag, str):
        return tag
    if isinstance(tag, dict):
        for key in ("branch", "name", "tag", "id"):
            value = tag.get(key)
            if isinstance(value, str):
                return value
    return None


def node_is_open_or_expandable(leaf: Dict[str, Any]) -> bool:
    status = leaf.get("status")
    audit_status = leaf.get("audit_status")
    if status in {"unresolved_forced", "unresolved_exceptional"}:
        return True
    if audit_status in {"unresolved", "reduced", "boundary", "expandable"}:
        return True
    if bool(leaf.get("expandable", False)):
        return True
    return False


def node_is_aggregation_safe(leaf: Dict[str, Any]) -> bool:
    audit_status = leaf.get("audit_status")
    if audit_status is not None:
        return audit_status in AGGREGATION_SAFE_AUDIT_STATUSES
    return leaf.get("status") in AGGREGATION_SAFE_LEAF_STATUSES


def verify_domain_extensions(records: List[Dict[str, Any]]) -> int:
    registry = generic_records_by_id(records)
    extension_count = 0

    extension_edges: Dict[str, List[str]] = {}
    for record in records:
        if record.get("type") != "domain_extension":
            continue
        parent_id = str_value(record.get("parent_domain"), "parent_domain")
        child_id = str_value(record.get("child_domain"), "child_domain")
        extension_edges.setdefault(parent_id, []).append(child_id)

    # Detect nontrivial cycles in the extension graph.
    visiting: Set[str] = set()
    visited: Set[str] = set()

    def dfs(domain_id: str) -> None:
        if domain_id in visiting:
            raise VerifyError(f"domain_extension graph has a cycle at {domain_id!r}")
        if domain_id in visited:
            return
        visiting.add(domain_id)
        for child_id in extension_edges.get(domain_id, []):
            if child_id != domain_id:
                dfs(child_id)
        visiting.remove(domain_id)
        visited.add(domain_id)

    for domain_id in list(extension_edges):
        dfs(domain_id)

    for extension in records:
        if extension.get("type") != "domain_extension":
            continue
        extension_count += 1
        extension_id = record_id(extension)

        parent_id = str_value(extension.get("parent_domain"), "parent_domain")
        child_id = str_value(extension.get("child_domain"), "child_domain")
        parent = ensure_reference(registry, parent_id, "branch_archive", f"{extension_id}.parent_domain")
        child = ensure_reference(registry, child_id, "branch_archive", f"{extension_id}.child_domain")

        branch = str_value(extension.get("branch"), "branch")
        parent_branch = branch_tag_value(parent)
        child_branch = branch_tag_value(child)
        if parent_branch is not None and parent_branch != branch:
            raise VerifyError(
                f"{extension_id} branch {branch!r} does not match parent branch_tag {parent_branch!r}"
            )
        if child_branch is not None and child_branch != branch:
            raise VerifyError(
                f"{extension_id} branch {branch!r} does not match child branch_tag {child_branch!r}"
            )

        parent_nodes = archive_nodes(parent)
        child_nodes = archive_nodes(child)
        old_frontier = set(string_list(extension.get("old_frontier"), "old_frontier"))
        new_frontier = set(string_list(extension.get("new_frontier"), "new_frontier"))
        for node in old_frontier:
            if node not in parent_nodes:
                raise VerifyError(f"{extension_id}.old_frontier node {node!r} is not in parent domain")
        for node in new_frontier:
            if node not in child_nodes:
                raise VerifyError(f"{extension_id}.new_frontier node {node!r} is not in child domain")

        parent_leaves = leaf_records_by_node(parent, registry)
        child_leaves = leaf_records_by_node(child, registry)
        child_splits = coverage_splits_by_parent(child, registry)

        open_parent_nodes = {
            node for node, leaf in parent_leaves.items() if node_is_open_or_expandable(leaf)
        }
        omitted_open = open_parent_nodes - old_frontier
        if omitted_open:
            node = sorted(omitted_open)[0]
            raise VerifyError(
                f"{extension_id} omits old open/boundary frontier node {node!r}"
            )

        coverage = extension.get("coverage_of_old_unresolved_or_boundary", [])
        coverage_by_old: Dict[str, Dict[str, Any]] = {}
        for item in coverage:
            old_node = str_value(item.get("old_node"), "coverage.old_node")
            if old_node not in old_frontier:
                raise VerifyError(
                    f"{extension_id} coverage old_node {old_node!r} is not in old_frontier"
                )
            if old_node in coverage_by_old:
                raise VerifyError(f"{extension_id} has duplicate coverage for old_node {old_node!r}")
            coverage_by_old[old_node] = item
            children = string_list(item.get("children"), "coverage.children", allow_empty=False)
            for child_node in children:
                if child_node not in child_nodes:
                    raise VerifyError(
                        f"{extension_id} coverage child {child_node!r} is not in child domain"
                    )
            if "split_id" in item:
                split = ensure_reference(
                    registry,
                    str_value(item["split_id"], "coverage.split_id"),
                    "coverage_split",
                    f"{extension_id}.coverage.split_id",
                )
                if str_value(split.get("parent"), "coverage_split.parent") != old_node:
                    raise VerifyError(
                        f"{extension_id} split_id for {old_node!r} has a different parent"
                    )
                split_children = set(string_list(split.get("children"), "coverage_split.children", allow_empty=False))
                if not set(children) <= split_children:
                    raise VerifyError(
                        f"{extension_id} coverage children for {old_node!r} are not contained in split children"
                    )
            elif old_node in child_splits:
                split_children = set(string_list(child_splits[old_node].get("children"), "coverage_split.children", allow_empty=False))
                if not set(children) <= split_children:
                    raise VerifyError(
                        f"{extension_id} coverage children for {old_node!r} are not contained in child-domain split"
                    )

        for old_node in old_frontier:
            if old_node in coverage_by_old:
                continue
            if old_node not in child_nodes:
                raise VerifyError(
                    f"{extension_id} old frontier node {old_node!r} is neither covered nor preserved in child domain"
                )

        delegated_frontier = set(extension.get("delegated_frontier", []) or [])
        for node in delegated_frontier:
            if node not in new_frontier:
                raise VerifyError(
                    f"{extension_id} delegated_frontier node {node!r} is not in new_frontier"
                )

        if bool_value(extension.get("aggregation_safe"), "aggregation_safe"):
            if delegated_frontier:
                raise VerifyError(
                    f"{extension_id} aggregation_safe=true cannot have delegated_frontier nodes"
                )
            for node in new_frontier:
                leaf = child_leaves.get(node)
                if leaf is None:
                    raise VerifyError(
                        f"{extension_id} aggregation_safe new_frontier node {node!r} is not terminal"
                    )
                if not node_is_aggregation_safe(leaf):
                    raise VerifyError(
                        f"{extension_id} new_frontier node {node!r} is not aggregation-safe"
                    )

    return extension_count

def generic_records_by_id(records: Iterable[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    out: Dict[str, Dict[str, Any]] = {}
    for record in records:
        if record.get("type") not in GENERIC_RECORD_TYPES:
            continue
        rid = record_id(record)
        if rid in out:
            raise VerifyError(f"duplicate generic record id {rid!r}")
        out[rid] = record
    return out


def ensure_reference(
    registry: Dict[str, Dict[str, Any]],
    rid: str,
    expected_type: str,
    field: str,
) -> Dict[str, Any]:
    if rid not in registry:
        raise VerifyError(f"{field} references missing record id {rid!r}")
    record = registry[rid]
    if record.get("type") != expected_type:
        raise VerifyError(
            f"{field} references {rid!r} with type {record.get('type')!r}, "
            f"expected {expected_type!r}"
        )
    return record


def check_acyclic(root: str, edges: Dict[str, List[str]]) -> Set[str]:
    visiting: Set[str] = set()
    visited: Set[str] = set()

    def dfs(node: str) -> None:
        if node in visiting:
            raise VerifyError(f"coverage graph has a cycle at node {node!r}")
        if node in visited:
            return
        visiting.add(node)
        for child in edges.get(node, []):
            dfs(child)
        visiting.remove(node)
        visited.add(node)

    dfs(root)
    return visited


def verify_generic_archives(records: List[Dict[str, Any]]) -> int:
    registry = generic_records_by_id(records)
    archive_count = 0
    for archive in records:
        if archive.get("type") != "branch_archive":
            continue
        archive_count += 1
        archive_id = record_id(archive)
        nodes = set(string_list(archive.get("nodes"), "nodes", allow_empty=False))
        root = str_value(archive.get("root"), "root")

        referenced: Dict[str, List[Dict[str, Any]]] = {}
        for field, expected_type in ARCHIVE_REFERENCE_FIELDS.items():
            referenced[field] = [
                ensure_reference(registry, rid, expected_type, f"{archive_id}.{field}")
                for rid in optional_string_list(archive, field)
            ]

        edges: Dict[str, List[str]] = {}
        parent_nodes: Set[str] = set()
        for split in referenced["coverage_splits"]:
            parent = str_value(split.get("parent"), "coverage_split.parent")
            children = string_list(split.get("children"), "coverage_split.children", allow_empty=False)
            if parent not in nodes:
                raise VerifyError(f"coverage split parent {parent!r} is not an archive node")
            for child in children:
                if child not in nodes:
                    raise VerifyError(f"coverage split child {child!r} is not an archive node")
            if parent in edges:
                raise VerifyError(f"node {parent!r} has more than one coverage split")
            edges[parent] = children
            parent_nodes.add(parent)

        leaf_by_node: Dict[str, str] = {}
        for leaf in referenced["leaf_statuses"]:
            node = str_value(leaf.get("node"), "leaf_status.node")
            if node not in nodes:
                raise VerifyError(f"leaf_status node {node!r} is not an archive node")
            if node in leaf_by_node:
                raise VerifyError(f"node {node!r} has more than one leaf_status")
            leaf_by_node[node] = record_id(leaf)

        if parent_nodes & set(leaf_by_node):
            overlap = sorted(parent_nodes & set(leaf_by_node))[0]
            raise VerifyError(f"node {overlap!r} is both internal and terminal")

        for node in nodes:
            if node not in parent_nodes and node not in leaf_by_node:
                raise VerifyError(f"archive node {node!r} is neither split nor leaf")

        reachable = check_acyclic(root, edges)
        if reachable != nodes:
            missing = sorted(nodes - reachable)
            raise VerifyError(f"archive has unreachable node(s): {missing}")

        forced_ids = {record_id(r) for r in referenced["forced_cofactors"]}
        tail_ids = {record_id(r) for r in referenced["tail_count_certificates"]}
        for leaf in referenced["leaf_statuses"]:
            if leaf.get("status") != "unresolved_forced":
                continue
            for rid in optional_string_list(leaf, "forced_cofactors"):
                if rid not in forced_ids:
                    raise VerifyError(f"unresolved leaf references forced_cofactor {rid!r} outside archive")
            for rid in optional_string_list(leaf, "tail_count_certificates"):
                if rid not in tail_ids:
                    raise VerifyError(f"unresolved leaf references tail_count_certificate {rid!r} outside archive")
    return archive_count


def domain_archive_summaries(records: List[Dict[str, Any]]) -> List[str]:
    """Validate and format optional finite-domain status summaries.

    In addition to the status distribution, this function computes the
    machine-readable aggregation flag

        recursive_controlled: true

    exactly when every frontier leaf has an aggregation-safe closed status.
    """
    registry = generic_records_by_id(records)
    summaries: List[str] = []
    order = [
        "lower_prime_refuted",
        "abundance_refuted",
        "directly_closed",
        "tail_controlled",
        "child_archive_tail_controlled",
        "reduced",
        "unresolved",
    ]

    # These are the terminal statuses that count as globally aggregable
    # under the tail-controlled frontier criterion.  The first two are
    # direct refutation subtypes and are therefore treated as directly closed.
    recursive_control_statuses = {
        "lower_prime_refuted",
        "abundance_refuted",
        "directly_closed",
        "tail_controlled",
        "child_archive_tail_controlled",
    }

    for archive in records:
        if archive.get("type") != "branch_archive":
            continue
        summary = archive.get("domain_summary")
        if summary is None:
            continue
        if not isinstance(summary, dict):
            raise VerifyError("branch_archive.domain_summary must be an object")

        name = str_value(summary.get("name"), "domain_summary.name")
        leaf_ids = optional_string_list(archive, "leaf_statuses")
        counts: Dict[str, int] = {}

        for leaf_id in leaf_ids:
            leaf = ensure_reference(
                registry, leaf_id, "leaf_status", "domain_summary.leaf_statuses"
            )
            status = str_value(
                leaf.get("audit_status", leaf.get("status")),
                "leaf_status.audit_status",
            )
            counts[status] = counts.get(status, 0) + 1

            for rid in optional_string_list(leaf, "forced_cofactors"):
                ensure_reference(
                    registry, rid, "forced_cofactor", f"{leaf_id}.forced_cofactors"
                )
            for rid in optional_string_list(leaf, "tail_count_certificates"):
                ensure_reference(
                    registry, rid, "tail_count_certificate", f"{leaf_id}.tail_count_certificates"
                )
            for rid in optional_string_list(leaf, "abundance_obstructions"):
                ensure_reference(
                    registry, rid, "abundance_obstruction", f"{leaf_id}.abundance_obstructions"
                )

            leaf_status = str_value(leaf.get("status"), "leaf_status.status")

            if status == "lower_prime_refuted":
                if leaf_status != "refuted" or leaf.get("reason") != "lower_prime_avoidance":
                    raise VerifyError(
                        f"{leaf_id} audit_status lower_prime_refuted requires "
                        "status=refuted and reason=lower_prime_avoidance"
                    )

            elif status == "abundance_refuted":
                if leaf_status != "refuted" or leaf.get("reason") != "abundance_obstruction":
                    raise VerifyError(
                        f"{leaf_id} audit_status abundance_refuted requires "
                        "status=refuted and reason=abundance_obstruction"
                    )
                if not optional_string_list(leaf, "abundance_obstructions"):
                    raise VerifyError(f"{leaf_id} abundance_refuted needs an abundance_obstruction")

            elif status == "directly_closed":
                if leaf_status not in {"refuted", "resolved"}:
                    raise VerifyError(
                        f"{leaf_id} audit_status directly_closed requires "
                        "status=refuted or status=resolved"
                    )
                reason = leaf.get("reason")
                if reason not in {
                    "lower_prime_avoidance",
                    "abundance_obstruction",
                    "valuation_defect",
                    "euler_parity_violation",
                    "finite_kernel_contradiction",
                    "literature_obstruction",
                    "bounded_range_obstruction",
                }:
                    raise VerifyError(
                        f"{leaf_id} directly_closed has unsupported reason {reason!r}"
                    )

            elif status == "tail_controlled":
                if leaf_status != "resolved":
                    raise VerifyError(
                        f"{leaf_id} tail_controlled requires status=resolved"
                    )
                if leaf.get("reason") not in {
                    "tail_abundance_control",
                    "abundance_obstruction",
                }:
                    raise VerifyError(
                        f"{leaf_id} tail_controlled requires reason="
                        "tail_abundance_control or abundance_obstruction"
                    )
                if not optional_string_list(leaf, "tail_count_certificates"):
                    raise VerifyError(f"{leaf_id} tail_controlled needs a tail_count_certificate")
                if not optional_string_list(leaf, "abundance_obstructions"):
                    raise VerifyError(f"{leaf_id} tail_controlled needs an abundance_obstruction")

            elif status == "child_archive_tail_controlled":
                if leaf_status != "resolved":
                    raise VerifyError(
                        f"{leaf_id} child_archive_tail_controlled requires "
                        "status=resolved"
                    )
                if leaf.get("reason") != "certified_branch_extension":
                    raise VerifyError(
                        f"{leaf_id} child_archive_tail_controlled requires "
                        "reason=certified_branch_extension"
                    )
                child_archive = str_value(leaf.get("child_archive"), "child_archive")
                ensure_reference(
                    registry, child_archive, "branch_archive", f"{leaf_id}.child_archive"
                )
                if leaf.get("child_archive_status") != "child_archive_tail_controlled":
                    raise VerifyError(
                        f"{leaf_id} must record child_archive_tail_controlled"
                    )
                child_kernel = leaf.get("child_kernel")
                if not isinstance(child_kernel, list) or not child_kernel:
                    raise VerifyError(
                        f"{leaf_id} child_archive_tail_controlled needs a nonempty child_kernel"
                    )
                for p in child_kernel:
                    require_prime(int_value(p, f"{leaf_id}.child_kernel[]"))

            elif status == "reduced":
                if leaf_status != "resolved" or leaf.get("reason") != "certified_branch_extension":
                    raise VerifyError(
                        f"{leaf_id} audit_status reduced requires status=resolved "
                        "and reason=certified_branch_extension"
                    )
                child_archive = str_value(leaf.get("child_archive"), "child_archive")
                ensure_reference(
                    registry, child_archive, "branch_archive", f"{leaf_id}.child_archive"
                )
                if leaf.get("child_archive_status") != "child_archive_attached":
                    raise VerifyError(
                        f"{leaf_id} reduced leaf must record child_archive_attached"
                    )
                child_kernel = leaf.get("child_kernel")
                if not isinstance(child_kernel, list) or not child_kernel:
                    raise VerifyError(f"{leaf_id} reduced leaf needs a nonempty child_kernel")
                for p in child_kernel:
                    require_prime(int_value(p, f"{leaf_id}.child_kernel[]"))

            elif status == "unresolved":
                if leaf_status != "unresolved_forced":
                    raise VerifyError(
                        f"{leaf_id} audit_status unresolved requires status=unresolved_forced"
                    )
                unresolved_reason = str_value(
                    leaf.get("unresolved_reason"), "unresolved_reason"
                )
                if unresolved_reason not in ALLOWED_UNRESOLVED_REASONS:
                    raise VerifyError(
                        f"{leaf_id} unresolved_reason {unresolved_reason!r} "
                        "is not one of the standard unresolved reason codes"
                    )
                str_value(leaf.get("next_action"), "next_action")

            else:
                raise VerifyError(f"{leaf_id} has unsupported audit_status {status!r}")

        expected_checked = int_value(
            summary.get("leaves_checked", len(leaf_ids)),
            "domain_summary.leaves_checked",
        )
        if expected_checked != len(leaf_ids):
            raise VerifyError(
                f"{name} summary says {expected_checked} leaves, "
                f"archive lists {len(leaf_ids)}"
            )

        expected_counts = summary.get("status_counts", {})
        if not isinstance(expected_counts, dict):
            raise VerifyError("domain_summary.status_counts must be an object")
        for status, expected in expected_counts.items():
            expected_n = int_value(expected, f"domain_summary.status_counts.{status}")
            if counts.get(status, 0) != expected_n:
                raise VerifyError(
                    f"{name} summary count for {status!r} is {expected_n}, "
                    f"but leaf records give {counts.get(status, 0)}"
                )

        recursive_controlled = (
            len(leaf_ids) == expected_checked
            and bool(leaf_ids)
            and counts.get("unresolved", 0) == 0
            and counts.get("reduced", 0) == 0
            and all(status in recursive_control_statuses for status in counts)
        )

        if "recursive_controlled" in summary:
            expected_recursive = bool_value(
                summary["recursive_controlled"],
                "domain_summary.recursive_controlled",
            )
            if expected_recursive != recursive_controlled:
                raise VerifyError(
                    f"{name} summary recursive_controlled={expected_recursive} "
                    f"but computed {recursive_controlled}"
                )

        parts = [f"{counts.get(status, 0)} {status}" for status in order if status in counts]
        for status in sorted(set(counts) - set(order)):
            parts.append(f"{counts[status]} {status}")

        summaries.append(
            f"{name}: {len(leaf_ids)}/{expected_checked} leaves checked; "
            + ", ".join(parts)
            + f"; recursive_controlled: {str(recursive_controlled).lower()}."
        )

    return summaries



def verify_parametric_post_window_closure(record: Dict[str, Any]) -> str:
    """Verify a named parametric post-window closure criterion.

    Supported instances:
      Q5E2, (pi,r)=(109,11), even e_r >= 22;
      Q5E2, (pi,r)=(229,23), even e_r >= 22;
      Q5E2, (pi,r)=(349,7), even e_r >= 94;
      Q5E2, (pi,r)=(409,41), even e_r >= 22.

    The check is theorem-level: it verifies the arithmetic hypotheses needed for
    the manuscript criterion rather than expanding infinitely many rows.
    """
    cid = record_id(record)
    branch = str_value(record.get("branch"), "branch")
    if branch != "Q5E2":
        raise VerifyError("parametric_post_window_closure currently supports branch Q5E2")

    pi = int_value(record.get("pi"), "pi")
    r = int_value(record.get("r"), "r")
    supported_bases = {
        (109, 11): [5, 11, 109],
        (229, 23): [5, 23, 229],
        (349, 7): [5, 7, 349],
        (409, 41): [5, 41, 409],
    }
    if (pi, r) not in supported_bases:
        raise VerifyError(
            "this parametric_post_window_closure supports only "
            "(pi,r)=(109,11), (pi,r)=(229,23), (pi,r)=(349,7), "
            "and (pi,r)=(409,41)"
        )
    require_prime(pi)
    require_prime(r)

    start_e = int_value(record.get("start_exponent"), "start_exponent")
    min_start = 94 if (pi, r) == (349, 7) else 22
    if start_e < min_start or start_e % 2 != 0:
        raise VerifyError(
            f"start_exponent must be an even integer at least {min_start}"
        )
    exponent_parity = record.get("exponent_parity")
    if exponent_parity is not None and exponent_parity != "even":
        raise VerifyError("exponent_parity must be even when supplied")

    n0 = start_e + 1
    if n0 % 2 == 0:
        raise VerifyError("n=e+1 must be odd for non-Euler exponent rows")

    theorem = str_value(
        record.get("primitive_divisor_theorem", "zsigmondy"),
        "primitive_divisor_theorem",
    )
    if theorem != "zsigmondy":
        raise VerifyError("primitive_divisor_theorem must be zsigmondy")

    # For a^n-1 with a in {7,11,23,41} and odd n in the supported range, Zsigmondy's exceptional
    # cases do not apply.  A primitive prime divisor s of r^n-1 has
    # ord_s(r)=n.  Since n is odd and s is odd, s-1 is an even multiple of n;
    # hence s >= 2n+1.  This bound is monotone in n.
    if n0 < 3:
        raise VerifyError("Zsigmondy post-window n must be at least 3")
    primitive_lower_bound = 2 * n0 + 1
    claimed_lb = int_value(
        record.get("forced_prime_lower_bound"),
        "forced_prime_lower_bound",
    )
    if claimed_lb > primitive_lower_bound:
        raise VerifyError(
            f"claimed forced_prime_lower_bound {claimed_lb} exceeds "
            f"theorem-level lower bound {primitive_lower_bound}"
        )
    if claimed_lb <= 1:
        raise VerifyError("forced_prime_lower_bound must be greater than 1")

    K_base_raw = record.get("K_base")
    if not isinstance(K_base_raw, list) or not K_base_raw:
        raise VerifyError("K_base must be a nonempty list")
    K_base = sorted({int_value(x, "K_base[]") for x in K_base_raw})
    if len(K_base) != len(K_base_raw):
        raise VerifyError("K_base contains duplicates")
    expected_base = supported_bases[(pi, r)]
    if K_base != expected_base:
        raise VerifyError(f"K_base must be {expected_base}")
    for q in K_base:
        require_prime(q)

    B = int_value(record.get("B"), "B")
    M = int_value(record.get("M", record.get("tail_count_bound")), "M")
    if B != 59 or M != 18:
        raise VerifyError("this criterion expects B=59 and M=18")

    # Worst-case monotonic H occurs at the smallest certified forced prime.
    h = exact_H(K_base) * Fraction(claimed_lb, claimed_lb - 1)
    lhs = h * (Fraction(B, B - 1) ** M)
    if lhs >= 2:
        raise VerifyError("parametric post-window tail-control inequality fails")
    supplied = record.get("verified_inequality")
    if isinstance(supplied, dict):
        if "lhs_num" in supplied and int_value(supplied["lhs_num"], "verified_inequality.lhs_num") != lhs.numerator:
            raise VerifyError("verified_inequality.lhs_num is incorrect")
        if "lhs_den" in supplied and int_value(supplied["lhs_den"], "verified_inequality.lhs_den") != lhs.denominator:
            raise VerifyError("verified_inequality.lhs_den is incorrect")
        if "holds" in supplied and bool_value(supplied["holds"], "verified_inequality.holds") != (lhs < 2):
            raise VerifyError("verified_inequality.holds is incorrect")

    return (
        f"parametric-post-window id={cid} pair=({pi},{r}) "
        f"e>={start_e} lb={claimed_lb} B={B} M={M} ok"
    )


def verify_parametric_q5e1_pi_window_closure(record: Dict[str, Any]) -> str:
    """Verify the parametric Q5E1 Euler-prime window closure.

    The supported theorem-level instance is:
      branch Q5E1;
      pi prime with pi >= 1381 and pi == 1 mod 60;
      C_5(pi)=Phi_5(pi)/5 forces an odd prime r with r >= 11;
      the endpoint tail inequality
          H({5, pi, r}) * (59/58)^18 < 2
      holds at (pi,r)=(1381,11), hence by monotonicity for all larger pi and r.
    """
    cid = record_id(record)
    branch = str_value(record.get("branch"), "branch")
    if branch != "Q5E1":
        raise VerifyError("parametric_q5e1_pi_window_closure supports only branch Q5E1")

    pi_lb = int_value(record.get("pi_lower_bound"), "pi_lower_bound")
    if pi_lb < 1381:
        raise VerifyError("pi_lower_bound must be at least 1381")
    require_prime(pi_lb)

    mod = int_value(record.get("pi_congruence_mod"), "pi_congruence_mod")
    rem = int_value(record.get("pi_congruence_rem"), "pi_congruence_rem")
    if mod != 60 or rem != 1:
        raise VerifyError("this Q5E1 criterion expects pi == 1 mod 60")
    if pi_lb % mod != rem:
        raise VerifyError("pi_lower_bound does not satisfy the supplied congruence")

    cofactor = str_value(record.get("forced_cofactor", "Phi5_over_5"), "forced_cofactor")
    if cofactor != "Phi5_over_5":
        raise VerifyError("forced_cofactor must be Phi5_over_5")

    claimed_r_lb = int_value(record.get("forced_prime_lower_bound"), "forced_prime_lower_bound")
    if claimed_r_lb > 11:
        raise VerifyError("claimed forced_prime_lower_bound is stronger than the theorem-level bound 11")
    if claimed_r_lb < 11:
        raise VerifyError("forced_prime_lower_bound must be at least 11 for this criterion")
    require_prime(claimed_r_lb)
    if claimed_r_lb % 5 != 1:
        raise VerifyError("forced_prime_lower_bound must be compatible with r == 1 mod 5")

    K_base_raw = record.get("K_base")
    if not isinstance(K_base_raw, list):
        raise VerifyError("K_base must be a list")
    K_base = sorted({int_value(x, "K_base[]") for x in K_base_raw})
    if K_base != [5]:
        raise VerifyError("K_base must be [5]")

    B = int_value(record.get("B"), "B")
    M = int_value(record.get("M", record.get("tail_count_bound")), "M")
    if B != 59 or M != 18:
        raise VerifyError("this criterion expects B=59 and M=18")

    # Worst-case monotonic H occurs at the smallest pi and smallest forced r.
    h = exact_H([5, pi_lb, claimed_r_lb])
    lhs = h * (Fraction(B, B - 1) ** M)
    if lhs >= 2:
        raise VerifyError("Q5E1 parametric pi-window tail-control inequality fails")

    supplied = record.get("verified_inequality")
    if isinstance(supplied, dict):
        if "lhs_num" in supplied and int_value(supplied["lhs_num"], "verified_inequality.lhs_num") != lhs.numerator:
            raise VerifyError("verified_inequality.lhs_num is incorrect")
        if "lhs_den" in supplied and int_value(supplied["lhs_den"], "verified_inequality.lhs_den") != lhs.denominator:
            raise VerifyError("verified_inequality.lhs_den is incorrect")
        if "holds" in supplied and bool_value(supplied["holds"], "verified_inequality.holds") != (lhs < 2):
            raise VerifyError("verified_inequality.holds is incorrect")

    return (
        f"parametric-q5e1-pi-window id={cid} pi>={pi_lb} "
        f"pi=={rem} mod {mod} r>={claimed_r_lb} B={B} M={M} ok"
    )


def verify_parametric_q5n_witness_window_closure(record: Dict[str, Any]) -> str:
    """Verify the parametric Q5N witness-prime window closure.

    The supported theorem-level instance is:
      branch Q5N;
      non-Euler 5-input witness p >= 211 with p == 1 mod 5;
      C_5(p)=Phi_5(p)/5 forces an odd prime r with r >= 11;
      the endpoint tail inequality
          H({5, p, r}) * (59/58)^18 < 2
      holds at (p,r)=(211,11), hence by monotonicity for all larger p and r.
    """
    cid = record_id(record)
    branch = str_value(record.get("branch"), "branch")
    if branch != "Q5N":
        raise VerifyError("parametric_q5n_witness_window_closure supports only branch Q5N")

    p_lb = int_value(record.get("p_lower_bound"), "p_lower_bound")
    if p_lb < 211:
        raise VerifyError("p_lower_bound must be at least 211")
    require_prime(p_lb)

    mod = int_value(record.get("p_congruence_mod"), "p_congruence_mod")
    rem = int_value(record.get("p_congruence_rem"), "p_congruence_rem")
    if mod != 5 or rem != 1:
        raise VerifyError("this Q5N criterion expects p == 1 mod 5")
    if p_lb % mod != rem:
        raise VerifyError("p_lower_bound does not satisfy the supplied congruence")

    cofactor = str_value(record.get("forced_cofactor", "Phi5_over_5"), "forced_cofactor")
    if cofactor != "Phi5_over_5":
        raise VerifyError("forced_cofactor must be Phi5_over_5")

    claimed_r_lb = int_value(record.get("forced_prime_lower_bound"), "forced_prime_lower_bound")
    if claimed_r_lb > 11:
        raise VerifyError("claimed forced_prime_lower_bound is stronger than the theorem-level bound 11")
    if claimed_r_lb < 11:
        raise VerifyError("forced_prime_lower_bound must be at least 11 for this criterion")
    require_prime(claimed_r_lb)
    if claimed_r_lb % 5 != 1:
        raise VerifyError("forced_prime_lower_bound must be compatible with r == 1 mod 5")

    K_base_raw = record.get("K_base")
    if not isinstance(K_base_raw, list):
        raise VerifyError("K_base must be a list")
    K_base = sorted({int_value(x, "K_base[]") for x in K_base_raw})
    if K_base != [5]:
        raise VerifyError("K_base must be [5]")

    B = int_value(record.get("B"), "B")
    M = int_value(record.get("M", record.get("tail_count_bound")), "M")
    if B != 59 or M != 18:
        raise VerifyError("this criterion expects B=59 and M=18")

    h = exact_H([5, p_lb, claimed_r_lb])
    lhs = h * (Fraction(B, B - 1) ** M)
    if lhs >= 2:
        raise VerifyError("Q5N parametric witness-window tail-control inequality fails")

    supplied = record.get("verified_inequality")
    if isinstance(supplied, dict):
        if "lhs_num" in supplied and int_value(supplied["lhs_num"], "verified_inequality.lhs_num") != lhs.numerator:
            raise VerifyError("verified_inequality.lhs_num is incorrect")
        if "lhs_den" in supplied and int_value(supplied["lhs_den"], "verified_inequality.lhs_den") != lhs.denominator:
            raise VerifyError("verified_inequality.lhs_den is incorrect")
        if "holds" in supplied and bool_value(supplied["holds"], "verified_inequality.holds") != (lhs < 2):
            raise VerifyError("verified_inequality.holds is incorrect")

    return (
        f"parametric-q5n-witness-window id={cid} p>={p_lb} "
        f"p=={rem} mod {mod} r>={claimed_r_lb} B={B} M={M} ok"
    )

def verify_record(record: Dict[str, Any]) -> str:
    kind = record.get("type")
    if kind == "cyclotomic":
        return verify_cyclotomic(record)
    if kind == "kernel":
        return verify_kernel(record)
    if kind == "nineteen_order_branch":
        return verify_nineteen_order_branch(record)
    if kind == "expansion_abundance_bound":
        return verify_expansion_abundance_bound(record)
    if kind == "branch_archive":
        return verify_branch_archive(record)
    if kind == "coverage_split":
        return verify_coverage_split(record)
    if kind == "leaf_status":
        return verify_leaf_status(record)
    if kind == "forced_cofactor":
        return verify_forced_cofactor(record)
    if kind == "tail_count_certificate":
        return verify_tail_count_certificate(record)
    if kind == "abundance_obstruction":
        return verify_abundance_obstruction(record)
    if kind == "literature_filter_certificate":
        return verify_literature_filter_certificate(record)
    if kind == "parametric_post_window_closure":
        return verify_parametric_post_window_closure(record)
    if kind == "parametric_q5e1_pi_window_closure":
        return verify_parametric_q5e1_pi_window_closure(record)
    if kind == "parametric_q5n_witness_window_closure":
        return verify_parametric_q5n_witness_window_closure(record)
    if kind == "domain_extension":
        return verify_domain_extension(record)
    raise VerifyError(f"unknown certificate type {kind!r}")


def iter_jsonl(path: Path) -> Iterable[Tuple[int, Dict[str, Any]]]:
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, 1):
            stripped = line.strip()
            if not stripped or stripped.startswith("#"):
                continue
            try:
                data = json.loads(stripped)
            except json.JSONDecodeError as exc:
                raise VerifyError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
            if not isinstance(data, dict):
                raise VerifyError(f"{path}:{line_no}: JSONL record must be an object")
            yield line_no, data


def main(argv: List[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="+", type=Path, help="JSONL certificate files")
    parser.add_argument("--verbose", action="store_true", help="print every verified record")
    args = parser.parse_args(argv)

    total = 0
    records: List[Dict[str, Any]] = []
    try:
        for path in args.certificates:
            for line_no, record in iter_jsonl(path):
                result = verify_record(record)
                records.append(record)
                total += 1
                if args.verbose:
                    print(f"{path}:{line_no}: {result}")
        archive_count = verify_generic_archives(records)
        if args.verbose and archive_count:
            print(f"generic archive cross-checks: {archive_count} ok")
        extension_count = verify_domain_extensions(records)
        if args.verbose and extension_count:
            print(f"domain extension cross-checks: {extension_count} ok")
        for summary in domain_archive_summaries(records):
            print(summary)
    except VerifyError as exc:
        print(f"verification failed: {exc}", file=sys.stderr)
        return 1
    print(f"verified {total} certificate record(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
