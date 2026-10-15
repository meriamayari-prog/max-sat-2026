"""
Independent verification of a certificate.

This module shares no code with the encoder.  It starts from the input formula,
replays every step with Definition 1 only, and checks that

  1. both premises are actually present in the current multiset,
  2. the pivot occurs positively in the first premise and negatively in the second,
  3. the resolvent is not a tautology,
  4. the derivation produces exactly lambda empty clauses, the last step
     producing one of them,
  5. the multiset stays MaxSAT-equivalent to the input formula -- checked
     exactly by enumeration while the number of variables allows it, and
     otherwise on a large random sample of assignments.

Satisfiability of Phi_{K,lambda} says the model is consistent with the encoding.
Only this module says the certificate is a MaxSAT-resolution derivation.
"""
import random

from maxsat_res import (Multiset, maxsat_resolution, norm, cost, variables,
                        maxsat_equivalent)


class VerificationError(Exception):
    pass


def verify(input_clauses, steps, lam, exact_upto=22, samples=20000, seed=0):
    """steps: list of (C1, C2, pivot).  Raises VerificationError on failure,
       returns a dict of statistics on success."""
    base = [norm(c) for c in input_clauses]
    ms = Multiset(base)
    vs = variables(base)
    rnd = random.Random(seed)
    exact = len(vs) <= exact_upto

    sample = None
    if not exact:
        sample = [{v: rnd.random() < 0.5 for v in vs} for _ in range(samples)]
        base_costs = [cost(base, a) for a in sample]

    for t, (C1, C2, x) in enumerate(steps, start=1):
        C1, C2 = norm(C1), norm(C2)
        if ms.count(C1) == 0:
            raise VerificationError(f"step {t}: premise {C1} absent from the multiset")
        ms.remove(C1)
        if ms.count(C2) == 0:
            ms.add(C1)
            raise VerificationError(f"step {t}: premise {C2} absent from the multiset")
        ms.add(C1)
        if x <= 0 or x not in C1 or -x not in C2:
            raise VerificationError(f"step {t}: pivot {x} has the wrong polarity")
        res, left, right = maxsat_resolution(C1, C2, x)
        if any(-l in set(res) for l in res):
            raise VerificationError(f"step {t}: the resolvent is a tautology")
        ms.remove(C1)
        ms.remove(C2)
        ms.add(res)
        for c in left + right:
            ms.add(c)
        after = ms.clauses()
        if exact:
            ok, ce = maxsat_equivalent(base, after)
            if not ok:
                raise VerificationError(
                    f"step {t}: MaxSAT equivalence broken, counterexample {ce}")
        else:
            for a, c0 in zip(sample, base_costs):
                if cost(after, a) != c0:
                    raise VerificationError(
                        f"step {t}: cost mismatch on a sampled assignment")

    n_empty = ms.empties()
    if n_empty != lam:
        raise VerificationError(
            f"the derivation produces {n_empty} empty clauses, expected {lam}")
    if steps:
        last_res, _, _ = maxsat_resolution(norm(steps[-1][0]), norm(steps[-1][1]),
                                           steps[-1][2])
        if last_res != ():
            raise VerificationError("the last inference does not produce an empty clause")
    return {'steps': len(steps), 'empty_clauses': n_empty,
            'final_multiset_size': ms.size(),
            'equivalence_check': 'exact' if exact else f'sampled({samples})'}


def verify_file(instance_clauses, path):
    import json
    data = json.load(open(path))
    steps = [(tuple(s['C1']), tuple(s['C2']), s['pivot']) for s in data['steps']]
    return verify(instance_clauses, steps, data['lambda'])
