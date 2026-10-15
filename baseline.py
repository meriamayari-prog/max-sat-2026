"""
Constructive upper bound U: an explicit certificate, produced without any SAT
solver, whose length bounds the shortest one from above.

Procedure: variable elimination by saturation, the complete method behind the
completeness proof of MaxSAT resolution.  To eliminate x, apply Definition 1 to
pairs (x v A, ~x v B) whose resolvent is not a tautology until no such pair
remains; the clauses on x that are left are then jointly satisfiable under every
assignment of the other variables, so they cost nothing and are never used
again.  When every variable has been eliminated, exactly lambda empty clauses
remain.

Termination: each application removes two clauses on x and adds only clauses on
x that are strictly longer, and lengths are bounded by the number of variables.

The elimination order changes the length by a large factor, so several orders
are tried and the shortest derivation is kept.  The result is a real derivation,
handed to the independent verifier like any other certificate.
"""
import random
import time
from collections import defaultdict

from maxsat_res import maxsat_resolution, norm


class Pool:
    def __init__(self, clauses):
        self.ctr = defaultdict(int)
        self.occ = defaultdict(set)
        self.empty = 0
        for c in clauses:
            self.add(c)

    def add(self, c):
        c = norm(c)
        if not c:
            self.empty += 1
            return
        if any(-l in c for l in c):
            # Definition 1 does produce tautological compensation clauses when
            # the two parents share literals.  They are never falsified, so
            # they contribute nothing to the cost; we simply never use them as
            # a premise.  Keeping them out of the index is what guarantees the
            # derivation contains no step with a tautological resolvent.
            return
        if self.ctr[c] == 0:
            for l in c:
                self.occ[l].add(c)
        self.ctr[c] += 1

    def remove(self, c):
        c = norm(c)
        assert self.ctr[c] > 0
        self.ctr[c] -= 1
        if self.ctr[c] == 0:
            del self.ctr[c]
            for l in c:
                self.occ[l].discard(c)

    def degree(self, x):
        p = sum(self.ctr[c] for c in self.occ.get(x, ()))
        n = sum(self.ctr[c] for c in self.occ.get(-x, ()))
        return p, n

    def size(self):
        return sum(self.ctr.values())


def saturate(pool, x, log, t_end, cap):
    while True:
        if time.time() > t_end or len(log) > cap or pool.size() > cap:
            return False
        pos, neg = pool.occ.get(x), pool.occ.get(-x)
        if not pos or not neg:
            return True
        pick = None
        for C1 in sorted(pos, key=len):
            A = [l for l in C1 if l != x]
            for C2 in sorted(neg, key=len):
                B = [l for l in C2 if l != -x]
                if any(-l in B for l in A):
                    continue
                k = len(set(A) | set(B))
                if pick is None or k < pick[0]:
                    pick = (k, C1, C2)
                    if k == 0:
                        break
            if pick and pick[0] == 0:
                break
        if pick is None:
            return True
        _, C1, C2 = pick
        res, left, right = maxsat_resolution(C1, C2, x)
        pool.remove(C1)
        pool.remove(C2)
        pool.add(res)
        for c in left + right:
            pool.add(c)
        log.append((C1, C2, x))


def _eliminate(clauses, pick, budget_s, cap):
    pool = Pool(clauses)
    allv = sorted({abs(l) for c in clauses for l in c})
    remaining, log = set(allv), []
    t_end = time.time() + budget_s
    while remaining:
        x = pick(pool, remaining)
        if not saturate(pool, x, log, t_end, cap):
            return None, None
        for lit in (x, -x):
            for c in list(pool.occ.get(lit, set())):
                for _ in range(pool.ctr.get(c, 0)):
                    pool.remove(c)
        remaining.discard(x)
    return log, pool.empty


def upper_bound(clauses, lam, budget_s=600, cap=3_000_000, seed=0, tries=8):
    """Returns (U, derivation) or (None, None)."""
    rnd = random.Random(seed)
    strategies = [
        lambda p, r: min(r, key=lambda v: ((lambda d: d[0] * d[1])(p.degree(v)), v)),
        lambda p, r: min(r, key=lambda v: ((lambda d: d[0] + d[1])(p.degree(v)), v)),
        lambda p, r: min(r, key=lambda v: ((lambda d: max(d))(p.degree(v)), v)),
        lambda p, r: min(r),
        lambda p, r: max(r),
    ]
    for _ in range(max(0, tries - len(strategies))):
        strategies.append(
            lambda p, r, _r=rnd: _r.choice(
                sorted(r, key=lambda v: (lambda d: d[0] * d[1])(p.degree(v)))[:3]))
    best = None
    per = max(5, budget_s // max(1, len(strategies)))
    for f in strategies:
        log, emp = _eliminate(clauses, f, per, cap)
        if log is None or emp != lam:
            continue
        if best is None or len(log) < len(best):
            best = log
    return (len(best), best) if best else (None, None)
