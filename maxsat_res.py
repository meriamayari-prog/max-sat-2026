"""
MaxSAT resolution (Definition 1) and the condensed (F, R) representation.

This module is the *reference semantics* of the whole project.  The SAT encoder
is written independently of it, and the verifier uses only this module, so that
a certificate is never checked with the same code that produced it.

Literals are non-zero ints: +i is x_i, -i is not x_i.  A clause is a tuple of
literals, a formula a multiset (list) of clauses.
"""
from itertools import product


def norm(clause):
    """Canonical form of a clause: duplicates removed, literals ordered."""
    return tuple(sorted(set(clause), key=lambda l: (abs(l), l)))


def is_tautology(clause):
    s = set(clause)
    return any(-l in s for l in s)


def maxsat_resolution(C1, C2, x):
    """Definition 1.

    C1 = x v A and C2 = ~x v B, with pivot variable x > 0.  Returns

        (resolvent, left_compensation, right_compensation)

    where resolvent = A v B,
          left_compensation  = [ x v A v b_1 v ... v b_{i-1} v ~b_i  for i ],
          right_compensation = [ ~x v B v a_1 v ... v a_{j-1} v ~a_j for j ].

    The lists are ordered, because the compensation clauses are exactly the
    family described by the condensed pair  (x v A, B)  resp.  (~x v B, A).
    """
    assert x > 0, "the pivot is a variable, not a literal"
    assert x in C1 and -x in C2, "pivot polarity"
    A = [l for l in C1 if l != x]
    B = [l for l in C2 if l != -x]
    resolvent = norm(A + B)
    left = [norm([x] + A + B[:i] + [-B[i]]) for i in range(len(B))]
    right = [norm([-x] + B + A[:j] + [-A[j]]) for j in range(len(A))]
    return resolvent, left, right


def gamma(F, R):
    """The family of clauses represented by the condensed pair (F, R),
       R being an ORDERED list:

           F v ~r_1
           F v r_1 v ~r_2
           ...
           F v r_1 v ... v r_{s-1} v ~r_s
    """
    return [norm(list(F) + R[:i] + [-R[i]]) for i in range(len(R))]


def extract_front(F, R):
    """Consume the first remainder literal.
       Extracted clause  F v ~r_1 ,  residual  (F + {r_1}, R \\ {r_1})."""
    assert R
    return norm(list(F) + [-R[0]]), (norm(list(F) + [R[0]]), list(R[1:]))


def extract_back(F, R):
    """Consume the last remainder literal (largest-clause extraction).
       Extracted clause  F v r_1 v ... v r_{s-1} v ~r_s ,  residual  (F, R \\ {r_s})."""
    assert R
    return norm(list(F) + R[:-1] + [-R[-1]]), (norm(F), list(R[:-1]))


# --------------------------------------------------------------- cost oracle
def cost(formula, assign):
    """Number of clauses of `formula` falsified by `assign` (dict var -> bool)."""
    c = 0
    for cl in formula:
        if not any((l > 0) == assign[abs(l)] for l in cl):
            c += 1
    return c


def variables(formula):
    return sorted({abs(l) for cl in formula for l in cl})


def maxsat_equivalent(F1, F2):
    """Brute force: cost_a(F1) == cost_a(F2) for every assignment a.
       Only usable for small variable counts; the verifier calls it on the
       instances where it is affordable and falls back to a structural check
       otherwise."""
    vs = sorted(set(variables(F1)) | set(variables(F2)))
    for bits in product([False, True], repeat=len(vs)):
        a = dict(zip(vs, bits))
        if cost(F1, a) != cost(F2, a):
            return False, a
    return True, None


# ------------------------------------------------------------------ multiset
class Multiset:
    """Multiset of clauses, with the operations a derivation needs."""

    def __init__(self, clauses=()):
        self.ctr = {}
        for c in clauses:
            self.add(c)

    def add(self, c):
        c = norm(c)
        self.ctr[c] = self.ctr.get(c, 0) + 1

    def remove(self, c):
        c = norm(c)
        n = self.ctr.get(c, 0)
        if n == 0:
            raise KeyError(f"clause {c} is not in the multiset")
        if n == 1:
            del self.ctr[c]
        else:
            self.ctr[c] = n - 1

    def count(self, c):
        return self.ctr.get(norm(c), 0)

    def empties(self):
        return self.ctr.get((), 0)

    def clauses(self):
        out = []
        for c, k in self.ctr.items():
            out.extend([c] * k)
        return out

    def size(self):
        return sum(self.ctr.values())

    def copy(self):
        m = Multiset()
        m.ctr = dict(self.ctr)
        return m

    def key(self):
        return tuple(sorted(self.ctr.items()))


def apply_step(ms, C1, C2, x):
    """Apply one inference to a multiset, in place.  Returns the resolvent."""
    ms.remove(C1)
    ms.remove(C2)
    res, left, right = maxsat_resolution(C1, C2, x)
    ms.add(res)
    for c in left:
        ms.add(c)
    for c in right:
        ms.add(c)
    return res
