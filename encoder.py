"""
The SAT encoding Phi_{K,lambda}.

Given an unweighted MaxSAT instance F = {C_1, ..., C_M} with opt(F) = lambda,
Phi_{K,lambda} is satisfiable iff there is a MaxSAT-resolution derivation of
exactly K inference steps from F that produces lambda empty clauses, the last
inference producing one of them.

----------------------------------------------------------------------------
MODEL
----------------------------------------------------------------------------
Standard clauses are indexed 1..M+K: 1..M are the input clauses, and M+t is the
resolvent produced at step t.  Compensation objects are indexed 1..2K: step t
creates object 2t-1 on the left and 2t on the right.  An object is a condensed
pair (F_k, R_k) standing for the family

    F_k v ~r_1 ,  F_k v r_1 v ~r_2 , ... ,  F_k v r_1 v..v r_{s-1} v ~r_s .

At step t the encoding selects a left parent and a right parent -- each either a
standard clause or a compensation object -- and a pivot variable x.  It then
names the two clauses actually entering the inference:

    EL_t  the clause extracted from the left parent   (must contain  x)
    ER_t  the clause extracted from the right parent  (must contain ~x)

and everything else is defined from those two, directly as Definition 1 states:

    resolvent at M+t      =  (EL_t \\ {x})  u  (ER_t \\ {~x})
    object 2t-1           =  ( F := EL_t ,  R := ER_t \\ {~x} )
    object 2t             =  ( F := ER_t ,  R := EL_t \\ {x}  )

Naming EL_t and ER_t is what keeps the encoding honest: the compensation set
generated on one side takes its remainder from the OPPOSITE parent, which is
the cross-pollution the earlier formulation got wrong.

Extracting a clause from a compensation object consumes exactly one remainder
literal, and only two extractions are available:

    front   the consumed literal is the complementary pivot (it lies on the
            pivot variable).  EL_t = F_k u {x}, and the consumed literal joins
            the fixed part of the residual with its own polarity.
    back    the consumed literal l is not on the pivot variable (the largest
            clause of the family).  EL_t = F_k u (R_k \\ {l}) u {~l}, and the
            fixed part of the residual is unchanged.

Which of the two applies is carried by a single mode variable per side and per
step, so no constraint of this encoding quantifies over two variables.
"""
from itertools import combinations

from pysat.formula import IDPool, CNF
from pysat.card import CardEnc, EncType

from maxsat_res import norm


class Encoder:
    def __init__(self, clauses, K, lam, mode='certificate', card=EncType.seqcounter):
        self.input = [norm(c) for c in clauses]
        self.M = len(self.input)
        self.K = K
        self.lam = lam if mode == 'certificate' else 1
        self.mode = mode
        self.card_enc = card
        self.X = sorted({abs(l) for c in self.input for l in c})
        self.pool = IDPool()
        self.cnf = CNF()
        self._build()

    # ------------------------------------------------------------- variables
    def v(self, *key):
        return self.pool.id(key)

    # standard clause i contains x / ~x
    def sp(self, i, x):
        return self.v('sp', i, x)

    def sn(self, i, x):
        return self.v('sn', i, x)

    # compensation object k at time t: fixed part / remainder
    def fp(self, k, t, x):
        return self.v('fp', k, t, x)

    def fn(self, k, t, x):
        return self.v('fn', k, t, x)

    def rp(self, k, t, x):
        return self.v('rp', k, t, x)

    def rn(self, k, t, x):
        return self.v('rn', k, t, x)

    # extracted clauses, side s in {'L','R'}
    def ep(self, s, t, x):
        return self.v('ep', s, t, x)

    def en(self, s, t, x):
        return self.v('en', s, t, x)

    # selection
    def sel_s(self, s, t, i):
        return self.v('sels', s, t, i)

    def sel_c(self, s, t, k):
        return self.v('selc', s, t, k)

    def piv(self, t, x):
        return self.v('piv', t, x)

    def acc(self, t, k, x):
        return self.v('acc', t, k, x)

    def front(self, s, t):
        return self.v('front', s, t)

    def oncc(self, s, t):
        """side s of step t takes a compensation object as its parent"""
        return self.v('oncc', s, t)

    def used(self, i, t):
        """standard clause i has been consumed at some step <= t"""
        return self.v('used', i, t)

    def alive(self, k, t):
        """compensation object k still has a non-empty remainder at time t"""
        return self.v('alive', k, t)

    def empty(self, t):
        return self.v('empty', t)

    # --------------------------------------------------------------- helpers
    def add(self, *clause):
        self.cnf.append(list(clause))

    def implies(self, antecedent, consequent):
        """(a1 & a2 & ...) -> c"""
        self.cnf.append([-a for a in antecedent] + [consequent])

    def iff_or(self, lit, sources):
        """lit <-> OR of sources, each source being a conjunction (list of lits)."""
        aux = []
        for src in sources:
            if len(src) == 1:
                aux.append(src[0])
                self.cnf.append([-src[0], lit])
            else:
                a = self.pool.id(('aux', lit, tuple(src)))
                for s in src:
                    self.cnf.append([-a, s])
                self.cnf.append([a] + [-s for s in src])
                aux.append(a)
                self.cnf.append([-a, lit])
        self.cnf.append([-lit] + aux)

    def exactly_one(self, lits):
        self.cnf.append(list(lits))
        for a, b in combinations(lits, 2):
            self.cnf.append([-a, -b])

    def at_most_one(self, lits):
        for a, b in combinations(lits, 2):
            self.cnf.append([-a, -b])

    # ------------------------------------------------------------- structure
    def create_step(self, k):
        """the step at which compensation object k is created"""
        return (k + 1) // 2

    def avail_s(self, t):
        """standard indices that may be a parent at step t"""
        return list(range(1, self.M + t))

    def avail_c(self, t):
        """compensation indices that may be a parent at step t"""
        return [k for k in range(1, 2 * self.K + 1) if self.create_step(k) < t]

    # ----------------------------------------------------------------- build
    def _build(self):
        self._input_clauses()
        for t in range(1, self.K + 1):
            self._selection(t)
            self._pivot(t)
            self._extract(t)
            self._resolvent(t)
            self._generate(t)
            self._residual(t)
            self._bookkeeping(t)
        self._empties()

    # -- the input clauses are fixed -----------------------------------------
    def _input_clauses(self):
        for i, c in enumerate(self.input, start=1):
            s = set(c)
            for x in self.X:
                self.add(self.sp(i, x) if x in s else -self.sp(i, x))
                self.add(self.sn(i, x) if -x in s else -self.sn(i, x))
            self.add(-self.used(i, 0))
        # compensation objects do not exist before they are created
        for k in range(1, 2 * self.K + 1):
            t0 = self.create_step(k)
            for x in self.X:
                self.add(-self.fp(k, t0 - 1, x))
                self.add(-self.fn(k, t0 - 1, x))
                self.add(-self.rp(k, t0 - 1, x))
                self.add(-self.rn(k, t0 - 1, x))
            self.add(-self.alive(k, t0 - 1))

    # -- one left parent and one right parent --------------------------------
    def _selection(self, t):
        for s in 'LR':
            lits = [self.sel_s(s, t, i) for i in self.avail_s(t)] + \
                   [self.sel_c(s, t, k) for k in self.avail_c(t)]
            self.exactly_one(lits)
            # a parent must still be available
            for i in self.avail_s(t):
                self.implies([self.sel_s(s, t, i)], -self.used(i, t - 1))
            for k in self.avail_c(t):
                self.implies([self.sel_c(s, t, k)], self.alive(k, t - 1))
            # oncc_s,t  <->  the parent on side s is a compensation object
            self.iff_or(self.oncc(s, t),
                        [[self.sel_c(s, t, k)] for k in self.avail_c(t)])
        # the two parents must be different objects
        for i in self.avail_s(t):
            self.add(-self.sel_s('L', t, i), -self.sel_s('R', t, i))
        for k in self.avail_c(t):
            self.add(-self.sel_c('L', t, k), -self.sel_c('R', t, k))

    # -- exactly one pivot variable ------------------------------------------
    def _pivot(self, t):
        self.exactly_one([self.piv(t, x) for x in self.X])

    # -- the two extracted clauses -------------------------------------------
    def _extract(self, t):
        # Consumption is a property of the step and of the object, not of the
        # side: an object selected as a parent gives up exactly one remainder
        # literal, and an object that is not selected gives up none.
        for k in self.avail_c(t):
            picked = self.v('pickedc', t, k)
            self.iff_or(picked, [[self.sel_c('L', t, k)], [self.sel_c('R', t, k)]])
            accs = [self.acc(t, k, x) for x in self.X]
            self.at_most_one(accs)
            self.cnf.append([-picked] + accs)          # picked -> one consumed
            for x in self.X:
                self.implies([self.acc(t, k, x)], picked)
                # only a literal present in the remainder can be consumed
                self.cnf.append([-self.acc(t, k, x),
                                 self.rp(k, t - 1, x), self.rn(k, t - 1, x)])

        for s in 'LR':
            sign = 1 if s == 'L' else -1          # L provides x, R provides ~x
            # ---- front / back mode
            self.iff_or(self.front(s, t),
                        [[self.sel_c(s, t, k), self.acc(t, k, x), self.piv(t, x)]
                         for k in self.avail_c(t) for x in self.X])
            self.implies([self.front(s, t)], self.oncc(s, t))
            back = self.v('back', s, t)
            self.iff_or(back, [[self.oncc(s, t), -self.front(s, t)]])

            for x in self.X:
                src_p, src_n = [], []
                # ---- standard parent: the extracted clause is the clause
                for i in self.avail_s(t):
                    src_p.append([self.sel_s(s, t, i), self.sp(i, x)])
                    src_n.append([self.sel_s(s, t, i), self.sn(i, x)])
                # ---- compensation parent
                for k in self.avail_c(t):
                    sc = self.sel_c(s, t, k)
                    # the fixed part is in every clause of the family
                    src_p.append([sc, self.fp(k, t - 1, x)])
                    src_n.append([sc, self.fn(k, t - 1, x)])
                    # the complement of the consumed literal
                    src_p.append([sc, self.acc(t, k, x), self.rn(k, t - 1, x)])
                    src_n.append([sc, self.acc(t, k, x), self.rp(k, t - 1, x)])
                    # back extraction also carries the unconsumed remainder
                    src_p.append([sc, back, -self.acc(t, k, x),
                                  self.rp(k, t - 1, x)])
                    src_n.append([sc, back, -self.acc(t, k, x),
                                  self.rn(k, t - 1, x)])
                self.iff_or(self.ep(s, t, x), src_p)
                self.iff_or(self.en(s, t, x), src_n)
                # an extracted clause is never a tautology
                self.add(-self.ep(s, t, x), -self.en(s, t, x))

            # ---- the extracted clause carries the pivot with the right sign
            for x in self.X:
                if sign > 0:
                    self.implies([self.piv(t, x)], self.ep(s, t, x))
                else:
                    self.implies([self.piv(t, x)], self.en(s, t, x))

    # -- resolvent at index M+t ----------------------------------------------
    def _resolvent(self, t):
        i = self.M + t
        for x in self.X:
            # the pivot variable is resolved away
            self.implies([self.piv(t, x)], -self.sp(i, x))
            self.implies([self.piv(t, x)], -self.sn(i, x))
            self.iff_or(self.sp(i, x),
                        [[self.ep('L', t, x), -self.piv(t, x)],
                         [self.ep('R', t, x), -self.piv(t, x)]])
            self.iff_or(self.sn(i, x),
                        [[self.en('L', t, x), -self.piv(t, x)],
                         [self.en('R', t, x), -self.piv(t, x)]])
            # the resolvent is not a tautology
            self.add(-self.sp(i, x), -self.sn(i, x))
        self.add(-self.used(i, t))

    # -- the two compensation objects created at step t ----------------------
    def _generate(self, t):
        for k, s, other in ((2 * t - 1, 'L', 'R'), (2 * t, 'R', 'L')):
            for x in self.X:
                # fixed part := the extracted clause of this side, pivot included
                self.iff_or(self.fp(k, t, x), [[self.ep(s, t, x)]])
                self.iff_or(self.fn(k, t, x), [[self.en(s, t, x)]])
                # remainder := the non-pivot part of the OPPOSITE extracted clause
                self.iff_or(self.rp(k, t, x),
                            [[self.ep(other, t, x), -self.piv(t, x)]])
                self.iff_or(self.rn(k, t, x),
                            [[self.en(other, t, x), -self.piv(t, x)]])
            self.iff_or(self.alive(k, t),
                        [[self.rp(k, t, x)] for x in self.X] +
                        [[self.rn(k, t, x)] for x in self.X])

    # -- residual of a compensation object used as a parent ------------------
    def _residual(self, t):
        for k in self.avail_c(t):
            picked = self.v('pickedc', t, k)
            for x in self.X:
                # fixed part: persists, plus the consumed literal when it is
                # the complementary pivot (front extraction)
                self.iff_or(self.fp(k, t, x),
                            [[self.fp(k, t - 1, x)],
                             [picked, self.acc(t, k, x), self.piv(t, x),
                              self.rp(k, t - 1, x)]])
                self.iff_or(self.fn(k, t, x),
                            [[self.fn(k, t - 1, x)],
                             [picked, self.acc(t, k, x), self.piv(t, x),
                              self.rn(k, t - 1, x)]])
                # remainder: every literal except the consumed one persists
                self.iff_or(self.rp(k, t, x),
                            [[self.rp(k, t - 1, x), -self.acc(t, k, x)]])
                self.iff_or(self.rn(k, t, x),
                            [[self.rn(k, t - 1, x), -self.acc(t, k, x)]])
            self.iff_or(self.alive(k, t),
                        [[self.rp(k, t, x)] for x in self.X] +
                        [[self.rn(k, t, x)] for x in self.X])

    # -- a standard clause is consumed when it is used as a parent -----------
    def _bookkeeping(self, t):
        for i in self.avail_s(t):
            self.iff_or(self.used(i, t),
                        [[self.used(i, t - 1)],
                         [self.sel_s('L', t, i)],
                         [self.sel_s('R', t, i)]])

    # -- empty clauses --------------------------------------------------------
    def _empties(self):
        for t in range(1, self.K + 1):
            i = self.M + t
            lits = []
            for x in self.X:
                lits += [self.sp(i, x), self.sn(i, x)]
            # empty_t <-> the resolvent has no literal
            for l in lits:
                self.add(-self.empty(t), -l)
            self.cnf.append([self.empty(t)] + lits)
        # exactly lambda empty clauses, and the last inference produces one
        card = CardEnc.equals(lits=[self.empty(t) for t in range(1, self.K + 1)],
                              bound=self.lam, vpool=self.pool,
                              encoding=self.card_enc)
        self.cnf.extend(card.clauses)
        self.add(self.empty(self.K))

    # ------------------------------------------------------------------ stats
    def stats(self):
        return {'n_vars': self.cnf.nv, 'n_clauses': len(self.cnf.clauses),
                'K': self.K, 'lambda': self.lam, 'M': self.M,
                'n_x': len(self.X), 'mode': self.mode}
