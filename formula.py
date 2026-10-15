"""
Input formulas: benchmark families, the dual-rail encoding, and readers for
DIMACS CNF and for the WCNF format used by the MaxSAT Evaluation.

Everything produced here is an UNWEIGHTED MaxSAT instance: a plain list of
clauses, every one soft with unit cost.  That is the setting of the paper.
"""
import gzip
import os
from itertools import combinations

from maxsat_res import norm


# ============================================================ benchmark families
def php(m):
    """PHP^{m+1}_m : m+1 pigeons, m holes."""
    var, cls = {}, []

    def v(i, j):
        return var.setdefault((i, j), len(var) + 1)

    for i in range(1, m + 2):
        cls.append([v(i, j) for j in range(1, m + 1)])
    for j in range(1, m + 1):
        for i1, i2 in combinations(range(1, m + 2), 2):
            cls.append([-v(i1, j), -v(i2, j)])
    return len(var), cls


def two_php(m):
    """2PHP^u_m : disjoint union of two copies of PHP^{m+1}_m."""
    n1, c1 = php(m)
    cls = [list(c) for c in c1]
    cls += [[(1 if l > 0 else -1) * (abs(l) + n1) for l in c] for c in c1]
    return 2 * n1, cls


def parity(k):
    """Tseitin formula of the cycle C_k with every charge equal to one:
       x_1 xor x_2 = 1, ..., x_k xor x_1 = 1.  Unsatisfiable iff k is odd."""
    cls = []
    for i in range(1, k + 1):
        a, b = i, (i % k) + 1
        cls.append([a, b])
        cls.append([-a, -b])
    return k, cls


# ================================================================== dual rail
def dual_rail(n_orig, cls):
    """Dual-rail encoding (Ignatiev et al. 2017, Bonet et al. 2018).

    p_x = 2x-1 says x is true, n_x = 2x says x is false.  A clause is
    translated by forbidding the assignment that falsifies it, so a positive
    literal x becomes ~n_x and a negative literal ~x becomes ~p_x; the
    translated clauses are purely negative.  Added: one consistency clause
    (~p_x v ~n_x) per original variable, and the 2N positive units (p_x), (n_x).

    Every clause is soft with unit cost.
    """
    P = lambda x: 2 * x - 1
    N = lambda x: 2 * x
    out = [norm([-N(l) if l > 0 else -P(-l) for l in c]) for c in cls]
    out += [norm([-P(x), -N(x)]) for x in range(1, n_orig + 1)]
    out += [(P(x),) for x in range(1, n_orig + 1)]
    out += [(N(x),) for x in range(1, n_orig + 1)]
    return 2 * n_orig, out


FAMILIES = {}
for _m in range(2, 10):
    FAMILIES[f"php{_m}"] = (lambda m=_m: php(m))
    FAMILIES[f"2php{_m}"] = (lambda m=_m: two_php(m))
for _k in range(3, 16, 2):
    FAMILIES[f"parity{_k}"] = (lambda k=_k: parity(k))


def family(name, encode_dual_rail=True):
    """Returns (n, clauses) for a named family instance."""
    if name not in FAMILIES:
        raise KeyError(f"unknown family instance {name!r}; "
                       f"known: {', '.join(sorted(FAMILIES))}")
    n_orig, cls = FAMILIES[name]()
    if encode_dual_rail:
        return dual_rail(n_orig, cls)
    return n_orig, [norm(c) for c in cls]


# ==================================================================== readers
def _open(path):
    if path.endswith('.xz'):
        import lzma
        return lzma.open(path, 'rt')
    if path.endswith('.gz'):
        return gzip.open(path, 'rt')
    return open(path, 'r')


def read_cnf(path):
    """Plain DIMACS CNF.  Every clause becomes a unit-cost soft clause."""
    cls, n = [], 0
    with _open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in 'c%':
                continue
            if line[0] == 'p':
                n = int(line.split()[2])
                continue
            lits = [int(t) for t in line.split()]
            if lits and lits[-1] == 0:
                lits = lits[:-1]
            if lits:
                cls.append(norm(lits))
    return (n or max((abs(l) for c in cls for l in c), default=0)), cls


def read_wcnf(path, hard_as_soft=False):
    """WCNF, both the old (p wcnf) and the new (h / weight) MaxSAT Evaluation
    formats.  Returns (n, soft_clauses, hard_clauses, weights).

    The paper's setting is unweighted, so an instance whose soft clauses are
    not all of weight one is rejected by pick_competition.py; this reader
    still reports the weights so the filter can see them.
    """
    soft, hard, weights = [], [], []
    top = None
    with _open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in 'c%':
                continue
            if line[0] == 'p':
                parts = line.split()
                if len(parts) >= 5 and parts[1] == 'wcnf':
                    top = int(parts[4])
                continue
            parts = line.split()
            if parts[0] == 'h':                      # new format, hard clause
                lits = [int(t) for t in parts[1:] if t != '0']
                hard.append(norm(lits))
                continue
            w = int(parts[0])
            lits = [int(t) for t in parts[1:] if t != '0']
            if not lits:
                continue
            if top is not None and w >= top:
                hard.append(norm(lits))
            else:
                soft.append(norm(lits))
                weights.append(w)
    n = max((abs(l) for c in soft + hard for l in c), default=0)
    if hard_as_soft:
        return n, soft + hard, [], weights + [1] * len(hard)
    return n, soft, hard, weights


def load(spec):
    """Dispatch on a specification string.

      php3, 2php4, parity5     -> benchmark family, dual-rail encoded
      raw:php3                 -> benchmark family, NOT dual-rail encoded
      path/to/file.cnf         -> DIMACS, all clauses soft
      path/to/file.wcnf[.gz]   -> WCNF, all clauses soft (unweighted check in
                                  pick_competition.py)

    Returns (n, clauses).
    """
    if spec.startswith('raw:'):
        return family(spec[4:], encode_dual_rail=False)
    if spec in FAMILIES:
        return family(spec, encode_dual_rail=True)
    if not os.path.exists(spec):
        raise FileNotFoundError(spec)
    if spec.endswith(('.wcnf', '.wcnf.gz', '.wcnf.xz')):
        n, soft, hard, _ = read_wcnf(spec, hard_as_soft=True)
        return n, soft
    return read_cnf(spec)


# ================================================================== optimum
def optimum(clauses, timeout=None):
    """lambda = opt(F) for an unweighted instance, with an exact MaxSAT solver."""
    from pysat.formula import WCNF
    from pysat.examples.rc2 import RC2
    w = WCNF()
    for c in clauses:
        w.append(list(c), weight=1)
    with RC2(w) as soL:
        soL.compute()
        return soL.cost
