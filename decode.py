"""
Turns a model of Phi_{K,lambda} into an explicit certificate: a list of steps
(C1, C2, pivot) over real clauses, which the verifier replays from Definition 1
without ever looking at the encoding.

Two passes are needed.  The encoding represents a compensation object as an
unordered pair (F, R), but the family it stands for depends on the ORDER of R.
Pass one reads, for every object, the schedule of extractions performed on it:
a front extraction takes a literal from the left end of R, a back extraction
from the right end.  Since every literal is consumed at most once, the fronts
form a prefix and the backs a suffix, so the schedule always determines a
consistent order.  Pass two replays the derivation with those orders fixed and
writes out the clauses themselves.
"""
from maxsat_res import norm, gamma, maxsat_resolution


class Decoded:
    def __init__(self, steps, objects, resolvents):
        self.steps = steps            # [(C1, C2, pivot), ...]
        self.objects = objects        # k -> (F, ordered R) as created
        self.resolvents = resolvents  # t -> resolvent clause


def decode(enc, model):
    val = {}
    for lit in model:
        val[abs(lit)] = lit > 0

    def V(v):
        return val.get(v, False)

    K, M, X = enc.K, enc.M, enc.X

    def clause_from(pos, neg):
        out = []
        for x in X:
            if pos(x):
                out.append(x)
            if neg(x):
                out.append(-x)
        return norm(out)

    # ---------------- pass 1 : read the schedule of every object -------------
    pivot = {}
    sel = {}            # (side, t) -> ('s', i) or ('c', k)
    consumed = {}       # (t, k) -> literal consumed (signed), or None
    extracted = {}      # (side, t) -> clause
    for t in range(1, K + 1):
        pivot[t] = next(x for x in X if V(enc.piv(t, x)))
        for s in 'LR':
            pick = None
            for i in enc.avail_s(t):
                if V(enc.sel_s(s, t, i)):
                    pick = ('s', i)
                    break
            if pick is None:
                for k in enc.avail_c(t):
                    if V(enc.sel_c(s, t, k)):
                        pick = ('c', k)
                        break
            assert pick is not None, f"step {t} side {s}: no parent selected"
            sel[(s, t)] = pick
            extracted[(s, t)] = clause_from(
                lambda x: V(enc.ep(s, t, x)), lambda x: V(enc.en(s, t, x)))
        for k in enc.avail_c(t):
            lit = None
            for x in X:
                if V(enc.acc(t, k, x)):
                    lit = x if V(enc.rp(k, t - 1, x)) else -x
                    break
            consumed[(t, k)] = lit

    # schedule per object: list of ('front'|'back', literal)
    schedule = {k: [] for k in range(1, 2 * K + 1)}
    for t in range(1, K + 1):
        for s in 'LR':
            kind, idx = sel[(s, t)]
            if kind != 'c':
                continue
            lit = consumed[(t, idx)]
            assert lit is not None, f"step {t}: object {idx} consumed nothing"
            mode = 'front' if abs(lit) == pivot[t] else 'back'
            schedule[idx].append((mode, lit))

    # ---------------- pass 2 : replay with explicit clauses -----------------
    F_of = {}
    R_of = {}

    def order_remainder(k, members):
        """Order R so that the recorded schedule is a valid deque schedule."""
        front_seq = [l for m, l in schedule[k] if m == 'front']
        back_seq = [l for m, l in schedule[k] if m == 'back']
        rest = [l for l in members if l not in front_seq and l not in back_seq]
        return front_seq + rest + back_seq[::-1]

    steps = []
    resolvents = {}
    cur_R = {}
    for t in range(1, K + 1):
        EL, ER = extracted[('L', t)], extracted[('R', t)]
        x = pivot[t]
        assert x in EL and -x in ER, f"step {t}: pivot polarity"
        steps.append((EL, ER, x))
        res, left, right = maxsat_resolution(EL, ER, x)
        resolvents[t] = res
        # objects created at this step
        for k, F, Rset in ((2 * t - 1, EL, [l for l in ER if l != -x]),
                           (2 * t, ER, [l for l in EL if l != x])):
            F_of[k] = F
            R_of[k] = order_remainder(k, Rset)
            cur_R[k] = list(R_of[k])
        # consume from the objects used as parents
        for s in 'LR':
            kind, idx = sel[(s, t)]
            if kind != 'c':
                continue
            lit = consumed[(t, idx)]
            assert lit in cur_R[idx], \
                f"step {t}: literal {lit} not in the remainder of object {idx}"
            cur_R[idx].remove(lit)
    return Decoded(steps, {k: (F_of[k], R_of[k]) for k in F_of}, resolvents)


def certificate_json(dec, instance, K, lam, mode):
    return {
        'instance': instance,
        'K': K,
        'lambda': lam,
        'mode': mode,
        'steps': [{'C1': list(a), 'C2': list(b), 'pivot': p}
                  for a, b, p in dec.steps],
    }
