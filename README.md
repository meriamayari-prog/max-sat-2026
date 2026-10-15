# Shortest MaxSAT-resolution optimality certificates



Given an unweighted MaxSAT instance `F` with optimum `λ = opt(F)`, the tool
searches for a **shortest MaxSAT-resolution optimality certificate**: a
derivation, under the MaxSAT-resolution rule, that produces exactly `λ` empty
clauses, with as few inference steps as possible. It also searches for a
shortest **max-refutation**, which produces a single empty clause.

The search is reduced to SAT: for a candidate length `K`, a propositional
formula `Φ_{K,λ}` is satisfiable if and only if a certificate of length `K`
exists. The search solves `Φ_{K,λ}` for `K = λ, λ+1, …`; every unsatisfiable
call raises the proven lower bound, the first satisfiable call gives the
optimum together with an explicit certificate.



## Requirements

Python 3.11 or later.

```
pip install -r requirements.txt
```

The only dependency is [PySAT](https://pysathq.github.io/), which provides
CaDiCaL, the RC2 MaxSAT solver and the cardinality encodings.

## Quick start

Check the encoder against the exhaustive oracle on small instances:

```
python3 selftest.py
```

Run one instance:

```
python3 run_one.py benchmark/families/Parity_3.wcnf --budget 3600 --out results
```

The instance argument is either a path to a `.cnf` or `.wcnf` file, optionally
`gzip`- or `xz`-compressed, or a family name (`php3`, `2php4`, `parity5`, …)
that regenerates the formula instead of reading it. Useful options:

| option | effect |
|---|---|
| `--mode certificate \| refutation` | derive `λ` empty clauses, or one |
| `--budget S` | total seconds for the instance |
| `--ub-budget S` | seconds for the constructive upper bound; `0` skips it |
| `--solver NAME` | any solver available in PySAT (default `cadical153`) |

Each run writes `results/<name>.result.json` and one JSON record per SAT call
in `results/<name>.calls.jsonl`, so every bound can be traced back to the call
that proves it.

## Benchmarks

All instances are in `benchmark/`, in the WCNF format of the MaxSAT
Evaluation: the fifteen structured instances in `benchmark/families/`, the six
competition instances in `benchmark/competition/`. Every clause is soft with
unit cost, which is the unweighted setting of the paper. `benchmark.csv` lists,
for each file, its group, its number of variables `n`, its number of clauses
`M`, its optimum `λ`, how many of its clauses were originally hard, and its
checksums.

**Structured families.** Fifteen instances, in dual-rail encoding.

| family | parameters | description | optimum |
|---|---|---|---|
| `PHP_{k+1}_{k}` | `k = 3..7` | pigeonhole principle, `k+1` pigeons into `k` holes | `k(k+1)+1` |
| `2PHP_{k}` | `k = 3..7` | disjoint union of two copies of `PHP_{k+1}_{k}` | `2(k(k+1)+1)` |
| `Parity_{j}` | `j = 3,5,7,9,11` | Tseitin formula of the cycle `C_j`, i.e. two-colourability of an odd cycle | `j+1` |

In the dual-rail encoding a positive literal `x_i` becomes `¬n_i` and a
negative literal `¬x_i` becomes `¬p_i`; the consistency clauses `(¬p_i ∨ ¬n_i)`
and the unit clauses `(p_i)` and `(n_i)` are added. The files are shipped, but
`formula.py` also regenerates them exactly: passing `php3` instead of
`benchmark/families/PHP_4_3.wcnf` builds the same clause multiset, and
`raw:php3` gives the family without the dual-rail translation.

**MaxSAT Evaluation instances.** Six instances from the unweighted exact track
of the 2024 MaxSAT Evaluation, selected with `pick_competition.py` as the
smallest whose encoding `Φ_{K,λ}` fits within the memory limit. They carry hard
clauses, which the unweighted setting of the paper reads as soft clauses of
unit cost; `benchmark.csv` records how many clauses this concerns for each one,
and the reported optimum is that of the transformed instance. They are shipped
unmodified, under their original names. Two checksums are recorded for them:
`sha1` is the sha1 of the file as shipped, and `sha1_declared_by_source` is the
one written in the instance's own header, which identifies the source instance
before the evaluation standardised it and therefore differs from the first.

After adding or replacing an instance, rebuild the index:

```
python3 make_index.py
```

## Results

`table.csv` holds the numbers reported in the paper:

| column | meaning |
|---|---|
| `n`, `M` | variables and clauses of the MaxSAT instance |
| `lambda` | its optimum |
| `lower_bound_L` | largest `K` proven to admit no certificate |
| `K_star` | shortest certificate length, when established |
| `U` | length of a verified constructive certificate |
| `seconds` | cumulated solving time of the SAT calls |
| `refutation_K_star` | shortest max-refutation length |

An empty cell means the value was not obtained within the budget. To rebuild
the table from a `results/` directory:

```
python3 collect.py results
```

## Verification

No certificate is accepted on the strength of the encoding alone. Every model
is decoded and replayed by `verify.py`, which shares no code with the encoder:
it applies the MaxSAT-resolution rule itself, checks that both premises are
present in the current multiset, that the pivot has the right polarity, that
the resolvent is not a tautology, and that after every step the multiset is
still MaxSAT-equivalent to the input formula — exactly, by enumeration, while
the number of variables allows it, and otherwise on a large random sample of
assignments. Satisfiability of `Φ_{K,λ}` says the model fits the encoding; only
the verifier says the certificate is a MaxSAT-resolution derivation.

`selftest.py` additionally compares the encoder against an exhaustive
shortest-derivation oracle on small instances, where the optimum can be
computed by brute force.

## Reproducing the experiments

The runs reported in the paper used one core and 64 GB of memory per instance,
with a budget of 24 hours of cumulated SAT-solving time. Each instance is
independent, so they can be run in any order, sequentially:

```
mkdir -p results
for f in benchmark/*/*.wcnf; do
    python3 run_one.py "$f" --budget 86400 --mode certificate --out results
done
python3 collect.py results
```

or one per job on a batch system. The memory limit is what decides whether an
instance produces a bound at all: the two largest ones were stopped while
building `Φ_{K,λ}` for the first value of `K`.
