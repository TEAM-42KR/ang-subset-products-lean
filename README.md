# Ang's conjecture on products of distinct integers fails for large primes: Lean 4 formalization

This repository contains machine-checked proofs, in Lean 4 with Mathlib, of two results of the paper
*Ang's conjecture on products of distinct integers fails for large primes* by Sungsoo Na (version 2.0.0,
October 28, 2026): the existence statement of Theorem 1.2 (the conjecture fails for primes p with p^2 > n),
and the disproof of the conjecture by the counterexample of Theorem 7.1 (the result of version 1.0.0 of the
paper). Nothing else of the paper is formalized here (see "What is not formalized").

## The conjecture

For a positive integer n let S(n) be the set of products of subsets of {1, ..., n}. Conjecture 1.1 of the paper
(Ang, 2020; OEIS A060957), as printed:

```tex
\begin{conjecture}[Ang, 2020]\label{conj:ang}
Let $p\le n$ be prime. If $m$ and $p^a m$ both lie in $S(n)$, then $p^k m\in S(n)$ for every $0<k<a$.
\end{conjecture}
```

In Lean, S(n) is `products n`, with the definition of the OEIS-Open benchmark problem
`oeis_60957_conjecture_0` (the keyword `private` removed, so that `Challenge.lean` and the proof can share it):

```lean
def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)
```

## What is proved

**Theorem 1.2** of the paper, as printed:

```tex
\begin{theorem}\label{thm:main}
For every $\varepsilon>0$ there are arbitrarily large integers $n$, primes $p$ with $p^2>n$ and $p>n^{1-\varepsilon}$,
and positive integers $u$ with $p\nmid u$, such that
\[
E_{n,p}(u)=K+\{0,1,3,4\}
\]
for some integer $K\ge 1$. In particular, $m=p^{K+1}u$ satisfies $m\in S(n)$ and $p^2m\in S(n)$, but $pm\notin S(n)$.
\end{theorem}
```

Here E_{n,p}(u) = {e >= 0 : p^e u in S(n)}. The formalized statement is its existence part (`Challenge.lean`;
proved in `Solution.lean` by `AngLarge.large_prime_counterexamples` of `AngCounterexample/LargeMain.lean`):

```lean
theorem large_prime_counterexamples (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n p u a b c : ℕ, N ≤ n ∧ p.Prime ∧ n < p ^ 2 ∧
      (n : ℝ) ^ (1 - ε) < p ∧ ¬ p ∣ u ∧ a < b ∧ b < c ∧
      p ^ a * u ∈ products n ∧ p ^ c * u ∈ products n ∧
      p ^ b * u ∉ products n
```

That is: for every real ε > 0 and every N there are n >= N, a prime p with p^2 > n and p > n^(1-ε), an integer u
with p not dividing u, and exponents a < b < c with a, c in E_{n,p}(u) and b not in E_{n,p}(u). There is no further
hypothesis. A corollary states that E_{n,p}(u) is not always an interval when p^2 > n:

```lean
theorem large_prime_interval_conjecture_false :
    ¬ ∀ n p : ℕ, p.Prime → n < p ^ 2 →
      ∀ u a b c : ℕ, ¬ p ∣ u → a < b → b < c →
        p ^ a * u ∈ products n → p ^ c * u ∈ products n →
        p ^ b * u ∈ products n
```

**Theorem 7.1** (the counterexample of version 1.0.0, with n = 1 399 108 927 917 911 481 and p = 1 118 479) gives the
negation of the benchmark statement of Conjecture 1.1:

```lean
theorem oeis_60957_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), ∀ p, Nat.Prime p → p ≤ n →
      ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
      ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n
```

proved by `Ang.disproof` in `AngCounterexample/Basic.lean` (with the explicit instance `Ang.counterexample`).
Every numerical fact of this proof is checked by the kernel; `native_decide` is not used.

## What is checked (trust boundary)

If `lake build` succeeds, then:

1. every module of the library `AngCounterexample`, `Challenge.lean`, `Solution.lean` and `Audit.lean` was checked
   by the Lean kernel;
2. `Audit.lean` (part of the default build) prints the axioms of the three public theorems, of `Ang.disproof`,
   `Ang.counterexample`, `AngLarge.large_prime_counterexamples`, `AngLarge.large_prime_interval_conjecture_false`,
   `AngLarge.saturated_residual_gap` and `AngLarge.large_realization`, checks the axioms of every declaration of the
   modules `AngCounterexample.*` and `Solution` (619 declarations), and fails if any of them depends on an axiom
   other than `propext`, `Classical.choice` and `Quot.sound` (in particular on `sorryAx`). In the recorded builds it
   printed `[propext, Classical.choice, Quot.sound]` for every listed theorem,
   `AUDIT declarations using sorry directly: []` and `AUDIT all development declarations checked: 619`
   (`receipts/aarch64/build_summary.txt`). Its last line, `AUDIT placeholders (0): []`, is a fixed message, not a
   computed result;
3. the only occurrences of `sorry` are the three statements of `Challenge.lean`, which restate the public theorems
   for comparison and are not imported by the proofs; the build reports them as three warnings. There is no
   `native_decide`, no `decide +native`, no `axiom` declaration, no `implemented_by` or `extern` attribute and no
   `admit`.

What you have to trust: the Lean 4 kernel (and the toolchain that runs it), the three standard axioms above, the
Mathlib definitions used in the statements (natural numbers, `Nat.Prime`, `Finset.Icc`, `Finset.powerset`,
`Finset.prod`, divisibility, the real power `(n : ℝ) ^ (1 - ε)`), and that `products` says what S(n) says.

`config.json` is a configuration for Comparator (`leanprover/comparator`), which checks that the three theorems of
`Solution.lean` have the same statements as in `Challenge.lean`, with identical definitions behind them, and use only
the permitted axioms. The configuration is included; a Comparator run is not part of this release.

## Rebuilding

Requirements: elan (the Lean toolchain manager), git, and an internet connection for the Mathlib cache.

From the repository root:

```
lake exe cache get
lake build
lake env lean Check.lean
```

Do not run `lake update` (the manifest pins every dependency).

Expected output: `lake build` ends with `Build completed successfully (8734 jobs).` Its output contains three
"declaration uses `sorry`" warnings, from `Challenge.lean`, a few linter warnings from the proof modules (unused
variables, unused simp arguments, deprecations and similar; no errors), and the `AUDIT` lines described above.
`Check.lean` prints the types of the three public theorems, of `AngLarge.saturated_residual_gap` and
`AngLarge.large_realization`, and their axioms `[propext, Classical.choice, Quot.sound]`.

The Lean source files, `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` of this repository are
byte-identical to those of the two clean builds recorded in `receipts/`, each made on a fresh machine from an empty
project directory with the precompiled Mathlib files from `lake exe cache get`:

- `receipts/aarch64/`: aarch64, 4 vCPUs, 30.8 GiB memory. `lake build`: 1 min 06 s wall clock, maximum resident
  memory 7.2 GiB; `Check.lean`: 3.6 s.
- `receipts/x86_64/`: x86_64, 8 vCPUs, 30 GiB memory. `lake exe cache get`: 69 s; `lake build`: 43 s;
  `Check.lean`: 3 s.

Each folder contains the unedited output of `lake build` and of `Check.lean`, a short summary of the build output
and a description of the machine; the timings are in `receipts/aarch64/build.time`, `receipts/aarch64/check.time`
(GNU time) and `receipts/x86_64/times.txt`.

## Versions

- Lean: `leanprover/lean4:v4.33.1` (`lean-toolchain`).
- Mathlib: tag `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474` (`lake-manifest.json`).

## Repository layout

- `Challenge.lean`: imports only Mathlib, repeats the definitions `A060957` and `products` of the benchmark, and
  states the three public theorems with `sorry`.
- `Solution.lean`: the same three statements, proved from the library.
- `AngCounterexample/Basic.lean`: the counterexample of Theorem 7.1 and `Ang.disproof` (unchanged from version 1.0.0
  of this repository).
- `AngCounterexample/LargeData.lean`: the prime grid, the complete layer of monomials of degree 1 to t, the
  coefficient and the cutoffs.
- `AngCounterexample/LayerArithmetic.lean`, `AngCounterexample/LayerProducts.lean`: layer sums and product identities.
- `AngCounterexample/LayerCore.lean`, `AngCounterexample/LayerClassify.lean`, `AngCounterexample/LayerBounds.lean`:
  prime valuations and the neutral factors.
- `AngCounterexample/LayerFinite.lean`, `AngCounterexample/LayerWitnesses.lean`, `AngCounterexample/LargeLayer.lean`:
  exclusion of the middle exponent and the explicit witnesses (saturated-layer lemma, `AngLarge.saturated_residual_gap`).
- `AngCounterexample/LayerSeparator.lean`, `AngCounterexample/LargePrice.lean`: balanced digits and the single integer
  price.
- `AngCounterexample/Forcing.lean`: the forcing lemma for distinct subset products.
- `AngCounterexample/RealizationPrimes.lean`, `AngCounterexample/RealizationGrowth.lean`,
  `AngCounterexample/RealizationBounds.lean`, `AngCounterexample/LargeRealization.lean`: the prime grid from Bertrand's
  postulate and the size inequalities (`AngLarge.large_realization`).
- `AngCounterexample/PrimeShift.lean`, `AngCounterexample/LargeGlue.lean`, `AngCounterexample/LargeConstruction.lean`:
  assembly of the forcing step and extraction of the part prime to p.
- `AngCounterexample/LargeMain.lean`: `AngLarge.large_prime_counterexamples` and
  `AngLarge.large_prime_interval_conjecture_false`.
- `AngCounterexample.lean`: imports the library.
- `Audit.lean`, `Check.lean`, `config.json`: the checks described above.
- `receipts/`: logs of the two clean builds.

The Lean code has 3340 lines.

## Differences from the route of the paper

Theorem 1.2 is proved along Sections 3 to 5 of the paper with m = 3, with four differences:

- The forms F_{i,j} are combined into a single integer price with base 4a+1, and the balanced-digit argument is
  applied only to divisors of the residual target, whose exponents are bounded. The forced set consists of all
  integers in [1, n] of negative price; this changes u, but not the argument.
- The coefficient a is defined as 1 plus a coordinate sum over the layer, and only a lower bound for it is used.
- The width is ℓ = ⌊3a/t⌋ + 1 instead of ℓ = ⌈3a/t⌉.
- The scale R is chosen sufficiently large by an eventual-domination argument instead of the explicit threshold of
  Table 1. Bertrand's postulate is taken from Mathlib (`Nat.exists_prime_lt_and_le_two_mul`).

Theorem 7.1 is proved along Section 7.2 with two simplifications: the 25 forms are combined into one form
L = Σ 10^(5i+j) λ_ij, whose negative-price integers form the forced set, and Lemma 7.2 and Corollary 7.3 are replaced by
a direct case analysis of the exponent matrices on which all λ_ij vanish.

## What is not formalized

- The exact description E_{n,p}(u) = K + {0, 1, m, m+1} of Theorem 4.5 and its counting polynomial (the formal proof
  gives only the three exponents a < b < c above), and Theorem 4.5 for m ≠ 3.
- The explicit examples of Theorem 1.3 (t = 2 and t = 3); their finite facts are checked by the programs of the
  supplementary material of the paper.
- Theorems 7.6 (n = 1125) and 7.7 (subset sums in simplices), and the computations of Remark 7.10 (n <= 56).
- For Theorem 7.1, the whole set E_{n,p}(u): the formal proof establishes the last sentence of the theorem.

The repository checks the statements above and nothing else.

## License

MIT (see `LICENSE`).

## Citation

If you use this repository, please cite the paper: Sungsoo Na, *Ang's conjecture on products of distinct integers
fails for large primes*, version 2.0.0, DOI: 10.5281/zenodo.23599288 (all versions: 10.5281/zenodo.23599287).

Assisted by AI.
