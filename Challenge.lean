import Mathlib

/-!
# Ang's conjecture (OEIS A060957) is false: challenge statement

Imports only Mathlib. The two definitions are those of the OEIS-Open benchmark problem
`oeis_60957_conjecture_0`, verbatim except that `products` is no longer `private` (so that the
same definition can be used by `Solution.lean`). The benchmark states the conjecture as

```
theorem oeis_60957_conjecture_0 (n : ℕ) :
    ∀ p, Nat.Prime p → p ≤ n →
    ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
    ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n := by sorry
```

The theorem below is its negation. `Solution.lean` proves it, and `config.json` lets Comparator
check that the proof uses the standard axioms only.
-/

open Finset Nat

/--
A060957: Number of different products (including the empty product) of any subset of $\{1, 2, 3, \dots, n\}$.
-/
def A060957 (n : ℕ) : ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id) |>.card

-- Convenience definition for the set of products
def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)

/-- Ang's conjecture (`oeis_60957_conjecture_0`) is false. -/
theorem oeis_60957_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), ∀ p, Nat.Prime p → p ≤ n →
      ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
      ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n := by
  sorry

/-- Large-prime result (version 2.0.0). -/
theorem large_prime_counterexamples (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n p u a b c : ℕ, N ≤ n ∧ p.Prime ∧ n < p ^ 2 ∧
      (n : ℝ) ^ (1 - ε) < p ∧ ¬ p ∣ u ∧ a < b ∧ b < c ∧
      p ^ a * u ∈ products n ∧ p ^ c * u ∈ products n ∧
      p ^ b * u ∉ products n := by
  sorry

/-- Large-prime result (version 2.0.0). -/
theorem large_prime_interval_conjecture_false :
    ¬ ∀ n p : ℕ, p.Prime → n < p ^ 2 →
      ∀ u a b c : ℕ, ¬ p ∣ u → a < b → b < c →
        p ^ a * u ∈ products n → p ^ c * u ∈ products n →
        p ^ b * u ∈ products n := by
  sorry
