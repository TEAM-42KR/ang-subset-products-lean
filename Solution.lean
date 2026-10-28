import AngCounterexample.Basic
import AngCounterexample.LargeMain

/-!
# Ang's conjecture (OEIS A060957) is false: solution

The statement of `Challenge.lean`, proved by `Ang.disproof` from `AngCounterexample/Basic.lean`.
The definitions `A060957` and `products` used here are those of `AngCounterexample/Basic.lean`,
which are the same as in `Challenge.lean`.
-/

open Finset Nat

/-- Ang's conjecture (`oeis_60957_conjecture_0`) is false. -/
theorem oeis_60957_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), ∀ p, Nat.Prime p → p ≤ n →
      ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
      ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n :=
  Ang.disproof

/-- Large-prime result (version 2.0.0). -/
theorem large_prime_counterexamples (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n p u a b c : ℕ, N ≤ n ∧ p.Prime ∧ n < p ^ 2 ∧
      (n : ℝ) ^ (1 - ε) < p ∧ ¬ p ∣ u ∧ a < b ∧ b < c ∧
      p ^ a * u ∈ products n ∧ p ^ c * u ∈ products n ∧
      p ^ b * u ∉ products n := 
  AngLarge.large_prime_counterexamples ε hε N

/-- Large-prime result (version 2.0.0). -/
theorem large_prime_interval_conjecture_false :
    ¬ ∀ n p : ℕ, p.Prime → n < p ^ 2 →
      ∀ u a b c : ℕ, ¬ p ∣ u → a < b → b < c →
        p ^ a * u ∈ products n → p ^ c * u ∈ products n →
        p ^ b * u ∈ products n := 
  AngLarge.large_prime_interval_conjecture_false
