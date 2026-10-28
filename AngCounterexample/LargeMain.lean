import AngCounterexample.LargeLayer
import AngCounterexample.LargeConstruction
import AngCounterexample.LargeRealization
import AngCounterexample.LayerArithmetic

/-!
# Arbitrarily large large-prime counterexamples

The statement keeps the original subset-product definition. All construction
parameters disappear from the final theorem; the only assumptions are ε > 0
and the requested lower bound N.
-/

namespace AngLarge

/-- Ang's exponent-interval assertion fails for primes arbitrarily close to n
on a logarithmic scale, with n arbitrarily large. -/
theorem large_prime_counterexamples (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n p u a b c : ℕ, N ≤ n ∧ p.Prime ∧ n < p ^ 2 ∧
      (n : ℝ) ^ (1 - ε) < p ∧ ¬ p ∣ u ∧ a < b ∧ b < c ∧
      p ^ a * u ∈ products n ∧ p ^ c * u ∈ products n ∧
      p ^ b * u ∉ products n := by
  obtain ⟨t, ht, hεt⟩ := exists_degree ε hε
  obtain ⟨ℓ, G, n, p, hℓ, hN, hp, hnp, hlarge, hq, ⟨C⟩⟩ :=
    large_realization t (coeff t) ht (mul_succ_lt_three_coeff t) ε hεt N
  let j0 : Fin ℓ := ⟨0, by omega⟩
  obtain ⟨S1, S3, hS1, hS3, hprod1, hprod3, hzero1, hzero3, hgap⟩ :=
    saturated_residual_gap G hℓ ht (coeff_pos t) (layer_sum_coord_add_one t)
      C hp hnp hq j0
  obtain ⟨u, a, b, c, hpfree, hab, hbc, hlo, hhi, hmiss⟩ :=
    G.counterexample_from_neutral_gap hp hq j0 S1 S3 hS1 hS3 hprod1 hprod3 hzero1 hzero3 hgap
  exact ⟨n, p, u, a, b, c, hN, hp, hnp, hlarge, hpfree, hab, hbc, hlo, hhi, hmiss⟩

/-- The restriction of the exponent-interval conjecture to n < p² is false. -/
theorem large_prime_interval_conjecture_false :
    ¬ ∀ n p : ℕ, p.Prime → n < p ^ 2 →
      ∀ u a b c : ℕ, ¬ p ∣ u → a < b → b < c →
        p ^ a * u ∈ products n → p ^ c * u ∈ products n →
        p ^ b * u ∈ products n := by
  intro h
  obtain ⟨n, p, u, a, b, c, _hN, hp, hnp, _hlarge, hpfree, hab, hbc, hlo, hhi, hmiss⟩ :=
    large_prime_counterexamples 1 (by norm_num) 0
  exact hmiss (h n p hp hnp u a b c hpfree hab hbc hlo hhi)

end AngLarge
