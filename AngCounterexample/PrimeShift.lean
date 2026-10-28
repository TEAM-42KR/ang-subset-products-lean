import AngCounterexample.Basic

/-! Extracting the prime-free part preserves a gap at consecutive exponents. -/

namespace AngLarge

lemma exists_pfree_gap {n p M : ℕ} (hp : p.Prime) (hM : M ≠ 0)
    (hlo : p * M ∈ products n) (hhi : p ^ 3 * M ∈ products n)
    (hgap : p ^ 2 * M ∉ products n) :
    ∃ u a b c : ℕ, ¬ p ∣ u ∧ a < b ∧ b < c ∧
      p ^ a * u ∈ products n ∧ p ^ c * u ∈ products n ∧
      p ^ b * u ∉ products n := by
  obtain ⟨k, u, hpu, hMu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM p hp.ne_one
  have he (e : ℕ) : p ^ (k + e) * u = p ^ e * M := by
    rw [hMu, pow_add]
    ring
  refine ⟨u, k + 1, k + 2, k + 3, hpu, by omega, by omega, ?_, ?_, ?_⟩
  · rw [he, pow_one]
    exact hlo
  · rw [he]
    exact hhi
  · rw [he]
    exact hgap

lemma exists_degree (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, 2 ≤ t ∧ 1 / ((t : ℝ) + 1) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  let t := max 2 k
  have ht : 2 ≤ t := le_max_left _ _
  have hkt : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast (le_max_right 2 k)
  have hprod : 1 < (t : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (lt_of_lt_of_le hk hkt)
  refine ⟨t, ht, (div_lt_iff₀ (by positivity : 0 < (t : ℝ) + 1)).mpr ?_⟩
  nlinarith

end AngLarge
