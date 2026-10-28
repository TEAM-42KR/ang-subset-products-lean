import AngCounterexample.LargeData

/-! Power-scale separation and the near-linear growth estimate. -/

open Filter

namespace AngLarge.Realization

lemma eventually_monomial_lt (c d e f : ℕ) (hd : 0 < d) (hef : e < f) :
    ∀ᶠ r : ℕ in atTop, c * r ^ e < d * r ^ f := by
  filter_upwards [eventually_ge_atTop (c + 1)] with r hr
  have hcr : c < r := by omega
  have hr1 : 1 ≤ r := by omega
  have hr0 : 0 < r ^ e := pow_pos (by omega) _
  calc
    c * r ^ e < r * r ^ e := Nat.mul_lt_mul_of_pos_right hcr hr0
    _ = r ^ (e + 1) := by rw [pow_succ]; ring
    _ ≤ r ^ f := Nat.pow_le_pow_right hr1 (by omega)
    _ ≤ d * r ^ f := by simpa using Nat.mul_le_mul_right (r ^ f) (show 1 ≤ d by omega)

lemma eventually_scaled_lt (c d K e f : ℕ) (hd : 0 < d) (hK : 0 < K) (hef : e < f) :
    ∀ᶠ r : ℕ in atTop, c * (K * r) ^ e < d * (K * r) ^ f := by
  have hh := eventually_monomial_lt (c * K ^ e) (d * K ^ f) e f
    (mul_pos hd (pow_pos hK _)) hef
  simpa only [mul_pow, mul_assoc] using hh

lemma eventually_product_lt (c d K e f h : ℕ) (hd : 0 < d) (hK : 0 < K)
    (hef : e < f + h) :
    ∀ᶠ r : ℕ in atTop, c * (K * r) ^ e < d * r ^ f * (K * r) ^ h := by
  have hh := eventually_monomial_lt (c * K ^ e) (d * K ^ h) e (f + h)
    (mul_pos hd (pow_pos hK _)) hef
  simpa only [mul_pow, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh

lemma eventually_rpow_mul_lt (c u v : ℝ) (huv : u < v) :
    ∀ᶠ r : ℕ in atTop, c * (r : ℝ) ^ u < (r : ℝ) ^ v := by
  have ht : Tendsto (fun r : ℕ => (r : ℝ) ^ (v - u)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_gt_atTop c), eventually_ge_atTop 1] with r hr hr1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  calc
    c * (r : ℝ) ^ u < (r : ℝ) ^ (v - u) * (r : ℝ) ^ u :=
      mul_lt_mul_of_pos_right hr (Real.rpow_pos_of_pos hr0 _)
    _ = (r : ℝ) ^ v := by rw [← Real.rpow_add hr0]; congr 1; ring

lemma eventually_growth (K E F : ℕ) (ε : ℝ)
    (h : (E : ℝ) * (1 - ε) < F) :
    ∀ᶠ r : ℕ in atTop, (((K * r) ^ E : ℕ) : ℝ) ^ (1 - ε) < (r ^ F : ℕ) := by
  have hh := eventually_rpow_mul_lt ((K : ℝ) ^ ((E : ℝ) * (1 - ε)))
    ((E : ℝ) * (1 - ε)) F h
  filter_upwards [hh] with r hr
  rw [Nat.cast_pow, Nat.cast_mul, ← Real.rpow_natCast,
    ← Real.rpow_mul (mul_nonneg (Nat.cast_nonneg K) (Nat.cast_nonneg r)),
    Real.mul_rpow (Nat.cast_nonneg K) (Nat.cast_nonneg r)]
  simpa only [Nat.cast_pow, Real.rpow_natCast] using hr

lemma parameter_gaps (t a : ℕ) (ht : 2 ≤ t) (ha : t * (t + 1) < 3 * a) :
    let ℓ := 3 * a / t + 1
    let v := 2 * ℓ
    let h := 2 * t + 1
    let w := min (h * ℓ) (6 * a + h)
    let z := max (h * ℓ) (6 * a + h)
    t + 2 ≤ ℓ ∧ 0 < v ∧ v * t < w ∧ z < v * (t + 1) ∧
      2 < h ∧ h < v * t := by
  dsimp
  have ht0 : 0 < t := by omega
  have hlo := Nat.mul_div_le (3 * a) t
  have hup : 3 * a < t * (3 * a / t + 1) := by
    have := Nat.mod_lt (3 * a) ht0
    have := Nat.mod_add_div (3 * a) t
    nlinarith
  have hℓ : t + 2 ≤ 3 * a / t + 1 := by nlinarith
  have hw1 : 2 * (3 * a / t + 1) * t < (2 * t + 1) * (3 * a / t + 1) := by
    nlinarith
  have hw2 : 2 * (3 * a / t + 1) * t < 6 * a + (2 * t + 1) := by
    nlinarith
  have hz1 : (2 * t + 1) * (3 * a / t + 1) < 2 * (3 * a / t + 1) * (t + 1) := by
    nlinarith
  have hz2 : 6 * a + (2 * t + 1) < 2 * (3 * a / t + 1) * (t + 1) := by
    nlinarith
  exact ⟨hℓ, by omega, lt_min hw1 hw2, max_lt hz1 hz2, by omega, by nlinarith⟩

end AngLarge.Realization
