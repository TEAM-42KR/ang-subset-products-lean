import AngCounterexample.RealizationBounds
import AngCounterexample.RealizationGrowth

/-!
Bertrand realization of the saturated-layer cutoffs, with unbounded n and
p > n^(1-epsilon).  The scale is allowed to be sufficiently large instead of
using the explicit numerical threshold in the paper's eleven-inequality table.
-/

open Filter

namespace AngLarge

open Realization

set_option maxRecDepth 2048

/-- Section 5, with the coefficient condition separated from its combinatorial evaluation. -/
theorem large_realization (t a : ℕ) (ht : 2 ≤ t) (ha : t * (t + 1) < 3 * a)
    (ε : ℝ) (hε : 1 / ((t : ℝ) + 1) < ε) (N : ℕ) :
    ∃ ℓ : ℕ, ∃ G : Grid ℓ, ∃ n p : ℕ,
      2 ≤ ℓ ∧ N ≤ n ∧ p.Prime ∧ n < p ^ 2 ∧ (n : ℝ) ^ (1 - ε) < p ∧
      (∀ i j, G.q i j ≠ p) ∧ Nonempty (Cutoffs G t a n p) := by
  let ℓ := 3 * a / t + 1
  let v := 2 * ℓ
  let h := 2 * t + 1
  let w := min (h * ℓ) (6 * a + h)
  let z := max (h * ℓ) (6 * a + h)
  let F := v * t
  let E := v * (t + 1)
  let Cs := 2 ^ (3 * ℓ)
  let Cl := 2 ^ ℓ
  let U := Cs ^ ℓ
  let C := max (Cl ^ ℓ) (Cl * Cs ^ (3 * a))
  let K := 2 * U
  obtain ⟨hℓt, hv, hFw, hzE, h2h, hhF⟩ := parameter_gaps t a ht ha
  change t + 2 ≤ ℓ at hℓt
  change 0 < v at hv
  change F < w at hFw
  change z < E at hzE
  change 2 < h at h2h
  change h < F at hhF
  have hℓ : 2 ≤ ℓ := by omega
  have hU : 0 < U := by dsimp [U, Cs]; positivity
  have hK : 0 < K := by dsimp [K]; omega
  have hK1 : 1 ≤ K := by omega
  have hC : 0 < C := by
    dsimp [C, Cl, Cs]
    exact lt_of_lt_of_le (by positivity : 0 < (2 ^ ℓ) ^ ℓ) (le_max_left _ _)
  have hF : 0 < F := by dsimp [F]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hEF : E = v + F := by dsimp [E, F]; ring
  have hFE : F < E := by omega
  have hvF : v < F := by dsimp [F]; nlinarith
  have hEwv : E < w + v := by omega
  have hEww : E < w * 2 := by omega
  have hEFvv : E < F + v * 2 := by omega
  have hEFw : E < F + w := by omega
  have hEFF : E < F * 2 := by omega
  have hreal : (E : ℝ) * (1 - ε) < F := by
    have htR : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hε' := (div_lt_iff₀ htR).mp hε
    have hinner : ((t : ℝ) + 1) * (1 - ε) < t := by nlinarith
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have hmul := mul_lt_mul_of_pos_left hinner hvR
    simpa only [E, F, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hmul
  have ev1 : ∀ᶠ r : ℕ in atTop, Cs * (K * r) ^ 2 < (K * r) ^ h := by
    simpa only [one_mul] using eventually_scaled_lt Cs 1 K 2 h (by omega) hK h2h
  have ev2 : ∀ᶠ r : ℕ in atTop, U ^ t * (K * r) ^ F < (K * r) ^ E := by
    simpa only [one_mul] using eventually_scaled_lt (U ^ t) 1 K F E (by omega) hK hFE
  have ev3 : ∀ᶠ r : ℕ in atTop, C * (K * r) ^ z < (K * r) ^ E := by
    simpa only [one_mul] using eventually_scaled_lt C 1 K z E (by omega) hK hzE
  have ev4 : ∀ᶠ r : ℕ in atTop, (K * r) ^ E < (K * r) ^ (w + v) := by
    simpa only [one_mul] using eventually_scaled_lt 1 1 K E (w + v) (by omega) hK hEwv
  have ev5 : ∀ᶠ r : ℕ in atTop, (K * r) ^ E < (K * r) ^ (w * 2) := by
    simpa only [one_mul] using eventually_scaled_lt 1 1 K E (w * 2) (by omega) hK hEww
  have ev6 : ∀ᶠ r : ℕ in atTop, (K * r) ^ E < r ^ F * (K * r) ^ (v * 2) := by
    simpa only [one_mul] using eventually_product_lt 1 1 K E F (v * 2) (by omega) hK hEFvv
  have ev7 : ∀ᶠ r : ℕ in atTop, (K * r) ^ E < r ^ F * (K * r) ^ w := by
    simpa only [one_mul] using eventually_product_lt 1 1 K E F w (by omega) hK hEFw
  have ev8 : ∀ᶠ r : ℕ in atTop, (K * r) ^ E < (r ^ F) ^ 2 := by
    simpa only [one_mul, pow_zero, mul_one, ← pow_mul] using
      eventually_product_lt 1 1 K E (F * 2) 0 (by omega) hK (by omega)
  have ev9 : ∀ᶠ r : ℕ in atTop, Cs * (K * r) ^ 2 < r ^ F := by
    simpa only [one_mul, pow_zero, mul_one] using
      eventually_product_lt Cs 1 K 2 F 0 (by omega) hK (by omega)
  have ev10 : ∀ᶠ r : ℕ in atTop, Cl * (K * r) ^ h < r ^ F := by
    simpa only [one_mul, pow_zero, mul_one] using
      eventually_product_lt Cl 1 K h F 0 (by omega) hK (by omega)
  have ev11 := eventually_growth K E F ε hreal
  have allEv : ∀ᶠ r : ℕ in atTop,
      N ≤ r ∧ 2 ≤ r ∧ Cs * (K * r) ^ 2 < (K * r) ^ h ∧
      U ^ t * (K * r) ^ F < (K * r) ^ E ∧ C * (K * r) ^ z < (K * r) ^ E ∧
      (K * r) ^ E < (K * r) ^ (w + v) ∧ (K * r) ^ E < (K * r) ^ (w * 2) ∧
      (K * r) ^ E < r ^ F * (K * r) ^ (v * 2) ∧
      (K * r) ^ E < r ^ F * (K * r) ^ w ∧ (K * r) ^ E < (r ^ F) ^ 2 ∧
      Cs * (K * r) ^ 2 < r ^ F ∧ Cl * (K * r) ^ h < r ^ F ∧
      (((K * r) ^ E : ℕ) : ℝ) ^ (1 - ε) < (r ^ F : ℕ) := by
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 2,
      ev1, ev2, ev3, ev4, ev5, ev6, ev7, ev8, ev9, ev10, ev11] with r hN hr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨hN, hr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  obtain ⟨r, hrN, hr2, hsep, hDt, hB, hbd, hbsq, hsd, hsb, hpsq, hqs, hql, hgr⟩ := allEv.exists
  let R := K * r
  let n := R ^ E
  let d := R ^ v + 1
  let D := U * R ^ v
  let b := R ^ w
  let B := C * R ^ z
  have hr0 : 0 < r := by omega
  have hR : 0 < R := mul_pos hK hr0
  have hR1 : 1 ≤ R := hR
  obtain ⟨G, hs, hl⟩ := prime_grid ℓ R h (by omega) hR hsep
  obtain ⟨p, hp, hgp, hpg⟩ := Nat.exists_prime_lt_and_le_two_mul (r ^ F) (by positivity)
  have hp0 : 0 < p := hp.pos
  have hsmall : ∀ i, d ≤ G.small i ∧ G.small i ≤ D := small_bounds G (by omega) hR hs
  have hlarge : (b ≤ G.row 3 ∧ G.row 3 ≤ B) ∧
      ∀ j, b ≤ G.col a j ∧ G.col a j ≤ B := large_bounds G hR1 hs hl
  have hKF : 2 * U ≤ K ^ F := by
    change K ≤ K ^ F
    exact le_self_pow hK1 (by omega)
  have hDp : D * p ≤ n := by
    calc
      D * p ≤ (U * R ^ v) * (2 * r ^ F) := Nat.mul_le_mul_left _ hpg
      _ = (2 * U) * (R ^ v * r ^ F) := by ring
      _ ≤ K ^ F * (R ^ v * r ^ F) := Nat.mul_le_mul_right _ hKF
      _ = n := by
        change K ^ F * (R ^ v * r ^ F) = R ^ E
        simp only [R, hEF, pow_add, mul_pow]
        ring
  have hsD : D ≤ n / p := (Nat.le_div_iff_mul_le hp0).mpr hDp
  have hsd' : n / p < d ^ 2 := by
    apply (Nat.div_lt_iff_lt_mul hp0).mpr
    have hd : R ^ (v * 2) ≤ d ^ 2 := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left (by dsimp [d]; omega) 2
    have hh := Nat.mul_le_mul hgp.le hd
    calc
      n < r ^ F * R ^ (v * 2) := hsd
      _ ≤ p * d ^ 2 := hh
      _ = d ^ 2 * p := Nat.mul_comm _ _
  have hsb' : n / p < b := by
    apply (Nat.div_lt_iff_lt_mul hp0).mpr
    calc
      n < r ^ F * b := hsb
      _ ≤ p * b := Nat.mul_le_mul_right b hgp.le
      _ = b * p := Nat.mul_comm _ _
  have hDt' : D ^ t ≤ n := by
    change (U * R ^ v) ^ t ≤ n
    rw [mul_pow, ← pow_mul R v t]
    exact hDt.le
  have hB' : B ≤ n := hB.le
  have hnd : n < d ^ (t + 1) := by
    have hh := Nat.pow_lt_pow_left (Nat.lt_succ_self (R ^ v)) (show t + 1 ≠ 0 by omega)
    simpa only [d, n, E, pow_mul] using hh
  have hnbd : n < b * d := by
    have hh : n < b * R ^ v := by simpa only [b, pow_add] using hbd
    exact hh.trans_le (Nat.mul_le_mul_left b (by dsimp [d]; omega))
  have hnbb : n < b ^ 2 := by simpa only [b, pow_mul] using hbsq
  have hnp : n < p ^ 2 := hpsq.trans_le (Nat.pow_le_pow_left hgp.le 2)
  have hnN : N ≤ n := by
    have hrR : r ≤ R := by
      change r ≤ K * r
      simpa only [one_mul] using Nat.mul_le_mul_right r hK1
    have hRn : R ≤ n := by
      have hh := Nat.pow_le_pow_right hR (show 1 ≤ E by omega)
      simpa only [pow_one, n] using hh
    exact hrN.trans (hrR.trans hRn)
  have hgrowth : (n : ℝ) ^ (1 - ε) < p := by
    exact hgr.trans (by exact_mod_cast hgp)
  have hnot : ∀ i j, G.q i j ≠ p := by
    intro i j
    by_cases hi : i.val < 3
    · have hq := (hs ⟨i.val, hi⟩ j).2
      have he : (⟨i.val, by omega⟩ : Fin 4) = i := Fin.ext rfl
      rw [he] at hq
      exact (hq.trans_lt (hqs.trans hgp)).ne
    · have he : i = 3 := Fin.ext (by have := i.isLt; omega)
      subst i
      exact ((hl j).2.trans_lt (hql.trans hgp)).ne
  refine ⟨ℓ, G, n, p, hℓ, hnN, hp, hnp, hgrowth, hnot, ?_⟩
  exact ⟨{
    d := d
    D := D
    b := b
    B := B
    d_pos := Nat.succ_pos _
    small_bounds := hsmall
    large_bounds := hlarge.1
    col_bounds := hlarge.2
    D_le := hsD
    s_lt_dsq := hsd'
    s_lt_b := hsb'
    Dt_le := hDt'
    B_le := hB'
    n_lt_dpow := hnd
    n_lt_bd := hnbd
    n_lt_bsq := hnbb }⟩

end AngLarge

#print axioms AngLarge.large_realization
