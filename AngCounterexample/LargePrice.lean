import AngCounterexample.Forcing
import AngCounterexample.LayerClassify
import AngCounterexample.LayerSeparator

/-! A scalar additive price encoding every grid form in balanced base. -/

open Finset

namespace AngLarge
namespace Grid

variable {ℓ : ℕ} (G : Grid ℓ)

/-- The base for digits bounded in absolute value by twice the row exponent. -/
def scalarPriceBase (a : ℕ) : ℤ := 4 * (a : ℤ) + 1

/-- All `3 * ℓ` forms, in the explicit row-major finite-product enumeration. -/
def scalarPriceDigit (a : ℕ) (j0 : Fin ℓ) (x : ℕ) (r : Fin (3 * ℓ)) : ℤ :=
  let ij := (finProdFinEquiv : Fin 3 × Fin ℓ ≃ Fin (3 * ℓ)).symm r
  G.form a j0 x ij.1 ij.2

/-- The integer-valued additive price uses every form, including the zero forms
at the reference column. The exponent enumeration is a bijection, not a subsample. -/
def scalarPrice (a : ℕ) (j0 : Fin ℓ) : AdditivePrice where
  val x := ∑ r : Fin (3 * ℓ), scalarPriceBase a ^ r.val * G.scalarPriceDigit a j0 x r
  one := by
    simp [scalarPriceDigit, G.form_one]
  mul := by
    intro x y hx hy
    simp only [scalarPriceDigit, G.form_mul a j0 hx hy, mul_add,
      Finset.sum_add_distrib]

lemma scalarPrice_val_def (a : ℕ) (j0 : Fin ℓ) (x : ℕ) :
    (G.scalarPrice a j0).val x =
      ∑ r : Fin (3 * ℓ), scalarPriceBase a ^ r.val * G.scalarPriceDigit a j0 x r :=
  rfl

lemma scalarPrice_val_eq_zero {a x : ℕ} (j0 : Fin ℓ)
    (hf : ∀ i j, G.form a j0 x i j = 0) : (G.scalarPrice a j0).val x = 0 := by
  simp [scalarPrice, scalarPriceDigit, hf]

/-- A box bound on the valuations bounds every form by twice `a`. -/
lemma scalarPrice_form_abs_le {a x : ℕ} (j0 : Fin ℓ)
    (hb : ∀ i j, G.v x (ri i) j ≤ a) (hl : ∀ j, G.v x 3 j ≤ 1)
    (i : Fin 3) (j : Fin ℓ) : |G.form a j0 x i j| ≤ 2 * (a : ℤ) := by
  have hs : |(G.v x (ri i) j : ℤ) - G.v x (ri i) j0| ≤ (a : ℤ) := by
    rw [abs_le]
    have h0 := hb i j0
    have hj := hb i j
    constructor <;> omega
  have hl' : |(G.v x 3 j : ℤ) - G.v x 3 j0| ≤ 1 := by
    rw [abs_le]
    have h0 := hl j0
    have hj := hl j
    constructor <;> omega
  change |(G.v x (ri i) j : ℤ) - G.v x (ri i) j0 -
    (a : ℤ) * ((G.v x 3 j : ℤ) - G.v x 3 j0)| ≤ _
  calc
    _ ≤ |(G.v x (ri i) j : ℤ) - G.v x (ri i) j0| +
        |(a : ℤ) * ((G.v x 3 j : ℤ) - G.v x 3 j0)| := abs_sub _ _
    _ = |(G.v x (ri i) j : ℤ) - G.v x (ri i) j0| +
        (a : ℤ) * |(G.v x 3 j : ℤ) - G.v x 3 j0| := by
      rw [abs_mul]
      have ha : |(a : ℤ)| = (a : ℤ) := abs_of_nonneg (Nat.cast_nonneg a)
      rw [ha]
    _ ≤ (a : ℤ) + (a : ℤ) * 1 :=
      add_le_add hs (mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg a))
    _ = 2 * (a : ℤ) := by ring

/-- On the valuation box, scalar zero is equivalent to simultaneous form zero. -/
lemma forms_eq_zero_of_scalarPrice_val_eq_zero {a x : ℕ} (j0 : Fin ℓ)
    (hb : ∀ i j, G.v x (ri i) j ≤ a) (hl : ∀ j, G.v x 3 j ≤ 1)
    (hz : (G.scalarPrice a j0).val x = 0) :
    ∀ i j, G.form a j0 x i j = 0 := by
  have hbase : 2 * ((2 * a : ℕ) : ℤ) < scalarPriceBase a := by
    simp only [scalarPriceBase, Nat.cast_mul, Nat.cast_ofNat]
    omega
  have hd : ∀ r : Fin (3 * ℓ), |G.scalarPriceDigit a j0 x r| ≤ ((2 * a : ℕ) : ℤ) := by
    intro r
    simpa only [scalarPriceDigit, Nat.cast_mul, Nat.cast_ofNat] using
      G.scalarPrice_form_abs_le j0 hb hl
        ((finProdFinEquiv : Fin 3 × Fin ℓ ≃ Fin (3 * ℓ)).symm r).1
        ((finProdFinEquiv : Fin 3 × Fin ℓ ≃ Fin (3 * ℓ)).symm r).2
  have he := balanced_digits_zero (2 * a) (scalarPriceBase a)
    (G.scalarPriceDigit a j0 x) hbase hd hz
  intro i j
  simpa only [scalarPriceDigit, Equiv.symm_apply_apply] using
    he ((finProdFinEquiv : Fin 3 × Fin ℓ ≃ Fin (3 * ℓ)) (i, j))

/-- An arbitrary power of an outside prime does not enlarge the grid valuation box. -/
lemma scalarPrice_bounds_of_dvd {p a e x : ℕ} (hp : p.Prime)
    (hq : ∀ i j, G.q i j ≠ p) (hxd : x ∣ p ^ e * G.H a) :
    (∀ i j, G.v x (ri i) j ≤ a) ∧ (∀ j, G.v x 3 j ≤ 1) := by
  have hmax : p ^ e * G.H a ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a)
  have hx : x ≠ 0 := ne_zero_of_dvd_ne_zero hmax hxd
  have hle := (Nat.factorization_le_iff_dvd hx hmax).mpr hxd
  have hv (i : Fin 4) (j : Fin ℓ) : G.v x i j ≤ G.v (p ^ e * G.H a) i j :=
    hle (G.q i j)
  constructor
  · intro i j
    have h := hv (ri i) j
    simpa only [G.v_mul (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a),
      G.v_p_pow hp hq, G.v_H_small, zero_add] using h
  · intro j
    have h := hv 3 j
    simpa only [G.v_mul (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a),
      G.v_p_pow hp hq, G.v_H_large, zero_add] using h

/-- In particular this applies to every divisor of `p^2 * H a`. -/
lemma forms_eq_zero_of_scalarPrice_val_eq_zero_of_dvd {p a e x : ℕ}
    (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p) (j0 : Fin ℓ)
    (hxd : x ∣ p ^ e * G.H a) (hz : (G.scalarPrice a j0).val x = 0) :
    ∀ i j, G.form a j0 x i j = 0 := by
  obtain ⟨hb, hl⟩ := G.scalarPrice_bounds_of_dvd hp hq hxd
  exact G.forms_eq_zero_of_scalarPrice_val_eq_zero j0 hb hl hz

lemma scalarPrice_val_eq_zero_iff_of_dvd {p a e x : ℕ}
    (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p) (j0 : Fin ℓ)
    (hxd : x ∣ p ^ e * G.H a) :
    (G.scalarPrice a j0).val x = 0 ↔ ∀ i j, G.form a j0 x i j = 0 := by
  constructor
  · exact G.forms_eq_zero_of_scalarPrice_val_eq_zero_of_dvd hp hq j0 hxd
  · exact G.scalarPrice_val_eq_zero j0

lemma form_H (a : ℕ) (j0 : Fin ℓ) (i : Fin 3) (j : Fin ℓ) :
    G.form a j0 (G.H a) i j = 0 := by
  change (G.v (G.H a) (ri i) j : ℤ) - G.v (G.H a) (ri i) j0 -
    (a : ℤ) * ((G.v (G.H a) 3 j : ℤ) - G.v (G.H a) 3 j0) = 0
  simp [G.v_H_small, G.v_H_large]

lemma scalarPrice_val_H (a : ℕ) (j0 : Fin ℓ) :
    (G.scalarPrice a j0).val (G.H a) = 0 :=
  G.scalarPrice_val_eq_zero j0 (G.form_H a j0)

lemma scalarPrice_val_prime_pow {p : ℕ} (hp : p.Prime)
    (hq : ∀ i j, G.q i j ≠ p) (a e : ℕ) (j0 : Fin ℓ) :
    (G.scalarPrice a j0).val (p ^ e) = 0 :=
  G.scalarPrice_val_eq_zero j0 (G.form_p_pow hp hq a e j0)

/-- Every tagged target has scalar price zero, for every tagging exponent. -/
lemma scalarPrice_val_prime_pow_H {p : ℕ} (hp : p.Prime)
    (hq : ∀ i j, G.q i j ≠ p) (a e : ℕ) (j0 : Fin ℓ) :
    (G.scalarPrice a j0).val (p ^ e * G.H a) = 0 := by
  rw [(G.scalarPrice a j0).mul (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a),
    G.scalarPrice_val_prime_pow hp hq, G.scalarPrice_val_H, zero_add]

end Grid
end AngLarge
