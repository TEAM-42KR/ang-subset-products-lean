import Mathlib

/-! A finite balanced-digit separator over the integers. -/

open Finset

namespace AngLarge

/-- If the base exceeds twice the uniform digit bound, a finite zero expansion
has only zero digits. The proof removes the least significant digit using
integer divisibility, so it needs neither logarithms nor geometric-series bounds. -/
theorem balanced_digits_zero {k : ℕ} (M : ℕ) (B : ℤ) (d : Fin k → ℤ)
    (hB : 2 * (M : ℤ) < B) (hd : ∀ r, |d r| ≤ (M : ℤ))
    (hsum : (∑ r, B ^ r.val * d r) = 0) : ∀ r, d r = 0 := by
  have hBpos : 0 < B := by omega
  have hMB : (M : ℤ) < B := by omega
  induction k with
  | zero =>
      intro r
      exact Fin.elim0 r
  | succ k ih =>
      have hsplit : (∑ r : Fin (k + 1), B ^ r.val * d r) =
          d 0 + B * (∑ r : Fin k, B ^ r.val * d r.succ) := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [pow_succ]
        ring
      rw [hsplit] at hsum
      have hdiv : B ∣ d 0 := by
        refine ⟨-(∑ r : Fin k, B ^ r.val * d r.succ), ?_⟩
        rw [mul_neg]
        linarith only [hsum]
      have hzero : d 0 = 0 :=
        Int.eq_zero_of_abs_lt_dvd hdiv (lt_of_le_of_lt (hd 0) hMB)
      have htail : (∑ r : Fin k, B ^ r.val * d r.succ) = 0 := by
        rw [hzero, zero_add] at hsum
        exact (mul_eq_zero.mp hsum).resolve_left (ne_of_gt hBpos)
      have hz := ih (fun r => d r.succ) (fun r => hd r.succ) htail
      intro r
      exact Fin.cases hzero (fun j => hz j) r

theorem balanced_digits_sum_eq_zero_iff {k : ℕ} (M : ℕ) (B : ℤ) (d : Fin k → ℤ)
    (hB : 2 * (M : ℤ) < B) (hd : ∀ r, |d r| ≤ (M : ℤ)) :
    (∑ r, B ^ r.val * d r) = 0 ↔ ∀ r, d r = 0 := by
  constructor
  · exact balanced_digits_zero M B d hB hd
  · intro h
    simp [h]

end AngLarge
