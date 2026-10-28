import AngCounterexample.Forcing
import AngCounterexample.PrimeShift

/-! The forcing construction and extraction of its prime-free part. -/
open Finset
namespace AngLarge

lemma priced_gap (P : AdditivePrice) {n p H : ℕ} (hp : p.Prime) (hH : H ≠ 0)
    (S1 S3 : Finset ℕ) (hS1 : S1 ⊆ Icc 1 n) (hS3 : S3 ⊆ Icc 1 n)
    (hprod1 : S1.prod id = p * H) (hprod3 : S3.prod id = p ^ 3 * H)
    (hzero1 : ∀ x ∈ S1, P.val x = 0) (hzero3 : ∀ x ∈ S3, P.val x = 0)
    (hzero2 : P.val (p ^ 2 * H) = 0)
    (hgap : ∀ S : Finset ℕ, S ⊆ Icc 1 n →
      (∀ x ∈ S, P.val x = 0) → S.prod id ≠ p ^ 2 * H) :
    ∃ u a b c : ℕ, ¬ p ∣ u ∧ a < b ∧ b < c ∧
      p ^ a * u ∈ products n ∧ p ^ c * u ∈ products n ∧
      p ^ b * u ∉ products n := by
  let M := (P.forced n).prod id * H
  have hM : M ≠ 0 := mul_ne_zero (P.forced_prod_ne_zero n) hH
  apply exists_pfree_gap hp hM
  · have hm := P.lift_mem hS1 hzero1
    rw [hprod1] at hm
    convert hm using 1 <;> dsimp [M] <;> ring
  · have hm := P.lift_mem hS3 hzero3
    rw [hprod3] at hm
    convert hm using 1 <;> dsimp [M] <;> ring
  · have hm := P.lift_not_mem (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hH) hzero2 hgap
    convert hm using 1 <;> dsimp [M] <;> ring

end AngLarge
