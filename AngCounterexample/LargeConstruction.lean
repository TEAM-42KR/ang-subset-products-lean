import AngCounterexample.LargeGlue
import AngCounterexample.LargePrice

/-! Applying the additive forcing construction to the neutral residual gap. -/
open Finset

namespace AngLarge
namespace Grid

variable {ℓ : ℕ} (G : Grid ℓ)

lemma counterexample_from_neutral_gap {n p a : ℕ} (hp : p.Prime)
    (hq : ∀ i j, G.q i j ≠ p) (j0 : Fin ℓ)
    (S1 S3 : Finset ℕ) (hS1 : S1 ⊆ Icc 1 n) (hS3 : S3 ⊆ Icc 1 n)
    (hprod1 : S1.prod id = p * G.H a) (hprod3 : S3.prod id = p ^ 3 * G.H a)
    (hzero1 : ∀ x ∈ S1, ∀ i j, G.form a j0 x i j = 0)
    (hzero3 : ∀ x ∈ S3, ∀ i j, G.form a j0 x i j = 0)
    (hgap : ∀ S : Finset ℕ, S ⊆ Icc 1 n →
      (∀ x ∈ S, ∀ i j, G.form a j0 x i j = 0) → S.prod id ≠ p ^ 2 * G.H a) :
    ∃ u b₀ b₁ b₂ : ℕ, ¬ p ∣ u ∧ b₀ < b₁ ∧ b₁ < b₂ ∧
      p ^ b₀ * u ∈ products n ∧ p ^ b₂ * u ∈ products n ∧
      p ^ b₁ * u ∉ products n := by
  apply priced_gap (G.scalarPrice a j0) hp (G.H_ne_zero a) S1 S3 hS1 hS3 hprod1 hprod3
  · intro x hx
    exact G.scalarPrice_val_eq_zero j0 (hzero1 x hx)
  · intro x hx
    exact G.scalarPrice_val_eq_zero j0 (hzero3 x hx)
  · exact G.scalarPrice_val_prime_pow_H hp hq a 2 j0
  · intro S hS hz heq
    apply hgap S hS ?_ heq
    intro x hx
    apply G.forms_eq_zero_of_scalarPrice_val_eq_zero_of_dvd (e := 2) hp hq j0 ?_ (hz x hx)
    rw [← heq]
    exact Finset.dvd_prod_of_mem id hx

end Grid
end AngLarge
