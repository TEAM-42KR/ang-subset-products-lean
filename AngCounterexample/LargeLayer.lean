import AngCounterexample.LayerWitnesses
import AngCounterexample.LayerProducts

/-! The conditional degree-t saturated residual gap, with three small rows. -/
open Finset

namespace AngLarge
namespace Grid
variable {ℓ : ℕ} (G : Grid ℓ)

lemma witness3_product {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (t a : ℕ) (hbal : ∀ i : Fin 3, (∑ α ∈ layer t, (α i).val) + 1 = a)
    (j0 : Fin ℓ) : (G.witness3 p t).prod id = p^3 * G.H a := by
  have hnot : G.row 3 ∉ G.monoSet t ∪ G.tags p := by
    simp only [mem_union, not_or]
    exact ⟨G.large_not_mono j0,G.large_not_tags hp hq⟩
  have hmul : (∏ i : Fin 3, G.small i ^ (∑ α ∈ layer t, (α i).val)) *
      (∏ i : Fin 3, G.small i) = ∏ i : Fin 3, G.small i ^ a := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_succ,hbal i]
  rw [witness3,prod_insert hnot,prod_union (G.mono_tags_disjoint hp hq t),
    G.monoSet_product t j0,G.tags_product hp j0,G.prod_layer_monomial_eq_prod_sum]
  calc
    G.row 3 * ((∏ i : Fin 3, G.small i ^ (∑ α ∈ layer t, (α i).val)) *
      (p^3 * ∏ i : Fin 3, G.small i)) =
      p^3 * (G.row 3 * ((∏ i : Fin 3, G.small i ^ (∑ α ∈ layer t, (α i).val)) *
        ∏ i : Fin 3, G.small i)) := by ring
    _ = p^3 * G.H a := by rw [hmul,G.H_eq_row_mul_prod_small_pow]

end Grid

/-- Two neutral subset products with the middle tagging exponent excluded. -/
theorem saturated_residual_gap {ℓ t a n p : ℕ} (G : Grid ℓ)
    (_hℓ : 2 ≤ ℓ) (_ht : 2 ≤ t) (_ha : 1 ≤ a)
    (hbal : ∀ i : Fin 3, (∑ α ∈ layer t, (α i).val) + 1 = a)
    (C : Cutoffs G t a n p) (hp : p.Prime) (hnp : n < p^2)
    (hq : ∀ i j, G.q i j ≠ p) (j0 : Fin ℓ) :
    ∃ S1 S3 : Finset ℕ,
      S1 ⊆ Icc 1 n ∧ S3 ⊆ Icc 1 n ∧
      S1.prod id = p * G.H a ∧ S3.prod id = p^3 * G.H a ∧
      (∀ x ∈ S1, ∀ i j, G.form a j0 x i j = 0) ∧
      (∀ x ∈ S3, ∀ i j, G.form a j0 x i j = 0) ∧
      ∀ S : Finset ℕ, S ⊆ Icc 1 n →
        (∀ x ∈ S, ∀ i j, G.form a j0 x i j = 0) → S.prod id ≠ p^2 * G.H a := by
  exact ⟨G.witness1 p a,G.witness3 p t,G.witness1_subset C hp j0,
    G.witness3_subset C hp,G.witness1_product hp hq a,
    G.witness3_product hp hq t a hbal j0,G.witness1_forms hp hq a j0,
    G.witness3_forms hp hq a t j0,fun S hS hf => G.residual_exclusion C hp hnp hq hbal j0 S hS hf⟩

end AngLarge
