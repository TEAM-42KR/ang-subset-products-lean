import AngCounterexample.LayerCore
import AngCounterexample.LayerArithmetic

/-! Exact rearrangements of the target and the full layer product. -/

open Finset

namespace AngLarge
namespace Grid

variable {ℓ : ℕ} (G : Grid ℓ)

/-- The column product is the last row times the common small-row powers. -/
theorem H_eq_row_mul_prod_small_pow (a : ℕ) :
    G.H a = G.row 3 * ∏ i : Fin 3, G.small i ^ a := by
  classical
  unfold H col
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_pow]
  rfl

/-- The product over the entire finite layer, with explicit coordinate-sum exponents. -/
theorem prod_layer_monomial_eq_prod_sum (t : ℕ) :
    (∏ α ∈ layer t, G.monomial α) =
      ∏ i : Fin 3, G.small i ^ (∑ α ∈ layer t, (α i).val) := by
  classical
  rw [G.prod_layer_monomial]
  apply Finset.prod_congr rfl
  intro i _
  rw [layer_sum_coord_eq_coeff_sub_one]

end Grid
end AngLarge
