import AngCounterexample.LargeData

/-! Coordinate symmetry and elementary lower bounds for the entire finite layer. -/

open Finset

namespace AngLarge

/-- Permuting the three coordinates preserves the exponent box. -/
def permuteExponent {t : ℕ} (e : Equiv.Perm (Fin 3)) : Exponent t ≃ Exponent t where
  toFun α i := α (e i)
  invFun α i := α (e.symm i)
  left_inv α := by funext i; simp
  right_inv α := by funext i; simp

@[simp] theorem degree_permuteExponent {t : ℕ} (e : Equiv.Perm (Fin 3))
    (α : Exponent t) : degree (permuteExponent e α) = degree α := by
  exact Equiv.sum_comp e (fun i => (α i).val)

/-- Every coordinate has the same total over the whole layer. -/
theorem layer_sum_coord_eq (t : ℕ) (i : Fin 3) :
    (∑ α ∈ layer t, (α i).val) = ∑ α ∈ layer t, (α 0).val := by
  classical
  let e := permuteExponent (t := t) (Equiv.swap (0 : Fin 3) i)
  refine Finset.sum_equiv e ?_ ?_
  · intro α
    dsimp only [e]
    simp [layer]
  · intro α _
    change (α i).val = (α ((Equiv.swap (0 : Fin 3) i) 0)).val
    simp

/-- The coefficient uses the entire layer, including in each coordinate. -/
theorem layer_sum_coord_add_one (t : ℕ) (i : Fin 3) :
    (∑ α ∈ layer t, (α i).val) + 1 = coeff t := by
  rw [layer_sum_coord_eq, coeff]
  omega

theorem coeff_pos (t : ℕ) : 0 < coeff t := by
  unfold coeff
  omega

theorem layer_sum_coord_eq_coeff_sub_one (t : ℕ) (i : Fin 3) :
    (∑ α ∈ layer t, (α i).val) = coeff t - 1 := by
  have := layer_sum_coord_add_one t i
  omega

private theorem twice_sum_fin_positive (t : ℕ) :
    2 * (∑ j : Fin t, (j.val + 1)) = t * (t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      nlinarith

/-- The positive points of the first coordinate axis already give a triangular sum. -/
theorem twice_layer_sum_coord_ge (t : ℕ) :
    t * (t + 1) ≤ 2 * (∑ α ∈ layer t, (α 0).val) := by
  classical
  let axis : Fin t → Exponent t := fun j i =>
    if i = 0 then ⟨j.val + 1, by omega⟩ else 0
  have hval (j : Fin t) : ((axis j) 0).val = j.val + 1 := by
    simp [axis]
  have hdeg (j : Fin t) : degree (axis j) = j.val + 1 := by
    simp [degree, axis, Fin.sum_univ_succ]
  have hmem (j : Fin t) : axis j ∈ layer t := by
    simp only [layer, mem_filter, mem_univ, true_and]
    rw [hdeg]
    constructor <;> omega
  have hinj : Function.Injective axis := by
    intro a b h
    have hv := congrArg (fun α : Exponent t => (α 0).val) h
    rw [hval, hval] at hv
    apply Fin.ext
    omega
  have hsub : (univ.image axis) ⊆ layer t := by
    intro α hα
    rcases mem_image.mp hα with ⟨j, _, rfl⟩
    exact hmem j
  have hle : (∑ α ∈ univ.image axis, (α 0).val) ≤
      ∑ α ∈ layer t, (α 0).val :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have himage : (∑ α ∈ univ.image axis, (α 0).val) =
      ∑ j : Fin t, (j.val + 1) := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    simp only [hval]
  rw [himage] at hle
  have hsum := twice_sum_fin_positive t
  nlinarith

/-- The numerical inequality needed to choose the number of columns.
The elementary axis lower bound proves this even without assuming `2 ≤ t`. -/
theorem mul_succ_lt_three_coeff (t : ℕ) : t * (t + 1) < 3 * coeff t := by
  have h := twice_layer_sum_coord_ge t
  unfold coeff
  nlinarith

theorem mul_succ_lt_three_coeff_of_two_le (t : ℕ) (_ht : 2 ≤ t) :
    t * (t + 1) < 3 * coeff t :=
  mul_succ_lt_three_coeff t

namespace Grid

/-- The product of all ordinary layer monomials has the same exponent in each row. -/
theorem prod_layer_monomial {ℓ : ℕ} (G : Grid ℓ) (t : ℕ) :
    (∏ α ∈ layer t, G.monomial α) = ∏ i, G.small i ^ (coeff t - 1) := by
  classical
  simp only [monomial]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_pow_eq_pow_sum, layer_sum_coord_eq_coeff_sub_one]

end Grid

end AngLarge
