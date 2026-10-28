import AngCounterexample.LargeData

open Finset
namespace AngLarge

abbrev ri (i : Fin 3) : Fin 4 := ⟨i.val, by omega⟩

namespace Grid
variable {ℓ : ℕ} (G : Grid ℓ)

def v (x : ℕ) (i : Fin 4) (j : Fin ℓ) : ℕ := x.factorization (G.q i j)

lemma row_ne_zero (i : Fin 4) : G.row i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => (G.prime i j).ne_zero)
lemma small_ne_zero (i : Fin 3) : G.small i ≠ 0 := G.row_ne_zero (ri i)
lemma col_ne_zero (a : ℕ) (j : Fin ℓ) : G.col a j ≠ 0 := by
  exact mul_ne_zero (G.prime 3 j).ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (G.prime (ri i) j).ne_zero))
lemma H_ne_zero (a : ℕ) : G.H a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => G.col_ne_zero a j)
lemma monomial_ne_zero {t : ℕ} (α : Exponent t) : G.monomial α ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (G.small_ne_zero i))

lemma q_eq {i k : Fin 4} {j l : Fin ℓ} : G.q i j = G.q k l ↔ i = k ∧ j = l := by
  constructor
  · intro h; exact Prod.mk.inj (G.injective h)
  · rintro ⟨rfl, rfl⟩; rfl

lemma v_mul {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (i : Fin 4) (j : Fin ℓ) :
    G.v (x*y) i j = G.v x i j + G.v y i j := by
  simp [v, Nat.factorization_mul hx hy]
lemma v_prod {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ k ∈ S, f k ≠ 0) (i : Fin 4) (j : Fin ℓ) :
    G.v (∏ k ∈ S, f k) i j = ∑ k ∈ S, G.v (f k) i j := by
  rw [v, Nat.factorization_prod hf, Finsupp.finsetSum_apply]
  rfl

lemma row_fact (i : Fin 4) (r : ℕ) :
    (G.row i).factorization r = ∑ j, if G.q i j = r then 1 else 0 := by
  rw [row, Nat.factorization_prod (fun j _ => (G.prime i j).ne_zero),
    Finsupp.finsetSum_apply]
  simp_rw [(G.prime _ _).factorization, Finsupp.single_apply]

lemma v_row (i k : Fin 4) (j : Fin ℓ) :
    G.v (G.row i) k j = if k = i then 1 else 0 := by
  rw [v, G.row_fact]
  simp_rw [G.q_eq]
  by_cases h : k = i
  · subst k; simp
  · simp [h, Ne.symm h]

lemma v_small (i k : Fin 3) (j : Fin ℓ) :
    G.v (G.small i) (ri k) j = if k = i then 1 else 0 := by
  change G.v (G.row (ri i)) (ri k) j = _
  rw [G.v_row]
  have h : ri k = ri i ↔ k = i := by
    constructor
    · intro he; apply Fin.ext; exact congrArg (fun z : Fin 4 => z.val) he
    · rintro rfl; rfl
  simp [h]
lemma v_small_large (i : Fin 3) (j : Fin ℓ) : G.v (G.small i) 3 j = 0 := by
  change G.v (G.row (ri i)) 3 j = 0
  rw [G.v_row, if_neg]
  intro h; have := congrArg Fin.val h; have := i.isLt; simp [ri] at *; omega

lemma v_col_small (a : ℕ) (l j : Fin ℓ) (i : Fin 3) :
    G.v (G.col a l) (ri i) j = if j = l then a else 0 := by
  unfold col
  rw [G.v_mul (G.prime 3 l).ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (G.prime (ri k) l).ne_zero))]
  rw [G.v_prod _ _ (fun k _ => pow_ne_zero _ (G.prime (ri k) l).ne_zero)]
  simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    (G.prime _ _).factorization, Finsupp.single_apply]
  have h3 : ∀ k : Fin 3, (3 : Fin 4) ≠ ri k := by
    intro k h; have := congrArg Fin.val h; have := k.isLt; simp [ri] at *; omega
  have hr : ∀ k : Fin 3, ri k = ri i ↔ k = i := by
    intro k; constructor
    · intro h; apply Fin.ext; exact congrArg (fun z : Fin 4 => z.val) h
    · rintro rfl; rfl
  simp_rw [G.q_eq]
  simp [h3, hr, eq_comm]
  split_ifs <;> simp_all

lemma v_col_large (a : ℕ) (l j : Fin ℓ) :
    G.v (G.col a l) 3 j = if j = l then 1 else 0 := by
  unfold col
  rw [G.v_mul (G.prime 3 l).ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (G.prime (ri k) l).ne_zero))]
  rw [G.v_prod _ _ (fun k _ => pow_ne_zero _ (G.prime (ri k) l).ne_zero)]
  simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    (G.prime _ _).factorization, Finsupp.single_apply]
  have h3 : ∀ k : Fin 3, ri k ≠ (3 : Fin 4) := by
    intro k h; have := congrArg Fin.val h; have := k.isLt; simp [ri] at *; omega
  simp_rw [G.q_eq]
  simp [h3, eq_comm]

lemma v_H_small (a : ℕ) (i : Fin 3) (j : Fin ℓ) : G.v (G.H a) (ri i) j = a := by
  rw [H, G.v_prod _ _ (fun j _ => G.col_ne_zero a j)]
  simp_rw [G.v_col_small]
  simp
lemma v_H_large (a : ℕ) (j : Fin ℓ) : G.v (G.H a) 3 j = 1 := by
  rw [H, G.v_prod _ _ (fun j _ => G.col_ne_zero a j)]
  simp_rw [G.v_col_large]
  simp
lemma v_monomial {t : ℕ} (α : Exponent t) (i : Fin 3) (j : Fin ℓ) :
    G.v (G.monomial α) (ri i) j = (α i).val := by
  rw [monomial, G.v_prod _ _ (fun k _ => pow_ne_zero _ (G.small_ne_zero k))]
  simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  change (∑ k, (α k).val * G.v (G.small k) (ri i) j) = _
  simp_rw [G.v_small]
  simp
lemma v_monomial_large {t : ℕ} (α : Exponent t) (j : Fin ℓ) :
    G.v (G.monomial α) 3 j = 0 := by
  rw [monomial, G.v_prod _ _ (fun k _ => pow_ne_zero _ (G.small_ne_zero k))]
  simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  change (∑ k, (α k).val * G.v (G.small k) 3 j) = _
  simp [G.v_small_large]

lemma monomial_injective (t : ℕ) (j0 : Fin ℓ) :
    Function.Injective (fun α : Exponent t => G.monomial α) := by
  intro α β h
  funext i
  apply Fin.ext
  have := congrArg (fun x => G.v x (ri i) j0) h
  simpa only [G.v_monomial] using this

lemma form_mul (a : ℕ) (j0 : Fin ℓ) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (i : Fin 3) (j : Fin ℓ) :
    G.form a j0 (x*y) i j = G.form a j0 x i j + G.form a j0 y i j := by
  simp only [form, Nat.factorization_mul hx hy, Finsupp.add_apply]
  push_cast
  ring
lemma form_one (a : ℕ) (j0 : Fin ℓ) (i : Fin 3) (j : Fin ℓ) :
    G.form a j0 1 i j = 0 := by simp [form]
lemma form_col (a : ℕ) (j0 l : Fin ℓ) (i : Fin 3) (j : Fin ℓ) :
    G.form a j0 (G.col a l) i j = 0 := by
  change (G.v (G.col a l) (ri i) j : ℤ) - G.v (G.col a l) (ri i) j0 -
    (a : ℤ) * ((G.v (G.col a l) 3 j : ℤ) - G.v (G.col a l) 3 j0) = 0
  simp only [G.v_col_small, G.v_col_large]
  split_ifs <;> simp <;> ring
lemma form_monomial (a : ℕ) (j0 : Fin ℓ) {t : ℕ} (α : Exponent t)
    (i : Fin 3) (j : Fin ℓ) : G.form a j0 (G.monomial α) i j = 0 := by
  change (G.v (G.monomial α) (ri i) j : ℤ) - G.v (G.monomial α) (ri i) j0 -
    (a : ℤ) * ((G.v (G.monomial α) 3 j : ℤ) - G.v (G.monomial α) 3 j0) = 0
  simp [G.v_monomial, G.v_monomial_large]
lemma form_small (a : ℕ) (j0 : Fin ℓ) (k i : Fin 3) (j : Fin ℓ) :
    G.form a j0 (G.small k) i j = 0 := by
  change (G.v (G.small k) (ri i) j : ℤ) - G.v (G.small k) (ri i) j0 -
    (a : ℤ) * ((G.v (G.small k) 3 j : ℤ) - G.v (G.small k) 3 j0) = 0
  simp [G.v_small, G.v_small_large]
lemma form_large (a : ℕ) (j0 : Fin ℓ) (i : Fin 3) (j : Fin ℓ) :
    G.form a j0 (G.row 3) i j = 0 := by
  change (G.v (G.row 3) (ri i) j : ℤ) - G.v (G.row 3) (ri i) j0 -
    (a : ℤ) * ((G.v (G.row 3) 3 j : ℤ) - G.v (G.row 3) 3 j0) = 0
  simp only [G.v_row]
  ring

end Grid
end AngLarge
