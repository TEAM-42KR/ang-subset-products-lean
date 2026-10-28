import AngCounterexample.LayerFinite

open Finset
namespace AngLarge
namespace Grid
variable {ℓ : ℕ} (G : Grid ℓ)

def witness1 (p a : ℕ) : Finset ℕ := insert p (G.columns a)
def witness3 (p t : ℕ) : Finset ℕ := insert (G.row 3) (G.monoSet t ∪ G.tags p)

lemma columns_injective (a : ℕ) : Function.Injective (G.col a) := by
  intro j k h
  have he := congrArg (fun x => G.v x 3 j) h
  rw [G.v_col_large,G.v_col_large,if_pos rfl] at he
  by_contra hjk
  simp [hjk] at he

lemma witness1_subset {t a n p : ℕ} (C : Cutoffs G t a n p)
    (hp : p.Prime) (j0 : Fin ℓ) : G.witness1 p a ⊆ Icc 1 n := by
  have hsmall : 1 ≤ G.small (0 : Fin 3) := Nat.pos_of_ne_zero (G.small_ne_zero 0)
  have hs : 1 ≤ n / p := hsmall.trans ((C.small_bounds 0).2.trans C.D_le)
  have hp_le : p ≤ n := by
    have h := (Nat.le_div_iff_mul_le hp.pos).mp hs
    simpa using h
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact mem_Icc.mpr ⟨hp.pos,hp_le⟩
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hx
    exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (G.col_ne_zero a j), (C.col_bounds j).2.trans C.B_le⟩

lemma witness3_subset {t a n p : ℕ} (C : Cutoffs G t a n p)
    (hp : p.Prime) : G.witness3 p t ⊆ Icc 1 n := by
  have hD : 1 ≤ C.D := le_trans (show 1 ≤ G.small 0 from Nat.pos_of_ne_zero (G.small_ne_zero 0)) (C.small_bounds 0).2
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (G.row_ne_zero 3), C.large_bounds.2.trans C.B_le⟩
  · rcases mem_union.mp hx with hx | hx
    · obtain ⟨α,hα,rfl⟩ := mem_image.mp hx
      have ht := (mem_filter.mp hα).2.2
      have hu : G.monomial α ≤ C.D ^ t := by
        exact (G.rowMon_upper C.D (fun i => (α i).val) (fun i => (C.small_bounds i).2)).trans
          (pow_le_pow_right' hD ht)
      exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (G.monomial_ne_zero α),hu.trans C.Dt_le⟩
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      refine mem_Icc.mpr ⟨Nat.mul_pos hp.pos (Nat.pos_of_ne_zero (G.small_ne_zero i)),?_⟩
      have hle := (Nat.le_div_iff_mul_le hp.pos).mp ((C.small_bounds i).2.trans C.D_le)
      simpa only [mul_comm] using hle

lemma witness1_forms {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (a : ℕ) (j0 : Fin ℓ) : ∀ x ∈ G.witness1 p a, ∀ i j, G.form a j0 x i j = 0 := by
  intro x hx i j
  rcases mem_insert.mp hx with rfl | hx
  · simpa using G.form_p_pow hp hq a 1 j0 i j
  · obtain ⟨l,_,rfl⟩ := mem_image.mp hx
    exact G.form_col a j0 l i j
lemma witness3_forms {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (a t : ℕ) (j0 : Fin ℓ) : ∀ x ∈ G.witness3 p t, ∀ i j, G.form a j0 x i j = 0 := by
  intro x hx i j
  rcases mem_insert.mp hx with rfl | hx
  · exact G.form_large a j0 i j
  · rcases mem_union.mp hx with hx | hx
    · obtain ⟨α,_,rfl⟩ := mem_image.mp hx
      exact G.form_monomial a j0 α i j
    · obtain ⟨k,_,rfl⟩ := mem_image.mp hx
      rw [G.form_mul a j0 hp.ne_zero (G.small_ne_zero k),G.form_small]
      have he := G.form_p_pow hp hq a 1 j0 i j
      simpa using he

lemma witness1_product {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (a : ℕ) : (G.witness1 p a).prod id = p * G.H a := by
  have hnot : p ∉ G.columns a := by
    intro h
    obtain ⟨j,_,he⟩ := mem_image.mp h
    have hv := congrArg (fun x : ℕ => x.factorization p) he
    rw [G.col_fact_p hq] at hv
    simp [hp.factorization] at hv
  rw [witness1, prod_insert hnot, columns,
    Finset.prod_image (G.columns_injective a).injOn]
  rfl

lemma mono_tags_disjoint {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p) (t : ℕ) :
    Disjoint (G.monoSet t) (G.tags p) := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  obtain ⟨α,_,rfl⟩ := mem_image.mp hx
  obtain ⟨i,_,he⟩ := mem_image.mp ht
  have hv := congrArg (fun x : ℕ => x.factorization p) he
  rw [G.tag_fact_p hp hq,G.monomial_fact_p hq] at hv
  omega
lemma large_not_mono {t : ℕ} (j0 : Fin ℓ) : G.row 3 ∉ G.monoSet t := by
  intro h
  obtain ⟨α,_,he⟩ := mem_image.mp h
  have hv := congrArg (fun x => G.v x 3 j0) he
  rw [G.v_monomial_large,G.v_row,if_pos rfl] at hv
  omega
lemma large_not_tags {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p) :
    G.row 3 ∉ G.tags p := by
  intro h
  obtain ⟨i,_,he⟩ := mem_image.mp h
  have hv := congrArg (fun x : ℕ => x.factorization p) he
  rw [G.tag_fact_p hp hq,G.row_fact_p hq] at hv
  omega
lemma tags_product {p : ℕ} (hp : p.Prime) (j0 : Fin ℓ) :
    (G.tags p).prod id = p^3 * ∏ i, G.small i := by
  rw [tags, Finset.prod_image (G.tags_injective hp j0).injOn]
  simp [Finset.prod_mul_distrib]
lemma monoSet_product (t : ℕ) (j0 : Fin ℓ) :
    (G.monoSet t).prod id = ∏ α ∈ layer t, G.monomial α := by
  rw [monoSet, Finset.prod_image (G.monomial_injective t j0).injOn]
  rfl

end Grid
end AngLarge
