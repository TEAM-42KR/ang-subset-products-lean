import AngCounterexample.LayerBounds

open Finset
namespace AngLarge
namespace Grid
variable {ℓ : ℕ} (G : Grid ℓ)

def monoSet (t : ℕ) : Finset ℕ := (layer t).image (fun α => G.monomial α)
def tags (p : ℕ) : Finset ℕ := univ.image (fun i : Fin 3 => p * G.small i)
def columns (a : ℕ) : Finset ℕ := univ.image (G.col a)

lemma monomial_fact_p {p : ℕ} (hq : ∀ i j, G.q i j ≠ p) {t : ℕ} (α : Exponent t) :
    (G.monomial α).factorization p = 0 := G.rowMon_fact_p hq _
lemma tag_fact_p {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p) (i : Fin 3) :
    (p * G.small i).factorization p = 1 := by
  rw [Nat.factorization_mul hp.ne_zero (G.small_ne_zero i), Finsupp.add_apply]
  change p.factorization p + (G.row (ri i)).factorization p = 1
  simp [hp.factorization, G.row_fact_p hq]
lemma v_p {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (i : Fin 4) (j : Fin ℓ) : G.v p i j = 0 := by
  simpa using G.v_p_pow hp hq 1 i j
lemma v_tag {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (k i : Fin 3) (j : Fin ℓ) :
    G.v (p * G.small k) (ri i) j = if i = k then 1 else 0 := by
  rw [G.v_mul hp.ne_zero (G.small_ne_zero k), G.v_p hp hq, zero_add, G.v_small]
lemma v_tag_large {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (k : Fin 3) (j : Fin ℓ) : G.v (p * G.small k) 3 j = 0 := by
  rw [G.v_mul hp.ne_zero (G.small_ne_zero k), G.v_p hp hq, G.v_small_large, add_zero]
lemma small_injective (j0 : Fin ℓ) : Function.Injective G.small := by
  intro i k h
  have hv := congrArg (fun x => G.v x (ri i) j0) h
  rw [G.v_small, G.v_small, if_pos rfl] at hv
  by_contra hik
  simp [hik] at hv
lemma small_ne_one (j0 : Fin ℓ) (i : Fin 3) : G.small i ≠ 1 := by
  intro h
  have hv := congrArg (fun x => G.v x (ri i) j0) h
  rw [G.v_small] at hv
  simp [v] at hv
lemma tags_injective {p : ℕ} (hp : p.Prime) (j0 : Fin ℓ) :
    Function.Injective (fun i : Fin 3 => p * G.small i) := by
  intro i k h
  exact G.small_injective j0 (Nat.eq_of_mul_eq_mul_left hp.pos h)
lemma v_row_large_small (i : Fin 3) (j : Fin ℓ) : G.v (G.row 3) (ri i) j = 0 := by
  rw [G.v_row,if_neg]
  intro h; have := congrArg (fun z : Fin 4 => z.val) h; have := i.isLt; simp [ri] at *; omega

lemma monoSet_sum (t : ℕ) (i : Fin 3) (j0 j : Fin ℓ) :
    ∑ x ∈ G.monoSet t, G.v x (ri i) j = ∑ α ∈ layer t, (α i).val := by
  rw [monoSet, Finset.sum_image (G.monomial_injective t j0).injOn]
  simp_rw [G.v_monomial]
lemma tags_sum_p {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p) (j0 : Fin ℓ) :
    ∑ x ∈ G.tags p, x.factorization p = 3 := by
  rw [tags, Finset.sum_image (G.tags_injective hp j0).injOn]
  simp [G.tag_fact_p hp hq]

/-- The saturated layer excludes the middle tagging exponent. -/
theorem residual_exclusion {t a n p : ℕ} (C : Cutoffs G t a n p)
    (hp : p.Prime) (hnp : n < p^2) (hq : ∀ i j, G.q i j ≠ p)
    (hbal : ∀ i : Fin 3, (∑ α ∈ layer t, (α i).val) + 1 = a)
    (j0 : Fin ℓ) (S : Finset ℕ) (hS : S ⊆ Icc 1 n)
    (hf : ∀ x ∈ S, ∀ i j, G.form a j0 x i j = 0) :
    S.prod id ≠ p^2 * G.H a := by
  intro hprod
  have hpos : ∀ x ∈ S, x ≠ 0 := by
    intro x hx; have := (Finset.mem_Icc.mp (hS hx)).1; omega
  have hclass : ∀ x ∈ S, x = 1 ∨ x = p ∨ (∃ α ∈ layer t, x = G.monomial α) ∨
      x = G.row 3 ∨ (∃ j, x = G.col a j) ∨ ∃ i, x = p * G.small i := by
    intro x hx
    apply G.classify_residual C hp hnp hq j0 (hpos x hx) (Finset.mem_Icc.mp (hS hx)).2
    · rw [← hprod]; exact Finset.dvd_prod_of_mem id hx
    · exact hf x hx
  have hpsum : (∑ x ∈ S, x.factorization p) = 2 := by
    have hh := congrArg (fun x : ℕ => x.factorization p) hprod
    change (∏ x ∈ S, x).factorization p = _ at hh
    rw [Nat.factorization_prod hpos, Finsupp.finsetSum_apply,
      Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a),
      Finsupp.add_apply, fact_p_pow hp, G.H_fact_p hq, add_zero] at hh
    exact hh
  have hsum : ∀ i j, (∑ x ∈ S, G.v x (ri i) j) = a := by
    intro i j
    have hh := congrArg (fun x : ℕ => G.v x (ri i) j) hprod
    rw [G.v_prod S id hpos,
      G.v_mul (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a),
      G.v_p_pow hp hq, G.v_H_small, zero_add] at hh
    exact hh
  have htag : ∃ i, p * G.small i ∈ S := by
    by_contra hn
    push_neg at hn
    have hle : (∑ x ∈ S, x.factorization p) ≤ ∑ x ∈ ({p} : Finset ℕ), x.factorization p := by
      apply Finset.sum_le_sum_of_ne_zero
      intro x hx hv
      rcases hclass x hx with rfl | rfl | ⟨α,hα,rfl⟩ | rfl | ⟨j,rfl⟩ | ⟨i,rfl⟩
      · simp at hv
      · simp
      · exact (hv (G.monomial_fact_p hq α)).elim
      · exact (hv (G.row_fact_p hq 3)).elim
      · exact (hv (G.col_fact_p hq a j)).elim
      · exact (hn i hx).elim
    simp [hp.factorization,hpsum] at hle
  obtain ⟨i0,hi0⟩ := htag
  have hncol : ∀ j, G.col a j ∉ S := by
    intro j hj
    have hne : p * G.small i0 ≠ G.col a j := by
      intro h
      have he := congrArg (fun x : ℕ => x.factorization p) h
      rw [G.tag_fact_p hp hq, G.col_fact_p hq] at he
      omega
    have hpair : ({p * G.small i0, G.col a j} : Finset ℕ) ⊆ S := by
      intro x hx; simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hle := Finset.sum_le_sum_of_subset (f := fun x => G.v x (ri i0) j) hpair
    rw [hsum i0 j] at hle
    simp [hne,G.v_tag hp hq,G.v_col_small] at hle
  have halltags : ∀ i, p * G.small i ∈ S := by
    intro i
    by_contra hni
    have hle : (∑ x ∈ S, G.v x (ri i) j0) ≤ ∑ x ∈ G.monoSet t, G.v x (ri i) j0 := by
      apply Finset.sum_le_sum_of_ne_zero
      intro x hx hv
      rcases hclass x hx with rfl | rfl | ⟨α,hα,rfl⟩ | rfl | ⟨j,rfl⟩ | ⟨k,rfl⟩
      · simp [v] at hv
      · exact (hv (G.v_p hp hq _ _)).elim
      · exact mem_image.mpr ⟨α,hα,rfl⟩
      · exact (hv (G.v_row_large_small i j0)).elim
      · exact (hncol j hx).elim
      · have hik : i = k := by
          by_contra hne
          exact hv (by simp [G.v_tag hp hq,hne])
        subst k
        exact (hni hx).elim
    rw [hsum i j0, G.monoSet_sum t i j0 j0] at hle
    have := hbal i
    omega
  have htags : G.tags p ⊆ S := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact halltags i
  have hle := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x.factorization p) htags
  rw [G.tags_sum_p hp hq j0,hpsum] at hle
  omega

end Grid
end AngLarge
