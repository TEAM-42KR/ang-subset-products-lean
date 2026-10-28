import AngCounterexample.Basic

/-! A general saturation/forcing lemma for products of distinct positive integers. -/
open Finset

namespace AngLarge

structure AdditivePrice where
  val : ℕ → ℤ
  one : val 1 = 0
  mul : ∀ {x y : ℕ}, x ≠ 0 → y ≠ 0 → val (x * y) = val x + val y

namespace AdditivePrice

variable (P : AdditivePrice)

def forced (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun x => P.val x < 0)

lemma prod_val {ι : Type*} (S : Finset ι) (g : ι → ℕ)
    (hg : ∀ x ∈ S, g x ≠ 0) : P.val (∏ x ∈ S, g x) = ∑ x ∈ S, P.val (g x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [P.one]
  | insert x S hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      P.mul (hg x (mem_insert_self x S))
        (prod_ne_zero_iff.mpr (fun y hy => hg y (mem_insert_of_mem hy))),
      ih (fun y hy => hg y (mem_insert_of_mem hy))]

lemma forced_sub (n : ℕ) : P.forced n ⊆ Icc 1 n := filter_subset _ _

lemma forced_prod_ne_zero (n : ℕ) : (P.forced n).prod id ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro x hx
  change x ≠ 0
  have := mem_Icc.mp (P.forced_sub n hx)
  omega

lemma lift_mem {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 n)
    (hzero : ∀ x ∈ S, P.val x = 0) :
    (P.forced n).prod id * S.prod id ∈ products n := by
  classical
  have hd : Disjoint (P.forced n) S := by
    apply disjoint_left.mpr
    intro x hx hxS
    have hn := (mem_filter.mp hx).2
    rw [hzero x hxS] at hn
    omega
  apply Ang.mem_products_iff.mpr
  refine ⟨P.forced n ∪ S, union_subset (P.forced_sub n) hS, ?_⟩
  exact prod_union hd

lemma forcing_minimal {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 n)
    (hsum : ∑ x ∈ S, P.val x = ∑ x ∈ P.forced n, P.val x) :
    S.filter (fun x => P.val x < 0) = P.forced n ∧
    ∀ x ∈ S.filter (fun x => ¬ P.val x < 0), P.val x = 0 := by
  classical
  let T := P.forced n
  have hsub : S.filter (fun x => P.val x < 0) ⊆ T := by
    intro x hx
    exact mem_filter.mpr ⟨hS (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩
  have hsplit := sum_filter_add_sum_filter_not S (fun x => P.val x < 0) P.val
  have hsd := sum_sdiff hsub (f := P.val)
  have hpos : 0 ≤ ∑ x ∈ S.filter (fun x => ¬ P.val x < 0), P.val x := by
    apply sum_nonneg
    intro x hx
    exact not_lt.mp (mem_filter.mp hx).2
  have hneg : ∀ x ∈ T \ S.filter (fun x => P.val x < 0), P.val x < 0 := by
    intro x hx
    exact (mem_filter.mp (mem_sdiff.mp hx).1).2
  have hdiff0 : T \ S.filter (fun x => P.val x < 0) = ∅ := by
    by_contra hne
    have hlt := sum_lt_sum_of_nonempty (nonempty_iff_ne_empty.mpr hne) hneg
    rw [sum_const_zero] at hlt
    change ∑ x ∈ S, P.val x = ∑ x ∈ T, P.val x at hsum
    linarith
  have hsum0 : ∑ x ∈ S.filter (fun x => ¬ P.val x < 0), P.val x = 0 := by
    rw [hdiff0, sum_empty, zero_add] at hsd
    change ∑ x ∈ S, P.val x = ∑ x ∈ T, P.val x at hsum
    linarith
  have hL0 : ∀ x ∈ S.filter (fun x => ¬ P.val x < 0), P.val x = 0 := by
    refine (sum_eq_zero_iff_of_nonneg (fun x hx => ?_)).mp hsum0
    exact not_lt.mp (mem_filter.mp hx).2
  refine ⟨Subset.antisymm hsub ?_, hL0⟩
  intro x hx
  by_contra hxs
  have hx' : x ∈ T \ S.filter (fun x => P.val x < 0) := mem_sdiff.mpr ⟨hx, hxs⟩
  rw [hdiff0] at hx'
  simp at hx'

lemma lift_not_mem {n R : ℕ} (hR : R ≠ 0) (hval : P.val R = 0)
    (hexcl : ∀ S : Finset ℕ, S ⊆ Icc 1 n →
      (∀ x ∈ S, P.val x = 0) → S.prod id ≠ R) :
    (P.forced n).prod id * R ∉ products n := by
  classical
  rw [Ang.mem_products_iff]
  rintro ⟨S, hS, hprod⟩
  have hS0 : ∀ x ∈ S, x ≠ 0 := by
    intro x hx
    have := mem_Icc.mp (hS hx)
    omega
  have hF0 : ∀ x ∈ P.forced n, x ≠ 0 := by
    intro x hx
    have := mem_Icc.mp (P.forced_sub n hx)
    omega
  have hsum : ∑ x ∈ S, P.val x = ∑ x ∈ P.forced n, P.val x := by
    have he := P.prod_val S id hS0
    rw [hprod, P.mul (P.forced_prod_ne_zero n) hR, hval, add_zero,
      P.prod_val (P.forced n) id hF0] at he
    exact he.symm
  obtain ⟨heq, hzero⟩ := P.forcing_minimal hS hsum
  let S0 := S.filter (fun x => ¬ P.val x < 0)
  have hprod2 := prod_filter_mul_prod_filter_not S (fun x => P.val x < 0) id
  rw [heq] at hprod2
  have hRprod : S0.prod id = R := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (P.forced_prod_ne_zero n))
    rw [← hprod]
    exact hprod2
  exact hexcl S0 (Subset.trans (filter_subset _ _) hS) hzero hRprod

end AdditivePrice
end AngLarge
