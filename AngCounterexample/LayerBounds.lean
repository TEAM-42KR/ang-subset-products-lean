import AngCounterexample.LayerClassify

open Finset
namespace AngLarge
namespace Grid
variable {ℓ : ℕ} (G : Grid ℓ)

lemma rowMon_lower (d : ℕ) (r : Fin 3 → ℕ) (hd : ∀ i, d ≤ G.small i) :
    d ^ (∑ i, r i) ≤ G.rowMon r := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' (fun i _ => pow_le_pow_left' (hd i) (r i))
lemma rowMon_upper (D : ℕ) (r : Fin 3 → ℕ) (hD : ∀ i, G.small i ≤ D) :
    G.rowMon r ≤ D ^ (∑ i, r i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' (fun i _ => pow_le_pow_left' (hD i) (r i))
lemma colProd_lower (a b : ℕ) (c : Fin ℓ → ℕ) (hb : ∀ j, b ≤ G.col a j) :
    b ^ (∑ j, c j) ≤ G.colProd a c := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' (fun j _ => pow_le_pow_left' (hb j) (c j))

lemma sum_le_one_shape {ι : Type*} [Fintype ι] (r : ι → ℕ) (h : (∑ i, r i) ≤ 1) :
    (∀ i, r i = 0) ∨ ∃ i, r i = 1 ∧ ∀ k, k ≠ i → r k = 0 := by
  classical
  by_cases hz : ∀ i, r i = 0
  · exact Or.inl hz
  · right
    push_neg at hz
    obtain ⟨i,hi⟩ := hz
    have hm := Finset.sum_le_one_iff.mp h
    refine ⟨i,(hm i i (mem_univ _) (mem_univ _) hi hi).2,?_⟩
    intro k hki
    by_contra hk
    exact hki (hm k i (mem_univ _) (mem_univ _) hk hi).1

lemma rowMon_sum_le_one (r : Fin 3 → ℕ) (h : (∑ i, r i) ≤ 1) :
    G.rowMon r = 1 ∨ ∃ i, G.rowMon r = G.small i := by
  rcases sum_le_one_shape r h with hz | ⟨i,hi,hr⟩
  · left; simp [rowMon,hz]
  · right; refine ⟨i,?_⟩
    rw [rowMon, Finset.prod_eq_single i]
    · simp [hi]
    · intro k _ hki; simp [hr k hki]
    · simp
lemma colProd_sum_le_one (a : ℕ) (c : Fin ℓ → ℕ) (h : (∑ j, c j) ≤ 1) :
    G.colProd a c = 1 ∨ ∃ j, G.colProd a c = G.col a j := by
  rcases sum_le_one_shape c h with hz | ⟨j,hj,hc⟩
  · left; simp [colProd,hz]
  · right; refine ⟨j,?_⟩
    rw [colProd, Finset.prod_eq_single j]
    · simp [hj]
    · intro k _ hkj; simp [hc k hkj]
    · simp

lemma bounded_exponent {p x n : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hxn : x ≤ n)
    (hnp : n < p^2) : x.factorization p ≤ 1 := by
  by_contra he
  have hd : p^2 ∣ x := (hp.pow_dvd_iff_le_factorization hx).mpr (by omega)
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hx) hd
  omega

/-- Exact classification of a bounded neutral divisor of the residual target. -/
lemma classify_residual {t a n p x : ℕ} (C : Cutoffs G t a n p)
    (hp : p.Prime) (hnp : n < p^2) (hq : ∀ i j, G.q i j ≠ p)
    (j0 : Fin ℓ) (hx : x ≠ 0) (hxn : x ≤ n) (hxd : x ∣ p^2 * G.H a)
    (hf : ∀ i j, G.form a j0 x i j = 0) :
    x = 1 ∨ x = p ∨ (∃ α ∈ layer t, x = G.monomial α) ∨
    x = G.row 3 ∨ (∃ j, x = G.col a j) ∨ ∃ i, x = p * G.small i := by
  have hR : p^2 * G.H a ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a)
  have sx : G.Support p x := G.support_of_dvd hR hxd
    (G.support_mul (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a)
      (G.support_pow (G.support_p p hp) 2) (G.support_H p a))
  have hvle := (Nat.factorization_le_iff_dvd hx hR).mpr hxd
  have hb : ∀ i j, G.v x (ri i) j ≤ a := by
    intro i j
    have := hvle (G.q (ri i) j)
    change G.v x (ri i) j ≤ G.v (p^2 * G.H a) (ri i) j at this
    simpa [G.v_mul (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a),
      G.v_p_pow hp hq, G.v_H_small] using this
  have hl : ∀ j, G.v x 3 j ≤ 1 := by
    intro j
    have := hvle (G.q 3 j)
    change G.v x 3 j ≤ G.v (p^2 * G.H a) 3 j at this
    simpa [G.v_mul (pow_ne_zero _ hp.ne_zero) (G.H_ne_zero a),
      G.v_p_pow hp hq, G.v_H_large] using this
  have he : x.factorization p ≤ 1 := bounded_exponent hp hx hxn hnp
  have hd : 1 ≤ C.d := C.d_pos
  have hbpos : 1 ≤ C.b := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le (n/p)) C.s_lt_b)
  have hppos : 1 ≤ p ^ x.factorization p := Nat.one_le_pow _ _ hp.pos
  rcases G.boxed_pattern j0 hb hl hf with hcol | hrow
  · have hshape := G.col_shape hp hq hx sx hcol
    have hc_le : G.colProd a (fun j => G.v x 3 j) ≤ x := by
      exact (Nat.le_mul_of_pos_left _ (show 0 < p ^ x.factorization p from pow_pos hp.pos _)).trans_eq hshape.symm
    have hcsum : (∑ j, G.v x 3 j) ≤ 1 := by
      by_contra h
      have h2 := pow_le_pow_right' hbpos (show 2 ≤ ∑ j, G.v x 3 j by omega)
      have hlo := G.colProd_lower a C.b (fun j => G.v x 3 j) (fun j => (C.col_bounds j).1)
      have : C.b^2 ≤ x := h2.trans (hlo.trans hc_le)
      have := C.n_lt_bsq
      omega
    rcases G.colProd_sum_le_one a _ hcsum with hc | ⟨j,hc⟩
    · rw [hc, mul_one] at hshape
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with he0 | he1
      · left; simpa [he0] using hshape
      · exact Or.inr (Or.inl (by simpa [he1] using hshape))
    · have he0 : x.factorization p = 0 := by
        by_contra hn
        have he1 : x.factorization p = 1 := by omega
        have hle : G.col a j ≤ n / p := by
          apply (Nat.le_div_iff_mul_le hp.pos).mpr
          have hxle := hxn
          rw [hshape,hc,he1,pow_one] at hxle
          simpa only [mul_comm] using hxle
        have := (C.col_bounds j).1
        have := C.s_lt_b
        omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j,by simpa [hc,he0] using hshape⟩))))
  · let r : Fin 3 → ℕ := fun i => G.v x (ri i) j0
    let k : ℕ := G.v x 3 j0
    have hshape : x = p ^ x.factorization p * (G.row 3 ^ k * G.rowMon r) :=
      G.row_shape hp hq hx sx j0 hrow
    have hlow : C.b ^ k * C.d ^ (∑ i, r i) ≤ x := by
      calc
        C.b ^ k * C.d ^ (∑ i, r i) ≤ G.row 3 ^ k * G.rowMon r :=
          Nat.mul_le_mul (pow_le_pow_left' C.large_bounds.1 _) (G.rowMon_lower C.d r (fun i => (C.small_bounds i).1))
        _ ≤ x := by exact (Nat.le_mul_of_pos_left _ (show 0 < p ^ x.factorization p from pow_pos hp.pos _)).trans_eq hshape.symm
    have hsum : (∑ i, r i) ≤ t := by
      by_contra h
      have hpw := pow_le_pow_right' hd (show t+1 ≤ ∑ i, r i by omega)
      have hdb : C.d ^ (∑ i, r i) ≤ C.b ^ k * C.d ^ (∑ i, r i) :=
        Nat.le_mul_of_pos_left _ (by positivity)
      have := C.n_lt_dpow
      have := hpw.trans (hdb.trans hlow)
      omega
    have hk : k ≤ 1 := hl j0
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with hk0 | hk1
    · rw [hk0,pow_zero,one_mul] at hshape
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with he0 | he1
      · have hm : x = G.rowMon r := by simpa [he0] using hshape
        by_cases hz : (∑ i, r i) = 0
        · left
          have hr : ∀ i, r i = 0 := by
            intro i
            have := Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) (mem_univ i)
            omega
          simpa [rowMon,hr] using hm
        · let α : Exponent t := fun i => ⟨r i, by
            have := Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) (mem_univ i)
            omega⟩
          have hα : α ∈ layer t := by
            change α ∈ univ.filter (fun β => 1 ≤ degree β ∧ degree β ≤ t)
            rw [Finset.mem_filter]
            exact ⟨mem_univ _, by change 1 ≤ ∑ i, r i; omega, by change (∑ i, r i) ≤ t; exact hsum⟩
          exact Or.inr (Or.inr (Or.inl ⟨α, hα, hm⟩))
      · have hm : x = p * G.rowMon r := by simpa [he1] using hshape
        have hmn : G.rowMon r ≤ n / p := by
          apply (Nat.le_div_iff_mul_le hp.pos).mpr
          simpa [hm,mul_comm] using hxn
        have hsum1 : (∑ i, r i) ≤ 1 := by
          by_contra h
          have hpw := pow_le_pow_right' hd (show 2 ≤ ∑ i, r i by omega)
          have hlo := G.rowMon_lower C.d r (fun i => (C.small_bounds i).1)
          have := C.s_lt_dsq
          have := hpw.trans (hlo.trans hmn)
          omega
        rcases G.rowMon_sum_le_one r hsum1 with hz | ⟨i,hi⟩
        · exact Or.inr (Or.inl (by simpa [hz] using hm))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i,by simpa [hi] using hm⟩))))
    · have hsum0 : (∑ i, r i) = 0 := by
        by_contra h
        have hd1 := pow_le_pow_right' hd (show 1 ≤ ∑ i, r i by omega)
        have hlo : C.b * C.d ≤ x := by
          calc
            C.b * C.d ≤ C.b ^ k * C.d ^ (∑ i, r i) := by simpa [hk1] using Nat.mul_le_mul_left C.b hd1
            _ ≤ x := hlow
        have := C.n_lt_bd
        omega
      have hr : ∀ i, r i = 0 := by
        intro i
        have := Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) (mem_univ i)
        omega
      have hm : x = p ^ x.factorization p * G.row 3 := by simpa [hk1,rowMon,hr] using hshape
      have he0 : x.factorization p = 0 := by
        by_contra hn
        have he1 : x.factorization p = 1 := by omega
        have hle : G.row 3 ≤ n / p := by
          apply (Nat.le_div_iff_mul_le hp.pos).mpr
          have hxle := hxn
          rw [hm,he1,pow_one] at hxle
          simpa only [mul_comm] using hxle
        have := C.large_bounds.1
        have := C.s_lt_b
        omega
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [he0] using hm))))

end Grid
end AngLarge
