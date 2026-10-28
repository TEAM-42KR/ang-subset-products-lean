import AngCounterexample.LayerCore

open Finset
namespace AngLarge
namespace Grid
variable {ℓ : ℕ} (G : Grid ℓ)

/-- No prime outside the grid and the tagging prime occurs. -/
def Support (p x : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ p → (∀ i j, r ≠ G.q i j) → x.factorization r = 0

def rowMon (r : Fin 3 → ℕ) : ℕ := ∏ i, G.small i ^ r i

lemma rowMon_ne_zero (r : Fin 3 → ℕ) : G.rowMon r ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (G.small_ne_zero i))
lemma v_rowMon (r : Fin 3 → ℕ) (i : Fin 3) (j : Fin ℓ) :
    G.v (G.rowMon r) (ri i) j = r i := by
  rw [rowMon, G.v_prod _ _ (fun k _ => pow_ne_zero _ (G.small_ne_zero k))]
  simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  change (∑ k, r k * G.v (G.small k) (ri i) j) = _
  simp_rw [G.v_small]
  simp
lemma v_rowMon_large (r : Fin 3 → ℕ) (j : Fin ℓ) : G.v (G.rowMon r) 3 j = 0 := by
  rw [rowMon, G.v_prod _ _ (fun k _ => pow_ne_zero _ (G.small_ne_zero k))]
  simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  change (∑ k, r k * G.v (G.small k) 3 j) = _
  simp [G.v_small_large]

lemma support_mul {p x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (sx : G.Support p x) (sy : G.Support p y) : G.Support p (x*y) := by
  intro r hr hrp hq
  simp [Nat.factorization_mul hx hy, sx r hr hrp hq, sy r hr hrp hq]
lemma support_prod {ι : Type*} (p : ℕ) (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ k ∈ S, f k ≠ 0) (hs : ∀ k ∈ S, G.Support p (f k)) :
    G.Support p (∏ k ∈ S, f k) := by
  intro r hr hrp hq
  rw [Nat.factorization_prod hf, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun k hk => hs k hk r hr hrp hq)
lemma support_pow {p x : ℕ} (sx : G.Support p x) (e : ℕ) : G.Support p (x^e) := by
  intro r hr hrp hq
  simp [Nat.factorization_pow, sx r hr hrp hq]
lemma support_p (p : ℕ) (hp : p.Prime) : G.Support p p := by
  intro r _ hrp _
  simp [hp.factorization, Finsupp.single_apply, Ne.symm hrp]
lemma support_row (p : ℕ) (i : Fin 4) : G.Support p (G.row i) := by
  intro r _ _ hq
  rw [G.row_fact]
  exact Finset.sum_eq_zero (fun j _ => if_neg (hq i j).symm)
lemma support_col (p a : ℕ) (j : Fin ℓ) : G.Support p (G.col a j) := by
  apply G.support_mul (G.prime 3 j).ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (G.prime (ri i) j).ne_zero))
  · intro r _ _ hq
    simp [(G.prime 3 j).factorization, Finsupp.single_apply, (hq 3 j).symm]
  · apply G.support_prod p _ _ (fun i _ => pow_ne_zero _ (G.prime (ri i) j).ne_zero)
    intro i _ r _ _ hq
    simp [Nat.factorization_pow, (G.prime (ri i) j).factorization,
      Finsupp.single_apply, (hq (ri i) j).symm]
lemma support_H (p a : ℕ) : G.Support p (G.H a) :=
  G.support_prod p _ _ (fun j _ => G.col_ne_zero a j) (fun j _ => G.support_col p a j)
lemma support_rowMon (p : ℕ) (r : Fin 3 → ℕ) : G.Support p (G.rowMon r) :=
  G.support_prod p _ _ (fun i _ => pow_ne_zero _ (G.small_ne_zero i))
    (fun i _ => G.support_pow (G.support_row p (ri i)) (r i))
lemma support_of_dvd {p x y : ℕ} (hy : y ≠ 0) (hxy : x ∣ y)
    (sy : G.Support p y) : G.Support p x := by
  intro r hr hrp hq
  have hx : x ≠ 0 := ne_zero_of_dvd_ne_zero hy hxy
  have h := (Nat.factorization_le_iff_dvd hx hy).mpr hxy r
  rw [sy r hr hrp hq] at h
  omega

lemma eq_of_vals {p x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (sx : G.Support p x) (sy : G.Support p y)
    (hp : x.factorization p = y.factorization p)
    (hv : ∀ i j, G.v x i j = G.v y i j) : x = y := by
  apply Nat.eq_of_factorization_eq hx hy
  intro r
  by_cases hr : r.Prime
  · by_cases hrp : r = p
    · subst r; exact hp
    · by_cases hq : ∃ i j, r = G.q i j
      · obtain ⟨i,j,rfl⟩ := hq; exact hv i j
      · simp only [not_exists] at hq
        rw [sx r hr hrp hq, sy r hr hrp hq]
  · simp [(Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hr)]

lemma row_fact_p {p : ℕ} (hq : ∀ i j, G.q i j ≠ p) (i : Fin 4) :
    (G.row i).factorization p = 0 := by
  rw [G.row_fact]
  exact Finset.sum_eq_zero (fun j _ => if_neg (hq i j))
lemma col_fact_p {p : ℕ} (hq : ∀ i j, G.q i j ≠ p) (a : ℕ) (j : Fin ℓ) :
    (G.col a j).factorization p = 0 := by
  unfold col
  rw [Nat.factorization_mul (G.prime 3 j).ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (G.prime (ri i) j).ne_zero)),
    Finsupp.add_apply, Nat.factorization_prod
      (fun i _ => pow_ne_zero _ (G.prime (ri i) j).ne_zero), Finsupp.finsetSum_apply]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    (G.prime _ _).factorization, Finsupp.single_apply, if_neg (hq _ _), mul_zero,
    Finset.sum_const_zero, add_zero]
lemma H_fact_p {p : ℕ} (hq : ∀ i j, G.q i j ≠ p) (a : ℕ) : (G.H a).factorization p = 0 := by
  rw [H, Nat.factorization_prod (fun j _ => G.col_ne_zero a j), Finsupp.finsetSum_apply]
  simp [G.col_fact_p hq]
lemma rowMon_fact_p {p : ℕ} (hq : ∀ i j, G.q i j ≠ p) (r : Fin 3 → ℕ) :
    (G.rowMon r).factorization p = 0 := by
  rw [rowMon, Nat.factorization_prod (fun i _ => pow_ne_zero _ (G.small_ne_zero i)),
    Finsupp.finsetSum_apply]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  change (∑ i, r i * (G.row (ri i)).factorization p) = _
  simp [G.row_fact_p hq]
lemma v_p_pow {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (e : ℕ) (i : Fin 4) (j : Fin ℓ) : G.v (p^e) i j = 0 := by
  simp [v, Nat.factorization_pow, hp.factorization, Finsupp.single_apply,
    (hq i j).symm]
lemma fact_p_pow {p : ℕ} (hp : p.Prime) (e : ℕ) : (p^e).factorization p = e := by
  simp [Nat.factorization_pow, hp.factorization]
lemma form_p_pow {p : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (a e : ℕ) (j0 : Fin ℓ) (i : Fin 3) (j : Fin ℓ) :
    G.form a j0 (p^e) i j = 0 := by
  change (G.v (p^e) (ri i) j : ℤ) - G.v (p^e) (ri i) j0 -
    (a : ℤ) * ((G.v (p^e) 3 j : ℤ) - G.v (p^e) 3 j0) = 0
  simp [G.v_p_pow hp hq]

lemma row_indices (i : Fin 4) : (∃ k : Fin 3, i = ri k) ∨ i = 3 := by
  by_cases h : i.val < 3
  · exact Or.inl ⟨⟨i.val,h⟩, rfl⟩
  · right; apply Fin.ext; have := i.isLt; simp; omega

/-- A box-constrained kernel vector is either column-type or row-constant. -/
lemma boxed_pattern {a x : ℕ} (j0 : Fin ℓ)
    (hb : ∀ i j, G.v x (ri i) j ≤ a) (hl : ∀ j, G.v x 3 j ≤ 1)
    (hf : ∀ i j, G.form a j0 x i j = 0) :
    (∀ i j, G.v x (ri i) j = a * G.v x 3 j) ∨
    (∀ i j k, G.v x i j = G.v x i k) := by
  have he : ∀ i j k, G.v x (ri i) j + a * G.v x 3 k =
      G.v x (ri i) k + a * G.v x 3 j := by
    intro i j k
    have hj := hf i j
    have hk := hf i k
    change (G.v x (ri i) j : ℤ) - G.v x (ri i) j0 -
      (a : ℤ) * ((G.v x 3 j : ℤ) - G.v x 3 j0) = 0 at hj
    change (G.v x (ri i) k : ℤ) - G.v x (ri i) j0 -
      (a : ℤ) * ((G.v x 3 k : ℤ) - G.v x 3 j0) = 0 at hk
    zify
    nlinarith
  by_cases hc : ∀ j, G.v x 3 j = G.v x 3 j0
  · right
    intro i j k
    rcases row_indices i with ⟨r,rfl⟩ | rfl
    · have := he r j k
      rw [hc j, hc k] at this
      omega
    · rw [hc j, hc k]
  · push_neg at hc
    obtain ⟨j1,hj1⟩ := hc
    have hz : ∃ k, G.v x 3 k = 0 := by
      by_cases h : G.v x 3 j0 = 0
      · exact ⟨j0,h⟩
      · have h0 := hl j0; have h1 := hl j1
        exact ⟨j1, by omega⟩
    have ho : ∃ k, G.v x 3 k = 1 := by
      by_cases h : G.v x 3 j0 = 1
      · exact ⟨j0,h⟩
      · have h0 := hl j0; have h1 := hl j1
        exact ⟨j1, by omega⟩
    obtain ⟨k0,h0⟩ := hz
    obtain ⟨k1,h1⟩ := ho
    have hs : ∀ i, G.v x (ri i) k0 = 0 := by
      intro i
      have he1 := he i k1 k0
      have hb1 := hb i k1
      rw [h0,h1] at he1
      nlinarith
    left
    intro i j
    have he1 := he i j k0
    rw [h0,hs i] at he1
    simpa using he1

lemma dvd_of_vals {p x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (sx : G.Support p x) (hp : x.factorization p ≤ y.factorization p)
    (hv : ∀ i j, G.v x i j ≤ G.v y i j) : x ∣ y := by
  rw [← Nat.factorization_le_iff_dvd hx hy, Finsupp.le_def]
  intro r
  by_cases hr : r.Prime
  · by_cases hrp : r = p
    · subst r; exact hp
    · by_cases hq : ∃ i j, r = G.q i j
      · obtain ⟨i,j,rfl⟩ := hq; exact hv i j
      · simp only [not_exists] at hq
        rw [sx r hr hrp hq]; exact Nat.zero_le _
  · simp [(Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hr)]

def colProd (a : ℕ) (c : Fin ℓ → ℕ) : ℕ := ∏ j, G.col a j ^ c j
lemma colProd_ne_zero (a : ℕ) (c : Fin ℓ → ℕ) : G.colProd a c ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (G.col_ne_zero a j))
lemma support_colProd (p a : ℕ) (c : Fin ℓ → ℕ) : G.Support p (G.colProd a c) :=
  G.support_prod p _ _ (fun j _ => pow_ne_zero _ (G.col_ne_zero a j))
    (fun j _ => G.support_pow (G.support_col p a j) (c j))
lemma colProd_fact_p {p : ℕ} (hq : ∀ i j, G.q i j ≠ p) (a : ℕ) (c : Fin ℓ → ℕ) :
    (G.colProd a c).factorization p = 0 := by
  rw [colProd, Nat.factorization_prod (fun j _ => pow_ne_zero _ (G.col_ne_zero a j)),
    Finsupp.finsetSum_apply]
  simp [Nat.factorization_pow, G.col_fact_p hq]
lemma v_colProd_small (a : ℕ) (c : Fin ℓ → ℕ) (i : Fin 3) (j : Fin ℓ) :
    G.v (G.colProd a c) (ri i) j = a * c j := by
  rw [colProd, G.v_prod _ _ (fun j _ => pow_ne_zero _ (G.col_ne_zero a j))]
  simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  change (∑ l, c l * G.v (G.col a l) (ri i) j) = _
  simp_rw [G.v_col_small]
  simp [mul_comm]
lemma v_colProd_large (a : ℕ) (c : Fin ℓ → ℕ) (j : Fin ℓ) :
    G.v (G.colProd a c) 3 j = c j := by
  rw [colProd, G.v_prod _ _ (fun j _ => pow_ne_zero _ (G.col_ne_zero a j))]
  simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  change (∑ l, c l * G.v (G.col a l) 3 j) = _
  simp_rw [G.v_col_large]
  simp

lemma row_shape {p x : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (hx : x ≠ 0) (sx : G.Support p x) (j0 : Fin ℓ)
    (hv : ∀ i j k, G.v x i j = G.v x i k) :
    x = p ^ x.factorization p * (G.row 3 ^ G.v x 3 j0 *
      G.rowMon (fun i => G.v x (ri i) j0)) := by
  have hy : G.row 3 ^ G.v x 3 j0 * G.rowMon (fun i => G.v x (ri i) j0) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (G.row_ne_zero 3)) (G.rowMon_ne_zero _)
  apply G.eq_of_vals hx (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hy) sx
    (G.support_mul (pow_ne_zero _ hp.ne_zero) hy (G.support_pow (G.support_p p hp) _)
      (G.support_mul (pow_ne_zero _ (G.row_ne_zero 3)) (G.rowMon_ne_zero _)
        (G.support_pow (G.support_row p 3) _) (G.support_rowMon p _)))
  · simp [Nat.factorization_mul, hp.ne_zero, G.row_ne_zero, G.rowMon_ne_zero,
      Nat.factorization_pow, G.row_fact_p hq, G.rowMon_fact_p hq, fact_p_pow hp, hp.factorization]
  · intro i j
    rw [G.v_mul (pow_ne_zero _ hp.ne_zero) hy, G.v_p_pow hp hq,
      G.v_mul (pow_ne_zero _ (G.row_ne_zero 3)) (G.rowMon_ne_zero _)]
    simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, zero_add]
    change G.v x i j = G.v x 3 j0 * G.v (G.row 3) i j +
      G.v (G.rowMon (fun i => G.v x (ri i) j0)) i j
    rcases row_indices i with ⟨k,rfl⟩ | rfl
    · rw [G.v_rowMon, G.v_row, if_neg]
      · simpa using hv (ri k) j j0
      · intro h; have := congrArg (fun z : Fin 4 => z.val) h; have := k.isLt; simp [ri] at *; omega
    · simp [G.v_row, G.v_rowMon_large, hv 3 j j0]

lemma col_shape {p a x : ℕ} (hp : p.Prime) (hq : ∀ i j, G.q i j ≠ p)
    (hx : x ≠ 0) (sx : G.Support p x)
    (hv : ∀ i j, G.v x (ri i) j = a * G.v x 3 j) :
    x = p ^ x.factorization p * G.colProd a (fun j => G.v x 3 j) := by
  apply G.eq_of_vals hx (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (G.colProd_ne_zero a _)) sx
    (G.support_mul (pow_ne_zero _ hp.ne_zero) (G.colProd_ne_zero a _)
      (G.support_pow (G.support_p p hp) _) (G.support_colProd p a _))
  · simp [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (G.colProd_ne_zero a _),
      fact_p_pow hp, hp.factorization, G.colProd_fact_p hq]
  · intro i j
    rw [G.v_mul (pow_ne_zero _ hp.ne_zero) (G.colProd_ne_zero a _), G.v_p_pow hp hq, zero_add]
    rcases row_indices i with ⟨k,rfl⟩ | rfl
    · rw [G.v_colProd_small, hv]
    · rw [G.v_colProd_large]

end Grid
end AngLarge
