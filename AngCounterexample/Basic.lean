import Mathlib

/-!
# A counterexample to Ang's conjecture (OEIS A060957)

Let `products n` be the set of products of subsets of `{1, …, n}`. Yan Sheng Ang conjectured
(OEIS A060957, 2020) that for every prime `p ≤ n`, if `m` and `p ^ a * m` lie in `products n`,
then so does `p ^ k * m` for every `0 < k < a`. This file proves the negation of that statement,
in the form of `oeis_60957_conjecture_0` from the OEIS-Open benchmark (theorem `Ang.disproof`).

## The counterexample

`n0 = 1399108927917911481`, `p0 = 1118479`, `a = 2`, `k = 1`, and
`m = mkM Tneg = p0 ^ 3 * ∏ j, A j * ∏ t ∈ Tneg, t`. Here `q` is a `6 × 6` array of the 36 smallest
primes, `kk = (2, 2, 2, 2, 2, 1)`, `D i = ∏ j, q i j`, `A j = ∏ i, q i j ^ kk i`, and `Tneg` is the
set of all `1 ≤ t ≤ n0` with `L t < 0` for the functional `L` below. Then `m` and `p0 ^ 2 * m` are
subset products of `{1, …, n0}` (`mkM_mem`, `p0sq_mkM_mem`), but `p0 * m` is not
(`p0_mkM_not_mem`).

## Outline (Section 5 of the accompanying paper)

* `v t i j` is the exponent of `q i j` in `t`. The 25 linear forms
  `ℓ_{ab} = x_{ab} - x_{a5} - k_a x_{5b} + k_a x_{55}` (`a, b < 5`) are packed into the single
  functional `L = ∑_r 10 ^ r * ℓ_r`, which is additive on products (`L_mul`, `L_prod`).
* Forcing: if `s ⊆ {1, …, n0}` multiplies to `p0 * m`, comparing `∑ x ∈ s, L x` with
  `∑ x ∈ Tneg, L x` shows that `Tneg ⊆ s` and that `L = 0` on the remaining factors, whose product
  is `R = p0 ^ 4 * ∏ j, A j` (steps (1)–(3) of `p0_mkM_not_mem`).
* Every remaining factor divides `R`, so its exponents lie in a box on which `|ℓ_r| ≤ 4`. Hence all
  25 forms vanish (`digits_eq_zero`, `ell_zero`), and the exponent matrix is a row or a weighted
  column (`pattern`). Since `n0 < A j * A j'`, `n0 < D i * D i'`, `n0 < p0 * A j`,
  `n0 < p0 ^ 2 * D i` and `n0 < p0 ^ 3`, the factor is one of the 21 integers in `Ulist`
  (`classify`).
* Counting the exponents of the primes `q a 0` and of `p0` over the remaining factors leaves two
  cases: the six `A j` are used, or the stacked pairs `D i, p0 * D i` are. Neither gives the
  `p0`-exponent `4` of `R` (the final `omega`).

Every numerical fact is checked by the kernel (`decide`, `rfl`, `norm_num`); `native_decide` is
not used.
-/

open Finset

/-- A060957: Number of different products (including the empty product) of any subset of
$\{1, 2, 3, \dots, n\}$. -/
def A060957 (n : ℕ) : ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id) |>.card

-- Convenience definition for the set of products
def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)

namespace Ang

/-- The prime of the counterexample. -/
def p0 : ℕ := 1118479
/-- The bound `n` of the counterexample. -/
def n0 : ℕ := 1399108927917911481
/-- Row weights `k_i`. -/
def kk : Fin 6 → ℕ := ![2, 2, 2, 2, 2, 1]
/-- The `6 × 6` array of the 36 smallest primes. -/
def q : Fin 6 → Fin 6 → ℕ :=
  ![![151, 3, 113, 83, 139, 13], ![19, 47, 71, 23, 101, 53], ![149, 131, 5, 59, 79, 17],
    ![37, 73, 103, 127, 2, 109], ![11, 137, 29, 31, 67, 89], ![43, 41, 97, 7, 61, 107]]
/-- Row atoms `D_i = ∏_j q_{ij}`. -/
def D (i : Fin 6) : ℕ := ∏ j, q i j
/-- Column atoms `A_j = ∏_i q_{ij}^{k_i}`. -/
def A (j : Fin 6) : ℕ := ∏ i, q i j ^ kk i

lemma p0_prime : p0.Prime := by norm_num [p0]

lemma q_prime (i j : Fin 6) : (q i j).Prime := by
  fin_cases i <;> fin_cases j <;> norm_num [q]

lemma q_inj : ∀ i j i' j', q i j = q i' j' → i = i' ∧ j = j' := by decide

lemma q_ne_p0 : ∀ i j, q i j ≠ p0 := by decide

lemma D_vals : D 0 = 7677377409 ∧ D 1 = 7806113957 ∧ D 2 = 7733135015 ∧ D 3 = 7702328258 ∧
    D 4 = 8078630659 ∧ D 5 = 7813321579 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

lemma A_vals : A 0 = 1301640063365904427 ∧ A 1 = 1399108927917911481 ∧
    A 2 = 1392694217997047425 ∧ A 3 = 1376400271662451063 ∧
    A 4 = 1347305126864296276 ∧ A 5 = 1381506947926437683 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

lemma D_ne_zero (i : Fin 6) : D i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => (q_prime i j).ne_zero)

lemma A_ne_zero (j : Fin 6) : A j ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (q_prime i j).ne_zero)

/-- Exponent of the grid prime `q i j` in `t`. -/
def v (t : ℕ) (i j : Fin 6) : ℕ := t.factorization (q i j)

lemma v_mul {s t : ℕ} (hs : s ≠ 0) (ht : t ≠ 0) (i j : Fin 6) :
    v (s * t) i j = v s i j + v t i j := by
  simp [v, Nat.factorization_mul hs ht]

lemma v_one (i j : Fin 6) : v 1 i j = 0 := by simp [v]

lemma v_p0_pow (e : ℕ) (i j : Fin 6) : v (p0 ^ e) i j = 0 := by
  simp only [v, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [p0_prime.factorization, Finsupp.single_apply, if_neg (q_ne_p0 i j).symm, mul_zero]

lemma v_D (i a b : Fin 6) : v (D i) a b = if a = i then 1 else 0 := by
  unfold v D
  rw [Nat.factorization_prod (fun j _ => (q_prime i j).ne_zero)]
  rw [Finsupp.finsetSum_apply]
  simp_rw [(q_prime _ _).factorization, Finsupp.single_apply]
  by_cases h : a = i
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single b]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro hq; exact hj (q_inj _ _ _ _ hq).2
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro hq; exact h (q_inj _ _ _ _ hq).1.symm

lemma v_A (j a b : Fin 6) : v (A j) a b = if b = j then kk a else 0 := by
  unfold v A
  rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (q_prime i j).ne_zero)]
  rw [Finsupp.finsetSum_apply]
  simp_rw [Nat.factorization_pow, (q_prime _ _).factorization, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  by_cases h : b = j
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · simp
    · intro i _ hi
      rw [if_neg, mul_zero]
      intro hq; exact hi (q_inj _ _ _ _ hq).1
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg, mul_zero]
    intro hq; exact h (q_inj _ _ _ _ hq).2.symm

/-! ### The forcing functional -/

/-- Row index of the `r`-th linear form (`r < 25`). -/
def rowOf (r : Fin 25) : Fin 6 := ⟨r.val / 5, by omega⟩
/-- Column index of the `r`-th linear form (`r < 25`). -/
def colOf (r : Fin 25) : Fin 6 := ⟨r.val % 5, by omega⟩

/-- The linear forms `ℓ_{ab}(x) = x_{ab} - x_{a5} - k_a x_{5b} + k_a x_{55}`. -/
def ell (a b : Fin 6) (t : ℕ) : ℤ :=
  (v t a b : ℤ) - v t a 5 - (kk a : ℤ) * v t 5 b + (kk a : ℤ) * v t 5 5

/-- The single forcing functional: the 25 forms packed as base-10 digits. -/
def L (t : ℕ) : ℤ := ∑ r : Fin 25, (10 : ℤ) ^ (r : ℕ) * ell (rowOf r) (colOf r) t

lemma ell_mul {s t : ℕ} (hs : s ≠ 0) (ht : t ≠ 0) (a b : Fin 6) :
    ell a b (s * t) = ell a b s + ell a b t := by
  simp only [ell, v_mul hs ht]; push_cast; ring

lemma L_mul {s t : ℕ} (hs : s ≠ 0) (ht : t ≠ 0) : L (s * t) = L s + L t := by
  simp only [L, ell_mul hs ht, mul_add, Finset.sum_add_distrib]

lemma L_one : L 1 = 0 := by simp [L, ell, v_one]

lemma L_p0_pow (e : ℕ) : L (p0 ^ e) = 0 := by simp [L, ell, v_p0_pow]

lemma kk5 : kk 5 = 1 := rfl

lemma L_D (i : Fin 6) : L (D i) = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  simp only [ell, v_D]
  split_ifs <;> simp_all

lemma L_A (j : Fin 6) : L (A j) = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  simp only [ell, v_A, kk5]
  split_ifs <;> simp_all

lemma L_prod {ι : Type*} (S : Finset ι) (g : ι → ℕ) (hg : ∀ x ∈ S, g x ≠ 0) :
    L (∏ x ∈ S, g x) = ∑ x ∈ S, L (g x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [L_one]
  | insert x S hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      L_mul (hg x (Finset.mem_insert_self x S))
        (Finset.prod_ne_zero_iff.mpr (fun y hy => hg y (Finset.mem_insert_of_mem hy))),
      ih (fun y hy => hg y (Finset.mem_insert_of_mem hy))]

/-- Base-10 digits in `[-4, 4]` summing to zero all vanish. -/
lemma digits_eq_zero : ∀ (N : ℕ) (d : Fin N → ℤ), (∀ r, |d r| ≤ 4) →
    ∑ r : Fin N, (10 : ℤ) ^ (r : ℕ) * d r = 0 → ∀ r, d r = 0 := by
  intro N
  induction N with
  | zero => intro d _ _ r; exact r.elim0
  | succ N ih =>
    intro d hd hsum
    rw [Fin.sum_univ_succ] at hsum
    have hrest : ∑ r : Fin N, (10 : ℤ) ^ ((Fin.succ r : Fin (N + 1)) : ℕ) * d (Fin.succ r)
        = 10 * ∑ r : Fin N, (10 : ℤ) ^ (r : ℕ) * d (Fin.succ r) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      simp [Fin.val_succ, pow_succ]; ring
    rw [hrest] at hsum
    simp only [Fin.val_zero, pow_zero, one_mul] at hsum
    have h0 := hd 0
    have hd0 : d 0 = 0 := by
      rw [abs_le] at h0; omega
    have hS : ∑ r : Fin N, (10 : ℤ) ^ (r : ℕ) * d (Fin.succ r) = 0 := by
      rw [hd0] at hsum; omega
    have := ih (fun r => d (Fin.succ r)) (fun r => hd _) hS
    intro r
    refine Fin.cases hd0 (fun r => this r) r

/-! ### Factorization bookkeeping -/

/-- `t` has no prime factor outside the grid and `p0`. -/
def Supp (t : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ p0 → (∀ a b, r ≠ q a b) → t.factorization r = 0

lemma D_fact (i : Fin 6) (r : ℕ) : (D i).factorization r = ∑ j, if q i j = r then 1 else 0 := by
  unfold D
  rw [Nat.factorization_prod (fun j _ => (q_prime i j).ne_zero), Finsupp.finsetSum_apply]
  simp_rw [(q_prime _ _).factorization, Finsupp.single_apply]

lemma A_fact (j : Fin 6) (r : ℕ) :
    (A j).factorization r = ∑ i, if q i j = r then kk i else 0 := by
  unfold A
  rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (q_prime i j).ne_zero),
    Finsupp.finsetSum_apply]
  simp_rw [Nat.factorization_pow, (q_prime _ _).factorization, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

lemma D_fact_p0 (i : Fin 6) : (D i).factorization p0 = 0 := by
  rw [D_fact]; exact Finset.sum_eq_zero (fun j _ => if_neg (q_ne_p0 i j))

lemma A_fact_p0 (j : Fin 6) : (A j).factorization p0 = 0 := by
  rw [A_fact]; exact Finset.sum_eq_zero (fun i _ => if_neg (q_ne_p0 i j))

lemma Supp_D (i : Fin 6) : Supp (D i) := by
  intro r _ _ hq
  rw [D_fact]; exact Finset.sum_eq_zero (fun j _ => if_neg (hq i j).symm)

lemma Supp_A (j : Fin 6) : Supp (A j) := by
  intro r _ _ hq
  rw [A_fact]; exact Finset.sum_eq_zero (fun i _ => if_neg (hq i j).symm)

lemma p0pow_fact (e r : ℕ) : (p0 ^ e).factorization r = if r = p0 then e else 0 := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, p0_prime.factorization, Finsupp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all

lemma Supp_p0pow (e : ℕ) : Supp (p0 ^ e) := by
  intro r _ hrp _
  rw [p0pow_fact, if_neg hrp]

lemma Supp_mul {s t : ℕ} (hs : s ≠ 0) (ht : t ≠ 0) (ss : Supp s) (st : Supp t) :
    Supp (s * t) := by
  intro r hr hrp hq
  rw [Nat.factorization_mul hs ht, Finsupp.add_apply, ss r hr hrp hq, st r hr hrp hq]

lemma Supp_of_dvd {s t : ℕ} (ht : t ≠ 0) (hst : s ∣ t) (st : Supp t) : Supp s := by
  intro r hr hrp hq
  have hs : s ≠ 0 := by rintro rfl; exact ht (Nat.eq_zero_of_zero_dvd hst)
  have := (Nat.factorization_le_iff_dvd hs ht).mpr hst r
  rw [st r hr hrp hq] at this; omega

lemma eq_of_v {t y : ℕ} (ht : t ≠ 0) (hy : y ≠ 0) (st : Supp t) (sy : Supp y)
    (hp : t.factorization p0 = y.factorization p0) (hv : ∀ a b, v t a b = v y a b) : t = y := by
  apply Nat.eq_of_factorization_eq ht hy
  intro r
  by_cases hr : r.Prime
  · by_cases hrp : r = p0
    · subst hrp; exact hp
    · by_cases hq : ∃ a b, r = q a b
      · obtain ⟨a, b, rfl⟩ := hq; exact hv a b
      · simp only [not_exists] at hq
        rw [st r hr hrp hq, sy r hr hrp hq]
  · simp [(Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hr)]

lemma dvd_of_v {y t : ℕ} (hy : y ≠ 0) (ht : t ≠ 0) (sy : Supp y)
    (hp : y.factorization p0 ≤ t.factorization p0) (hv : ∀ a b, v y a b ≤ v t a b) : y ∣ t := by
  rw [← Nat.factorization_le_iff_dvd hy ht, Finsupp.le_def]
  intro r
  by_cases hr : r.Prime
  · by_cases hrp : r = p0
    · subst hrp; exact hp
    · by_cases hq : ∃ a b, r = q a b
      · obtain ⟨a, b, rfl⟩ := hq; exact hv a b
      · simp only [not_exists] at hq
        rw [sy r hr hrp hq]; exact Nat.zero_le _
  · simp [(Nat.factorization_eq_zero_iff _ _).mpr (Or.inl hr)]

lemma v_prod {ι : Type*} (S : Finset ι) (g : ι → ℕ) (hg : ∀ x ∈ S, g x ≠ 0) (a b : Fin 6) :
    v (∏ x ∈ S, g x) a b = ∑ x ∈ S, v (g x) a b := by
  unfold v
  rw [Nat.factorization_prod hg, Finsupp.finsetSum_apply]

lemma fact_prod {ι : Type*} (S : Finset ι) (g : ι → ℕ) (hg : ∀ x ∈ S, g x ≠ 0) (r : ℕ) :
    (∏ x ∈ S, g x).factorization r = ∑ x ∈ S, (g x).factorization r := by
  rw [Nat.factorization_prod hg, Finsupp.finsetSum_apply]

/-- The residual target `R = p0^4 · ∏ A_j`. -/
def R : ℕ := p0 ^ 4 * ∏ j, A j

lemma prodA_ne_zero : (∏ j, A j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => A_ne_zero j)

lemma R_ne_zero : R ≠ 0 := mul_ne_zero (pow_ne_zero _ p0_prime.ne_zero) prodA_ne_zero

lemma v_prodA (a b : Fin 6) : v (∏ j, A j) a b = kk a := by
  rw [v_prod _ _ (fun j _ => A_ne_zero j)]
  simp only [v_A]
  simp

lemma v_R (a b : Fin 6) : v R a b = kk a := by
  unfold R
  rw [v_mul (pow_ne_zero _ p0_prime.ne_zero) prodA_ne_zero, v_p0_pow, v_prodA, zero_add]

lemma fact_prodA_p0 : (∏ j, A j).factorization p0 = 0 := by
  rw [fact_prod _ _ (fun j _ => A_ne_zero j)]
  exact Finset.sum_eq_zero (fun j _ => A_fact_p0 j)

lemma p0pow_fact_self (e : ℕ) : (p0 ^ e).factorization p0 = e :=
  (p0pow_fact e p0).trans (if_pos rfl)

lemma fact_p0pow_mul (e x : ℕ) (hx : x ≠ 0) :
    (p0 ^ e * x).factorization p0 = e + x.factorization p0 := by
  rw [Nat.factorization_mul (pow_ne_zero e p0_prime.ne_zero) hx, Finsupp.add_apply,
    p0pow_fact_self]

lemma R_fact_p0 : R.factorization p0 = 4 := by
  have h := fact_p0pow_mul 4 (∏ j, A j) prodA_ne_zero
  rw [fact_prodA_p0, add_zero] at h
  exact h

lemma Supp_prodA : Supp (∏ j, A j) := by
  intro r hr hrp hq
  rw [fact_prod _ _ (fun j _ => A_ne_zero j)]
  exact Finset.sum_eq_zero (fun j _ => Supp_A j r hr hrp hq)

lemma Supp_R : Supp R :=
  Supp_mul (pow_ne_zero _ p0_prime.ne_zero) prodA_ne_zero (Supp_p0pow 4) Supp_prodA

lemma kk_le_two (a : Fin 6) : kk a ≤ 2 := by fin_cases a <;> decide

lemma kk_cases (a : Fin 6) : kk a = 1 ∨ kk a = 2 := by fin_cases a <;> decide

lemma fin6_cases (a : Fin 6) : a.val < 5 ∨ a = 5 := by
  rcases a with ⟨a, ha⟩
  by_cases h : a < 5
  · left; exact h
  · right; ext; simp; omega

/-- From `L t = 0` and the box bounds, all 25 forms vanish. -/
lemma ell_zero {t : ℕ} (hb : ∀ a b, v t a b ≤ kk a) (hL : L t = 0) :
    ∀ a b : Fin 6, a.val < 5 → b.val < 5 → ell a b t = 0 := by
  have hd := digits_eq_zero 25 (fun r => ell (rowOf r) (colOf r) t) (by
    intro r
    have h1 := hb (rowOf r) (colOf r)
    have h2 := hb (rowOf r) 5
    have h3 := hb 5 (colOf r)
    have h4 := hb 5 5
    have hk5 : kk 5 = 1 := rfl
    rw [hk5] at h3 h4
    simp only [ell]
    rcases kk_cases (rowOf r) with hk | hk <;> rw [hk] at h1 h2 ⊢ <;> rw [abs_le] <;>
      push_cast <;> constructor <;> omega) hL
  intro a b ha hb'
  have := hd ⟨5 * a.val + b.val, by omega⟩
  have hr : rowOf ⟨5 * a.val + b.val, by omega⟩ = a := by
    ext; simp [rowOf]; omega
  have hc : colOf ⟨5 * a.val + b.val, by omega⟩ = b := by
    ext; simp [colOf]; omega
  simpa [hr, hc] using this


/-! ### Numerical facts -/

lemma A_ge (j : Fin 6) : 1301640063365904427 ≤ A j := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := A_vals
  fin_cases j
  · rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl, h0]
  · rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl, h1]; norm_num
  · rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl, h2]; norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl, h3]; norm_num
  · rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl, h4]; norm_num
  · rw [show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl, h5]; norm_num

lemma A_le (j : Fin 6) : A j ≤ n0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := A_vals
  fin_cases j
  · rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl, h0]; norm_num [n0]
  · rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl, h1]; norm_num [n0]
  · rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl, h2]; norm_num [n0]
  · rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl, h3]; norm_num [n0]
  · rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl, h4]; norm_num [n0]
  · rw [show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl, h5]; norm_num [n0]

lemma D_ge (i : Fin 6) : 7677377409 ≤ D i := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := D_vals
  fin_cases i
  · rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl, h0]
  · rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl, h1]; norm_num
  · rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl, h2]; norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl, h3]; norm_num
  · rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl, h4]; norm_num
  · rw [show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl, h5]; norm_num

lemma D_le (i : Fin 6) : D i ≤ 8078630659 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := D_vals
  fin_cases i
  · rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl, h0]; norm_num
  · rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl, h1]; norm_num
  · rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl, h2]; norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl, h3]; norm_num
  · rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl, h4]
  · rw [show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl, h5]; norm_num

lemma p0_le_n0 : p0 ≤ n0 := by norm_num [p0, n0]
lemma p0sq_le_n0 : p0 ^ 2 ≤ n0 := by norm_num [p0, n0]
lemma n0_lt_p0cube : n0 < p0 ^ 3 := by norm_num [p0, n0]

lemma pD_le_n0 (i : Fin 6) : p0 * D i ≤ n0 :=
  calc p0 * D i ≤ p0 * 8078630659 := Nat.mul_le_mul_left _ (D_le i)
    _ ≤ n0 := by norm_num [p0, n0]

lemma n0_lt_pA (j : Fin 6) : n0 < p0 * A j :=
  calc n0 < p0 * 1301640063365904427 := by norm_num [p0, n0]
    _ ≤ p0 * A j := Nat.mul_le_mul_left _ (A_ge j)

lemma n0_lt_ppD (i : Fin 6) : n0 < p0 ^ 2 * D i :=
  calc n0 < p0 ^ 2 * 7677377409 := by norm_num [p0, n0]
    _ ≤ p0 ^ 2 * D i := Nat.mul_le_mul_left _ (D_ge i)

lemma n0_lt_AA (j j' : Fin 6) : n0 < A j * A j' :=
  calc n0 < 1301640063365904427 * 1301640063365904427 := by norm_num [n0]
    _ ≤ A j * A j' := Nat.mul_le_mul (A_ge j) (A_ge j')

lemma n0_lt_DD (i i' : Fin 6) : n0 < D i * D i' :=
  calc n0 < 7677377409 * 7677377409 := by norm_num [n0]
    _ ≤ D i * D i' := Nat.mul_le_mul (D_ge i) (D_ge i')

/-! ### The residual factors -/

/-- The 21 admissible residual factors. -/
def Ulist : List ℕ :=
  [1, p0, p0 ^ 2, A 0, A 1, A 2, A 3, A 4, A 5, D 0, D 1, D 2, D 3, D 4, D 5,
    p0 * D 0, p0 * D 1, p0 * D 2, p0 * D 3, p0 * D 4, p0 * D 5]

lemma A_mem (j : Fin 6) : A j ∈ Ulist := by
  fin_cases j <;> simp [Ulist]

lemma D_mem (i : Fin 6) : D i ∈ Ulist := by
  fin_cases i <;> simp [Ulist]

lemma pD_mem (i : Fin 6) : p0 * D i ∈ Ulist := by
  fin_cases i <;> simp [Ulist]

/-- Shape of an exponent matrix in the kernel of the 25 forms and inside the box. -/
lemma pattern (x : Fin 6 → Fin 6 → ℕ) (hb : ∀ a b, x a b ≤ kk a)
    (he : ∀ a b : Fin 6, a.val < 5 → b.val < 5 → x a b + kk a * x 5 5 = x a 5 + kk a * x 5 b) :
    (∃ c : Fin 6 → ℕ, (∀ j, c j ≤ 1) ∧ ∀ a b, x a b = kk a * c b) ∨
    (∃ e : Fin 6 → ℕ, (∀ i, e i ≤ kk i) ∧ ∀ a b, x a b = e a) := by
  have hk5 : kk 5 = 1 := rfl
  have h55 : x 5 5 ≤ 1 := hb 5 5
  have h5 : ∀ b, x 5 b ≤ 1 := fun b => hb 5 b
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h55 with h0 | h1
  · by_cases hB : ∃ b0 : Fin 6, b0.val < 5 ∧ x 5 b0 = 1
    · obtain ⟨b0, hb0, hx⟩ := hB
      have hcol : ∀ a : Fin 6, a.val < 5 → x a 5 = 0 := by
        intro a ha
        have h1 := he a b0 ha hb0
        rw [h0, hx, mul_zero, mul_one, add_zero] at h1
        have h2 := hb a b0
        omega
      left
      refine ⟨fun b => if b.val < 5 then x 5 b else 0, ?_, ?_⟩
      · intro j
        dsimp only
        split_ifs
        · exact h5 j
        · exact Nat.zero_le 1
      · intro a b
        rcases fin6_cases a with ha | rfl <;> rcases fin6_cases b with hb' | rfl
        · have h1 := he a b ha hb'
          rw [h0, mul_zero, add_zero, hcol a ha, zero_add] at h1
          simp [hb', h1]
        · simp [hcol a ha]
        · simp [hb', hk5]
        · simp [h0]
    · simp only [not_exists, not_and] at hB
      have hz : ∀ b : Fin 6, b.val < 5 → x 5 b = 0 := by
        intro b hb'
        have h1 := h5 b
        have h2 := hB b hb'
        omega
      right
      refine ⟨fun a => if a.val < 5 then x a 5 else 0, ?_, ?_⟩
      · intro i
        dsimp only
        split_ifs
        · exact hb i 5
        · exact Nat.zero_le _
      · intro a b
        rcases fin6_cases a with ha | rfl <;> rcases fin6_cases b with hb' | rfl
        · have h1 := he a b ha hb'
          rw [h0, mul_zero, add_zero, hz b hb', mul_zero, add_zero] at h1
          simp [ha, h1]
        · simp [ha]
        · simp [hz b hb']
        · simp [h0]
  · by_cases hB : ∃ b0 : Fin 6, b0.val < 5 ∧ x 5 b0 = 0
    · obtain ⟨b0, hb0, hx⟩ := hB
      have hcol : ∀ a : Fin 6, a.val < 5 → x a 5 = kk a := by
        intro a ha
        have h2 := he a b0 ha hb0
        rw [h1, hx, mul_zero, mul_one, add_zero] at h2
        have h3 := hb a 5
        omega
      left
      refine ⟨fun b => if b.val < 5 then x 5 b else 1, ?_, ?_⟩
      · intro j
        dsimp only
        split_ifs
        · exact h5 j
        · exact le_refl 1
      · intro a b
        rcases fin6_cases a with ha | rfl <;> rcases fin6_cases b with hb' | rfl
        · have h2 := he a b ha hb'
          rw [h1, mul_one, hcol a ha] at h2
          simp only [hb', if_true]
          omega
        · simp [hcol a ha]
        · simp [hb', hk5]
        · simp [h1, hk5]
    · simp only [not_exists, not_and] at hB
      have ho : ∀ b : Fin 6, b.val < 5 → x 5 b = 1 := by
        intro b hb'
        have h2 := h5 b
        have h3 := hB b hb'
        omega
      right
      refine ⟨fun a => if a.val < 5 then x a 5 else 1, ?_, ?_⟩
      · intro i
        dsimp only
        split_ifs with hi
        · exact hb i 5
        · rcases fin6_cases i with h | rfl
          · exact absurd h hi
          · simp [hk5]
      · intro a b
        rcases fin6_cases a with ha | rfl <;> rcases fin6_cases b with hb' | rfl
        · have h2 := he a b ha hb'
          rw [h1, mul_one, ho b hb'] at h2
          simp only [ha, if_true]
          omega
        · simp [ha]
        · simp [ho b hb']
        · simp [h1]

lemma eq_p0pow_mul {t y : ℕ} (ht0 : t ≠ 0) (st : Supp t) (hy0 : y ≠ 0) (sy : Supp y)
    (hyp : y.factorization p0 = 0) (hv : ∀ a b, v t a b = v y a b) :
    t = p0 ^ t.factorization p0 * y := by
  have hp0 : p0 ^ t.factorization p0 ≠ 0 := pow_ne_zero _ p0_prime.ne_zero
  apply eq_of_v ht0 (mul_ne_zero hp0 hy0) st (Supp_mul hp0 hy0 (Supp_p0pow _) sy)
  · rw [fact_p0pow_mul _ _ hy0, hyp, add_zero]
  · intro a b
    rw [v_mul hp0 hy0, v_p0_pow, zero_add, hv]

lemma false_of_big_dvd {t y : ℕ} (ht0 : t ≠ 0) (htn : t ≤ n0) (hy0 : y ≠ 0) (sy : Supp y)
    (hyp : y.factorization p0 = 0) (hv : ∀ a b, v y a b ≤ v t a b) (hbig : n0 < y) : False := by
  have hd := dvd_of_v hy0 ht0 sy (by rw [hyp]; exact Nat.zero_le _) hv
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hd
  omega

lemma fact_mul_p0 {s t : ℕ} (hs : s ≠ 0) (ht : t ≠ 0) (hs0 : s.factorization p0 = 0)
    (ht0 : t.factorization p0 = 0) : (s * t).factorization p0 = 0 := by
  rw [Nat.factorization_mul hs ht, Finsupp.add_apply, hs0, ht0]

/-- Every residual factor is one of the 21 admissible ones. -/
lemma classify {t : ℕ} (ht0 : t ≠ 0) (htn : t ≤ n0) (hdvd : t ∣ R) (hL : L t = 0) :
    t ∈ Ulist := by
  have st : Supp t := Supp_of_dvd R_ne_zero hdvd Supp_R
  have hb : ∀ a b, v t a b ≤ kk a := by
    intro a b
    have := (Nat.factorization_le_iff_dvd ht0 R_ne_zero).mpr hdvd (q a b)
    rw [← v_R a b]
    exact this
  have hell := ell_zero hb hL
  have he : ∀ a b : Fin 6, a.val < 5 → b.val < 5 →
      v t a b + kk a * v t 5 5 = v t a 5 + kk a * v t 5 b := by
    intro a b ha hb'
    have h := hell a b ha hb'
    simp only [ell] at h
    have h' : ((v t a b + kk a * v t 5 5 : ℕ) : ℤ) = ((v t a 5 + kk a * v t 5 b : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast h'
  -- finishing lemmas for the three admissible shapes
  have finA : ∀ j, (∀ a b, v t a b = v (A j) a b) → t ∈ Ulist := by
    intro j hv
    have heq := eq_p0pow_mul ht0 st (A_ne_zero j) (Supp_A j) (A_fact_p0 j) hv
    have hf0 : t.factorization p0 = 0 := by
      by_contra hne
      have h1 : p0 ≤ p0 ^ t.factorization p0 :=
        (pow_one p0).symm.le.trans (Nat.pow_le_pow_right p0_prime.pos (by omega))
      have h2 : p0 * A j ≤ t := by rw [heq]; exact Nat.mul_le_mul_right _ h1
      have := n0_lt_pA j
      omega
    rw [hf0, pow_zero, one_mul] at heq
    rw [heq]; exact A_mem j
  have finD : ∀ i, (∀ a b, v t a b = v (D i) a b) → t ∈ Ulist := by
    intro i hv
    have heq := eq_p0pow_mul ht0 st (D_ne_zero i) (Supp_D i) (D_fact_p0 i) hv
    have hf1 : t.factorization p0 ≤ 1 := by
      by_contra hne
      have h1 : p0 ^ 2 ≤ p0 ^ t.factorization p0 := Nat.pow_le_pow_right p0_prime.pos (by omega)
      have h2 : p0 ^ 2 * D i ≤ t := by rw [heq]; exact Nat.mul_le_mul_right _ h1
      have := n0_lt_ppD i
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hf1 with h | h
    · rw [h, pow_zero, one_mul] at heq; rw [heq]; exact D_mem i
    · rw [h, pow_one] at heq; rw [heq]; exact pD_mem i
  have fin1 : (∀ a b, v t a b = 0) → t ∈ Ulist := by
    intro hv
    have heq := eq_p0pow_mul ht0 st one_ne_zero (by intro r _ _ _; simp) (by simp)
      (fun a b => by rw [hv, v_one])
    rw [mul_one] at heq
    obtain ⟨g, hg⟩ : ∃ g, g = t.factorization p0 := ⟨_, rfl⟩
    rw [← hg] at heq
    have hf2 : g ≤ 2 := by
      by_contra hne
      have h1 : p0 ^ 3 ≤ p0 ^ g := Nat.pow_le_pow_right p0_prime.pos (by omega)
      have := n0_lt_p0cube
      omega
    interval_cases g <;> rw [heq] <;> simp [Ulist]
  rcases pattern (v t) hb he with ⟨c, hc1, hcx⟩ | ⟨e, he1, hex⟩
  · -- column type
    by_cases two : ∃ j j', j ≠ j' ∧ c j = 1 ∧ c j' = 1
    · obtain ⟨j, j', hne, hj, hj'⟩ := two
      exfalso
      apply false_of_big_dvd ht0 htn (mul_ne_zero (A_ne_zero j) (A_ne_zero j'))
        (Supp_mul (A_ne_zero j) (A_ne_zero j') (Supp_A j) (Supp_A j'))
        (fact_mul_p0 (A_ne_zero j) (A_ne_zero j') (A_fact_p0 j) (A_fact_p0 j'))
        _ (n0_lt_AA j j')
      intro a b
      rw [v_mul (A_ne_zero j) (A_ne_zero j'), v_A, v_A, hcx a b]
      by_cases hb1 : b = j
      · subst hb1
        rw [if_pos rfl, if_neg hne, hj]; simp
      · by_cases hb2 : b = j'
        · subst hb2
          rw [if_neg hb1, if_pos rfl, hj']; simp
        · rw [if_neg hb1, if_neg hb2]; simp
    · by_cases one : ∃ j, c j = 1
      · obtain ⟨j, hj⟩ := one
        have hz : ∀ j', j' ≠ j → c j' = 0 := by
          intro j' hne
          have h1 := hc1 j'
          by_contra hc
          exact two ⟨j', j, hne, by omega, hj⟩
        apply finA j
        intro a b
        rw [hcx a b, v_A]
        by_cases hb1 : b = j
        · subst hb1; rw [if_pos rfl, hj, mul_one]
        · rw [if_neg hb1, hz b hb1, mul_zero]
      · simp only [not_exists] at one
        apply fin1
        intro a b
        rw [hcx a b]
        have h1 := hc1 b
        have h2 := one b
        have : c b = 0 := by omega
        rw [this, mul_zero]
  · -- row type
    by_cases two : (∃ i, 2 ≤ e i) ∨ (∃ i i', i ≠ i' ∧ 1 ≤ e i ∧ 1 ≤ e i')
    · exfalso
      rcases two with ⟨i, hi⟩ | ⟨i, i', hne, hi, hi'⟩
      · apply false_of_big_dvd ht0 htn (mul_ne_zero (D_ne_zero i) (D_ne_zero i))
          (Supp_mul (D_ne_zero i) (D_ne_zero i) (Supp_D i) (Supp_D i))
          (fact_mul_p0 (D_ne_zero i) (D_ne_zero i) (D_fact_p0 i) (D_fact_p0 i))
          _ (n0_lt_DD i i)
        intro a b
        rw [v_mul (D_ne_zero i) (D_ne_zero i), v_D, hex a b]
        by_cases ha : a = i
        · subst ha; rw [if_pos rfl]; omega
        · rw [if_neg ha]; omega
      · apply false_of_big_dvd ht0 htn (mul_ne_zero (D_ne_zero i) (D_ne_zero i'))
          (Supp_mul (D_ne_zero i) (D_ne_zero i') (Supp_D i) (Supp_D i'))
          (fact_mul_p0 (D_ne_zero i) (D_ne_zero i') (D_fact_p0 i) (D_fact_p0 i'))
          _ (n0_lt_DD i i')
        intro a b
        rw [v_mul (D_ne_zero i) (D_ne_zero i'), v_D, v_D, hex a b]
        by_cases ha : a = i
        · subst ha; rw [if_pos rfl, if_neg hne]; omega
        · by_cases ha' : a = i'
          · subst ha'; rw [if_neg ha, if_pos rfl]; omega
          · rw [if_neg ha, if_neg ha']; omega
    · simp only [not_or, not_exists, not_and] at two
      obtain ⟨h2, h11⟩ := two
      by_cases one : ∃ i, e i = 1
      · obtain ⟨i, hi⟩ := one
        have hz : ∀ i', i' ≠ i → e i' = 0 := by
          intro i' hne
          have := h11 i' i hne
          have := h2 i'
          omega
        apply finD i
        intro a b
        rw [hex a b, v_D]
        by_cases ha : a = i
        · subst ha; rw [if_pos rfl, hi]
        · rw [if_neg ha, hz a ha]
      · simp only [not_exists] at one
        apply fin1
        intro a b
        rw [hex a b]
        have h3 := h2 a
        have h4 := one a
        omega

/-! ### The forced set and the integer `m`

The integer `m` of the counterexample is `mkM Tneg = p0^3 · ∏ A_j · ∏ Tneg`. The three facts about
it are proved for an arbitrary finset `T` with the defining property of `Tneg` (`IsForced T`) and
only then specialized to `Tneg`. This is not just a matter of style: `Tneg` is a closed term, and if
the kernel is asked to compare two closed natural-number expressions that contain `∏ Tneg` and are
not syntactically equal, its accelerated `Nat` arithmetic tries to evaluate `∏ Tneg`, a product
over all `t ≤ n0`. Working with a variable `T` keeps every such comparison symbolic. -/

/-- The forced factors: all `1 ≤ t ≤ n0` on which the functional `L` is negative. -/
def Tneg : Finset ℕ := (Icc 1 n0).filter (fun t => L t < 0)

/-- `mkM T = p0^3 · ∏ A_j · ∏_{t ∈ T} t`; the integer `m` of the counterexample is `mkM Tneg`. -/
def mkM (T : Finset ℕ) : ℕ := p0 ^ 3 * (∏ j, A j) * T.prod id

/-- `T` consists exactly of the integers `1 ≤ t ≤ n0` with `L t < 0`. -/
def IsForced (T : Finset ℕ) : Prop := ∀ x, x ∈ T ↔ x ∈ Icc 1 n0 ∧ L x < 0

lemma isForced_Tneg : IsForced Tneg := fun _ => Finset.mem_filter

lemma mem_products_iff {n m : ℕ} : m ∈ products n ↔ ∃ s ⊆ Icc 1 n, s.prod id = m := by
  simp only [products, Finset.mem_image, Finset.mem_powerset]

lemma IsForced.sub {T : Finset ℕ} (hT : IsForced T) : T ⊆ Icc 1 n0 :=
  fun x hx => ((hT x).mp hx).1

lemma IsForced.ne_zero {T : Finset ℕ} (hT : IsForced T) : ∀ x ∈ T, x ≠ 0 := by
  intro x hx
  have := hT.sub hx
  rw [Finset.mem_Icc] at this
  omega

lemma IsForced.disj {T S : Finset ℕ} (hT : IsForced T) (hS : ∀ x ∈ S, L x = 0) :
    Disjoint T S := by
  rw [Finset.disjoint_left]
  intro x hx hxS
  have := ((hT x).mp hx).2
  rw [hS x hxS] at this
  exact lt_irrefl _ this

lemma L_p0 : L p0 = 0 := by simpa using L_p0_pow 1

lemma L_pD (i : Fin 6) : L (p0 * D i) = 0 := by
  rw [L_mul p0_prime.ne_zero (D_ne_zero i), L_p0, L_D, add_zero]

lemma kk0 : kk 0 = 2 := rfl
lemma kk1 : kk 1 = 2 := rfl
lemma kk2 : kk 2 = 2 := rfl
lemma kk3 : kk 3 = 2 := rfl
lemma kk4 : kk 4 = 2 := rfl

lemma prod_D_pow : ∏ i, D i ^ kk i = ∏ j, A j := by
  simp only [D, A, ← Finset.prod_pow]
  exact Finset.prod_comm

lemma A_eq0 : A 0 = 1301640063365904427 := A_vals.1
lemma A_eq1 : A 1 = 1399108927917911481 := A_vals.2.1
lemma A_eq2 : A 2 = 1392694217997047425 := A_vals.2.2.1
lemma A_eq3 : A 3 = 1376400271662451063 := A_vals.2.2.2.1
lemma A_eq4 : A 4 = 1347305126864296276 := A_vals.2.2.2.2.1
lemma A_eq5 : A 5 = 1381506947926437683 := A_vals.2.2.2.2.2
lemma D_eq0 : D 0 = 7677377409 := D_vals.1
lemma D_eq1 : D 1 = 7806113957 := D_vals.2.1
lemma D_eq2 : D 2 = 7733135015 := D_vals.2.2.1
lemma D_eq3 : D 3 = 7702328258 := D_vals.2.2.2.1
lemma D_eq4 : D 4 = 8078630659 := D_vals.2.2.2.2.1
lemma D_eq5 : D 5 = 7813321579 := D_vals.2.2.2.2.2

/-! ### The two witnesses -/

/-- Low witness: the six column atoms and `p0, p0^2`. -/
def S1 : List ℕ := [A 0, A 1, A 2, A 3, A 4, A 5, p0, p0 ^ 2]

/-- High witness: `D_i, p0 D_i` for `i ≤ 4`, and `D_5`. -/
def S2 : List ℕ :=
  [D 0, p0 * D 0, D 1, p0 * D 1, D 2, p0 * D 2, D 3, p0 * D 3, D 4, p0 * D 4, D 5]

lemma S1_nodup : S1.Nodup := by
  simp only [S1, A_eq0, A_eq1, A_eq2, A_eq3, A_eq4, A_eq5, p0]
  decide

lemma S2_nodup : S2.Nodup := by
  simp only [S2, D_eq0, D_eq1, D_eq2, D_eq3, D_eq4, D_eq5, p0]
  decide

lemma Ulist_nodup : Ulist.Nodup := by
  simp only [Ulist, A_eq0, A_eq1, A_eq2, A_eq3, A_eq4, A_eq5, D_eq0, D_eq1, D_eq2, D_eq3,
    D_eq4, D_eq5, p0]
  decide

lemma S1_prod : S1.toFinset.prod id = p0 ^ 3 * ∏ j, A j := by
  rw [List.prod_toFinset _ S1_nodup]
  simp only [S1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, id,
    Fin.prod_univ_six]
  ring

lemma S2_prod : S2.toFinset.prod id = p0 ^ 5 * ∏ j, A j := by
  rw [List.prod_toFinset _ S2_nodup, ← prod_D_pow]
  simp only [S2, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, id,
    Fin.prod_univ_six]
  simp only [kk0, kk1, kk2, kk3, kk4, kk5]
  ring

lemma S1_L : ∀ x ∈ S1.toFinset, L x = 0 := by
  intro x hx
  simp only [S1, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst h
  · exact L_A 0
  · exact L_A 1
  · exact L_A 2
  · exact L_A 3
  · exact L_A 4
  · exact L_A 5
  · exact L_p0
  · exact L_p0_pow 2

lemma S2_L : ∀ x ∈ S2.toFinset, L x = 0 := by
  intro x hx
  simp only [S2, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact L_D 0
  · exact L_pD 0
  · exact L_D 1
  · exact L_pD 1
  · exact L_D 2
  · exact L_pD 2
  · exact L_D 3
  · exact L_pD 3
  · exact L_D 4
  · exact L_pD 4
  · exact L_D 5

lemma S1_sub : S1.toFinset ⊆ Icc 1 n0 := by
  intro x hx
  simp only [S1, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
  rw [Finset.mem_Icc]
  have hA : ∀ j, 1 ≤ A j ∧ A j ≤ n0 :=
    fun j => ⟨Nat.one_le_iff_ne_zero.mpr (A_ne_zero j), A_le j⟩
  rcases hx with h | h | h | h | h | h | h | h <;> subst h
  · exact hA 0
  · exact hA 1
  · exact hA 2
  · exact hA 3
  · exact hA 4
  · exact hA 5
  · exact ⟨p0_prime.one_lt.le, p0_le_n0⟩
  · exact ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ p0_prime.ne_zero), p0sq_le_n0⟩

lemma D_le_n0 (i : Fin 6) : D i ≤ n0 :=
  le_trans (Nat.le_mul_of_pos_left _ p0_prime.pos) (pD_le_n0 i)

lemma S2_sub : S2.toFinset ⊆ Icc 1 n0 := by
  intro x hx
  simp only [S2, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
  rw [Finset.mem_Icc]
  have hD : ∀ i, 1 ≤ D i ∧ D i ≤ n0 :=
    fun i => ⟨Nat.one_le_iff_ne_zero.mpr (D_ne_zero i), D_le_n0 i⟩
  have hpD : ∀ i, 1 ≤ p0 * D i ∧ p0 * D i ≤ n0 := fun i =>
    ⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero p0_prime.ne_zero (D_ne_zero i)), pD_le_n0 i⟩
  rcases hx with h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact hD 0
  · exact hpD 0
  · exact hD 1
  · exact hpD 1
  · exact hD 2
  · exact hpD 2
  · exact hD 3
  · exact hpD 3
  · exact hD 4
  · exact hpD 4
  · exact hD 5

/-- `m = mkM T` is a subset product: `T ∪ S1` multiplies to it. -/
theorem mkM_mem {T : Finset ℕ} (hT : IsForced T) : mkM T ∈ products n0 := by
  rw [mem_products_iff]
  refine ⟨T ∪ S1.toFinset, Finset.union_subset hT.sub S1_sub, ?_⟩
  rw [Finset.prod_union (hT.disj S1_L), S1_prod, mkM]
  ring

/-- `p0^2 m` is a subset product: `T ∪ S2` multiplies to it. -/
theorem p0sq_mkM_mem {T : Finset ℕ} (hT : IsForced T) : p0 ^ 2 * mkM T ∈ products n0 := by
  rw [mem_products_iff]
  refine ⟨T ∪ S2.toFinset, Finset.union_subset hT.sub S2_sub, ?_⟩
  rw [Finset.prod_union (hT.disj S2_L), S2_prod, mkM]
  ring

/-! ### `p0 · m` is not a subset product -/

/-- Indicator of membership, as a natural number. -/
def ind (s : Finset ℕ) (u : ℕ) : ℕ := if u ∈ s then 1 else 0

lemma ind_le (s : Finset ℕ) (u : ℕ) : ind s u ≤ 1 := by
  unfold ind; split_ifs <;> omega

lemma sum_over_U {s0 : Finset ℕ} (hU : ∀ x ∈ s0, x ∈ Ulist) (g : ℕ → ℕ) :
    ∑ x ∈ s0, g x = (Ulist.map (fun u => ind s0 u * g u)).sum := by
  rw [← List.sum_toFinset _ Ulist_nodup]
  have h1 : (∑ x ∈ Ulist.toFinset, ind s0 x * g x)
      = ∑ x ∈ Ulist.toFinset.filter (· ∈ s0), g x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold ind
    split_ifs <;> simp
  have hset : s0 = Ulist.toFinset.filter (· ∈ s0) := by
    ext x
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun hx => ⟨hU x hx, hx⟩, fun h => h.2⟩
  rw [h1]
  exact Finset.sum_congr hset (fun _ _ => rfl)

lemma L_prodId (S : Finset ℕ) (hS : ∀ x ∈ S, x ≠ 0) : L (S.prod id) = ∑ x ∈ S, L x :=
  L_prod S id hS

lemma L_R : L R = 0 := by
  rw [R, L_mul (pow_ne_zero _ p0_prime.ne_zero) prodA_ne_zero, L_p0_pow,
    L_prod Finset.univ A (fun j _ => A_ne_zero j)]
  simp only [L_A, Finset.sum_const_zero, zero_add]

lemma p0_mkM (T : Finset ℕ) : p0 * mkM T = T.prod id * R := by
  rw [mkM, R]
  ring

lemma fact_p0_q (a b : Fin 6) : p0.factorization (q a b) = 0 := by
  have := v_p0_pow 1 a b
  simpa [v] using this

lemma fact_p0pow_q (e : ℕ) (a b : Fin 6) : (p0 ^ e).factorization (q a b) = 0 :=
  v_p0_pow e a b

lemma fA (j a b : Fin 6) : (A j).factorization (q a b) = if b = j then kk a else 0 := v_A j a b

lemma fD (i a b : Fin 6) : (D i).factorization (q a b) = if a = i then 1 else 0 := v_D i a b

lemma fpD (i a b : Fin 6) : (p0 * D i).factorization (q a b) = if a = i then 1 else 0 := by
  have := v_mul p0_prime.ne_zero (D_ne_zero i) a b
  rw [v_D] at this
  simp only [v] at this
  rw [this, fact_p0_q, zero_add]

lemma fact_p0_self : p0.factorization p0 = 1 := p0_prime.factorization_self

lemma fact_pD_p0 (i : Fin 6) : (p0 * D i).factorization p0 = 1 := by
  rw [Nat.factorization_mul p0_prime.ne_zero (D_ne_zero i), Finsupp.add_apply, fact_p0_self,
    D_fact_p0]

theorem p0_mkM_not_mem {T : Finset ℕ} (hT : IsForced T) : p0 * mkM T ∉ products n0 := by
  rw [mem_products_iff]
  rintro ⟨s, hs, hprod⟩
  rw [p0_mkM] at hprod
  have hs0 : ∀ x ∈ s, x ≠ 0 := by
    intro x hx
    have := hs hx
    rw [Finset.mem_Icc] at this
    omega
  have hT0 := hT.ne_zero
  have hTp : T.prod id ≠ 0 := Finset.prod_ne_zero_iff.mpr hT0
  -- (1) the sum of `L` over `s` equals its sum over `T`
  have hLs : ∑ x ∈ s, L x = ∑ x ∈ T, L x := by
    have h1 := L_prodId s hs0
    rw [hprod, L_mul hTp R_ne_zero, L_R, add_zero, L_prodId T hT0] at h1
    exact h1.symm
  -- (2) minimality forces `T ⊆ s` and `L = 0` on the rest
  have hsub : s.filter (fun x => L x < 0) ⊆ T := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact (hT x).mpr ⟨hs hx.1, hx.2⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun x => L x < 0) L
  have hsd := Finset.sum_sdiff hsub (f := L)
  have hpos : 0 ≤ ∑ x ∈ s.filter (fun x => ¬ L x < 0), L x := by
    apply Finset.sum_nonneg
    intro x hx
    rw [Finset.mem_filter] at hx
    exact not_lt.mp hx.2
  have hneg : ∀ x ∈ T \ s.filter (fun x => L x < 0), L x < 0 :=
    fun x hx => ((hT x).mp (Finset.mem_sdiff.mp hx).1).2
  have hdiff0 : T \ s.filter (fun x => L x < 0) = ∅ := by
    by_contra hne
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hne) hneg
    rw [Finset.sum_const_zero] at hlt
    linarith
  have hsum0 : ∑ x ∈ s.filter (fun x => ¬ L x < 0), L x = 0 := by
    rw [hdiff0, Finset.sum_empty, zero_add] at hsd
    linarith
  have hL0 : ∀ x ∈ s.filter (fun x => ¬ L x < 0), L x = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg (fun x hx => ?_)).mp hsum0
    rw [Finset.mem_filter] at hx
    exact not_lt.mp hx.2
  have hTsN : T ⊆ s.filter (fun x => L x < 0) := by
    intro x hx
    by_contra hxs
    have h' : x ∈ T \ s.filter (fun x => L x < 0) := Finset.mem_sdiff.mpr ⟨hx, hxs⟩
    rw [hdiff0] at h'
    simp at h'
  have hsNeq : s.filter (fun x => L x < 0) = T := Finset.Subset.antisymm hsub hTsN
  -- (3) the residual factors multiply to `R`
  have hprod2 := Finset.prod_filter_mul_prod_filter_not s (fun x => L x < 0) id
  rw [hsNeq] at hprod2
  have hR : (s.filter (fun x => ¬ L x < 0)).prod id = R := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hTp)
    rw [← hprod]
    exact hprod2
  -- (4) every residual factor is admissible
  have hs0sub : s.filter (fun x => ¬ L x < 0) ⊆ s := Finset.filter_subset _ _
  have hU : ∀ x ∈ s.filter (fun x => ¬ L x < 0), x ∈ Ulist := by
    intro x hx
    have hxI := hs (hs0sub hx)
    rw [Finset.mem_Icc] at hxI
    refine classify (by omega) hxI.2 ?_ (hL0 x hx)
    rw [← hR]
    exact Finset.dvd_prod_of_mem id hx
  -- (5) count prime exponents
  have hs00 : ∀ x ∈ s.filter (fun x => ¬ L x < 0), x ≠ 0 := fun x hx => hs0 x (hs0sub hx)
  have hval : ∀ r, ∑ x ∈ s.filter (fun x => ¬ L x < 0), x.factorization r
      = R.factorization r := by
    intro r
    rw [← hR]
    exact (fact_prod _ id hs00 r).symm
  have eq_q : ∀ a : Fin 6,
      (Ulist.map (fun u => ind (s.filter (fun x => ¬ L x < 0)) u * u.factorization (q a 0))).sum
        = kk a := by
    intro a
    rw [← sum_over_U hU (fun u => u.factorization (q a 0)), hval]
    exact v_R a 0
  have eq_p :
      (Ulist.map (fun u => ind (s.filter (fun x => ¬ L x < 0)) u * u.factorization p0)).sum
        = 4 := by
    rw [← sum_over_U hU (fun u => u.factorization p0), hval, R_fact_p0]
  have e0 := eq_q 0
  have e1 := eq_q 1
  have e2 := eq_q 2
  have e3 := eq_q 3
  have e4 := eq_q 4
  have e5 := eq_q 5
  simp only [Ulist, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, fact_p0_q, fact_p0pow_q, fA, fD, fpD,
    kk0, kk1, kk2, kk3, kk4, kk5, Fin.isValue, Fin.reduceEq, if_true, if_false, mul_zero, mul_one,
    add_zero, zero_add] at e0 e1 e2 e3 e4 e5
  simp only [Ulist, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, fact_p0_self, p0pow_fact_self,
    A_fact_p0, D_fact_p0, fact_pD_p0, mul_zero, mul_one, add_zero, zero_add] at eq_p
  have b1 := ind_le (s.filter (fun x => ¬ L x < 0)) p0
  have b2 := ind_le (s.filter (fun x => ¬ L x < 0)) (p0 ^ 2)
  have bA0 := ind_le (s.filter (fun x => ¬ L x < 0)) (A 0)
  have bD0 := ind_le (s.filter (fun x => ¬ L x < 0)) (D 0)
  have bD1 := ind_le (s.filter (fun x => ¬ L x < 0)) (D 1)
  have bD2 := ind_le (s.filter (fun x => ¬ L x < 0)) (D 2)
  have bD3 := ind_le (s.filter (fun x => ¬ L x < 0)) (D 3)
  have bD4 := ind_le (s.filter (fun x => ¬ L x < 0)) (D 4)
  have bD5 := ind_le (s.filter (fun x => ¬ L x < 0)) (D 5)
  have bP0 := ind_le (s.filter (fun x => ¬ L x < 0)) (p0 * D 0)
  have bP1 := ind_le (s.filter (fun x => ¬ L x < 0)) (p0 * D 1)
  have bP2 := ind_le (s.filter (fun x => ¬ L x < 0)) (p0 * D 2)
  have bP3 := ind_le (s.filter (fun x => ¬ L x < 0)) (p0 * D 3)
  have bP4 := ind_le (s.filter (fun x => ¬ L x < 0)) (p0 * D 4)
  have bP5 := ind_le (s.filter (fun x => ¬ L x < 0)) (p0 * D 5)
  -- either the six `A_j` are used (then `p0, p0^2` must supply `p0^4`), or none is (then the
  -- `D_i` are stacked and supply at least `p0^5`)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bA0 with hA | hA <;> omega

/-- The same, with the exponent written as `p0 ^ 1`, as it arises from the conjecture. -/
theorem p0pow1_mkM_not_mem {T : Finset ℕ} (hT : IsForced T) : p0 ^ 1 * mkM T ∉ products n0 := by
  rw [pow_one]
  exact p0_mkM_not_mem hT

/-- The explicit counterexample: with `m = mkM Tneg`, both `m` and `p0^2 m` are subset products of
`{1, …, n0}`, but `p0 m` is not. -/
theorem counterexample :
    mkM Tneg ∈ products n0 ∧ p0 ^ 2 * mkM Tneg ∈ products n0 ∧ p0 * mkM Tneg ∉ products n0 :=
  ⟨mkM_mem isForced_Tneg, p0sq_mkM_mem isForced_Tneg, p0_mkM_not_mem isForced_Tneg⟩

end Ang

/-- **Ang's conjecture (OEIS A060957) is false.** The statement negated here is
`oeis_60957_conjecture_0` of the OEIS-Open benchmark. -/
theorem Ang.disproof :
    ¬ ∀ (n : ℕ), ∀ p, Nat.Prime p → p ≤ n →
      ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
      ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n := by
  intro h
  exact Ang.p0pow1_mkM_not_mem Ang.isForced_Tneg
    (h Ang.n0 Ang.p0 Ang.p0_prime Ang.p0_le_n0 (Ang.mkM Ang.Tneg) 2
      (Ang.mkM_mem Ang.isForced_Tneg) (Ang.p0sq_mkM_mem Ang.isForced_Tneg) 1
      (by norm_num) (by norm_num))
