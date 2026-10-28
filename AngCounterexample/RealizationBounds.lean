import AngCounterexample.RealizationPrimes

/-! Bounds for the products in a Bertrand grid. -/

open Finset

namespace AngLarge.Realization

lemma small_bounds {ℓ R : ℕ} (G : Grid ℓ) (hℓ : 0 < ℓ) (hR : 0 < R)
    (hs : ∀ i : Fin 3, ∀ j, R ^ 2 < G.q ⟨i.val, by omega⟩ j ∧
      G.q ⟨i.val, by omega⟩ j ≤ 2 ^ (3 * ℓ) * R ^ 2) :
    ∀ i, R ^ (2 * ℓ) + 1 ≤ G.small i ∧
      G.small i ≤ (2 ^ (3 * ℓ)) ^ ℓ * R ^ (2 * ℓ) := by
  haveI : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  intro i
  have hl : R ^ (2 * ℓ) < G.small i := by
    have hh := Finset.prod_lt_prod_of_nonempty (s := (univ : Finset (Fin ℓ)))
      (f := fun _ => R ^ 2) (g := fun j => G.q ⟨i.val, by omega⟩ j)
      (fun _ _ => pow_pos hR 2) (fun j _ => (hs i j).1) univ_nonempty
    simpa only [Grid.small, Grid.row, prod_const, card_univ, Fintype.card_fin, ← pow_mul] using hh
  have hu : G.small i ≤ (2 ^ (3 * ℓ) * R ^ 2) ^ ℓ := by
    have hh := Finset.prod_le_prod (s := (univ : Finset (Fin ℓ)))
      (f := fun j => G.q ⟨i.val, by omega⟩ j)
      (g := fun _ => 2 ^ (3 * ℓ) * R ^ 2)
      (fun _ _ => Nat.zero_le _) (fun j _ => (hs i j).2)
    simpa only [Grid.small, Grid.row, prod_const, card_univ, Fintype.card_fin] using hh
  exact ⟨by omega, by simpa only [mul_pow, ← pow_mul] using hu⟩

lemma large_bounds {ℓ R a h : ℕ} (G : Grid ℓ) (hR : 1 ≤ R)
    (hs : ∀ i : Fin 3, ∀ j, R ^ 2 < G.q ⟨i.val, by omega⟩ j ∧
      G.q ⟨i.val, by omega⟩ j ≤ 2 ^ (3 * ℓ) * R ^ 2)
    (hl : ∀ j, R ^ h < G.q 3 j ∧ G.q 3 j ≤ 2 ^ ℓ * R ^ h) :
    let w := min (h * ℓ) (6 * a + h)
    let z := max (h * ℓ) (6 * a + h)
    let C := max ((2 ^ ℓ) ^ ℓ) (2 ^ ℓ * (2 ^ (3 * ℓ)) ^ (3 * a))
    (R ^ w ≤ G.row 3 ∧ G.row 3 ≤ C * R ^ z) ∧
    ∀ j, R ^ w ≤ G.col a j ∧ G.col a j ≤ C * R ^ z := by
  dsimp only
  let Cs := 2 ^ (3 * ℓ)
  let Cl := 2 ^ ℓ
  have hrlo : R ^ (h * ℓ) ≤ G.row 3 := by
    have hh := Finset.prod_le_prod (s := (univ : Finset (Fin ℓ)))
      (f := fun _ => R ^ h) (g := fun j => G.q 3 j)
      (fun _ _ => Nat.zero_le _) (fun j _ => (hl j).1.le)
    simpa only [Grid.row, prod_const, card_univ, Fintype.card_fin, ← pow_mul] using hh
  have hrhi : G.row 3 ≤ Cl ^ ℓ * R ^ (h * ℓ) := by
    have hh := Finset.prod_le_prod (s := (univ : Finset (Fin ℓ)))
      (f := fun j => G.q 3 j) (g := fun _ => Cl * R ^ h)
      (fun _ _ => Nat.zero_le _) (fun j _ => (hl j).2)
    simpa only [Grid.row, prod_const, card_univ, Fintype.card_fin, mul_pow, ← pow_mul] using hh
  have hclo (j : Fin ℓ) : R ^ (6 * a + h) ≤ G.col a j := by
    have hh := Finset.prod_le_prod (s := (univ : Finset (Fin 3)))
      (f := fun _ => (R ^ 2) ^ a)
      (g := fun i => G.q ⟨i.val, by omega⟩ j ^ a)
      (fun _ _ => Nat.zero_le _)
      (fun i _ => Nat.pow_le_pow_left (hs i j).1.le a)
    have hh' : R ^ (6 * a) ≤ ∏ i : Fin 3, G.q ⟨i.val, by omega⟩ j ^ a := by
      simpa only [prod_const, card_univ, Fintype.card_fin, ← pow_mul, show 2 * a * 3 = 6 * a by omega] using hh
    calc
      R ^ (6 * a + h) = R ^ h * R ^ (6 * a) := by rw [pow_add]; ring
      _ ≤ G.q 3 j * ∏ i : Fin 3, G.q ⟨i.val, by omega⟩ j ^ a :=
        Nat.mul_le_mul (hl j).1.le hh'
      _ = G.col a j := rfl
  have hchi (j : Fin ℓ) : G.col a j ≤ Cl * Cs ^ (3 * a) * R ^ (6 * a + h) := by
    have hh := Finset.prod_le_prod (s := (univ : Finset (Fin 3)))
      (f := fun i => G.q ⟨i.val, by omega⟩ j ^ a)
      (g := fun _ => (Cs * R ^ 2) ^ a)
      (fun _ _ => Nat.zero_le _)
      (fun i _ => Nat.pow_le_pow_left (hs i j).2 a)
    have hh' : (∏ i : Fin 3, G.q ⟨i.val, by omega⟩ j ^ a) ≤
        Cs ^ (3 * a) * R ^ (6 * a) := by
      simpa only [prod_const, card_univ, Fintype.card_fin, mul_pow, ← pow_mul,
        show a * 3 = 3 * a by omega, show 2 * a * 3 = 6 * a by omega] using hh
    calc
      G.col a j ≤ (Cl * R ^ h) * (Cs ^ (3 * a) * R ^ (6 * a)) :=
        Nat.mul_le_mul (hl j).2 hh'
      _ = Cl * Cs ^ (3 * a) * R ^ (6 * a + h) := by rw [pow_add]; ring
  constructor
  · exact ⟨(Nat.pow_le_pow_right hR (min_le_left _ _)).trans hrlo,
      hrhi.trans (Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right hR (le_max_left _ _)))⟩
  · intro j
    exact ⟨(Nat.pow_le_pow_right hR (min_le_right _ _)).trans (hclo j),
      (hchi j).trans (Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right hR (le_max_right _ _)))⟩

end AngLarge.Realization
