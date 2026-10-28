import Mathlib

/-! Shared mathematical data for the large-prime construction. -/

open Finset

namespace AngLarge

abbrev Exponent (t : ℕ) := Fin 3 → Fin (t + 1)

def degree {t : ℕ} (α : Exponent t) : ℕ := ∑ i, (α i).val

def layer (t : ℕ) : Finset (Exponent t) :=
  univ.filter (fun α => 1 ≤ degree α ∧ degree α ≤ t)

def coeff (t : ℕ) : ℕ := 1 + ∑ α ∈ layer t, (α 0).val

structure Grid (ℓ : ℕ) where
  q : Fin 4 → Fin ℓ → ℕ
  prime : ∀ i j, (q i j).Prime
  injective : Function.Injective (fun ij : Fin 4 × Fin ℓ => q ij.1 ij.2)

namespace Grid

variable {ℓ : ℕ}

def row (G : Grid ℓ) (i : Fin 4) : ℕ := ∏ j, G.q i j

def small (G : Grid ℓ) (i : Fin 3) : ℕ := G.row ⟨i.val, by omega⟩

def col (G : Grid ℓ) (a : ℕ) (j : Fin ℓ) : ℕ :=
  G.q 3 j * ∏ i : Fin 3, G.q ⟨i.val, by omega⟩ j ^ a

def H (G : Grid ℓ) (a : ℕ) : ℕ := ∏ j, G.col a j

def monomial (G : Grid ℓ) {t : ℕ} (α : Exponent t) : ℕ :=
  ∏ i, G.small i ^ (α i).val

def form (G : Grid ℓ) (a : ℕ) (j0 : Fin ℓ) (x : ℕ)
    (i : Fin 3) (j : Fin ℓ) : ℤ :=
  (x.factorization (G.q ⟨i.val, by omega⟩ j) : ℤ) -
  (x.factorization (G.q ⟨i.val, by omega⟩ j0) : ℤ) -
  (a : ℤ) * ((x.factorization (G.q 3 j) : ℤ) -
    (x.factorization (G.q 3 j0) : ℤ))

end Grid

structure Cutoffs {ℓ : ℕ} (G : Grid ℓ) (t a n p : ℕ) where
  d : ℕ
  D : ℕ
  b : ℕ
  B : ℕ
  d_pos : 0 < d
  small_bounds : ∀ i, d ≤ G.small i ∧ G.small i ≤ D
  large_bounds : b ≤ G.row 3 ∧ G.row 3 ≤ B
  col_bounds : ∀ j, b ≤ G.col a j ∧ G.col a j ≤ B
  D_le : D ≤ n / p
  s_lt_dsq : n / p < d ^ 2
  s_lt_b : n / p < b
  Dt_le : D ^ t ≤ n
  B_le : B ≤ n
  n_lt_dpow : n < d ^ (t + 1)
  n_lt_bd : n < b * d
  n_lt_bsq : n < b ^ 2

end AngLarge
