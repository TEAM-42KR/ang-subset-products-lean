import AngCounterexample.LargeData

/-! Finite Bertrand chains, used only to realize the prime grid. -/

open Finset

namespace AngLarge.Realization

lemma prime_chain (k x : ℕ) (hx : 0 < x) :
    ∃ f : Fin k → ℕ, Function.Injective f ∧
      ∀ j, (f j).Prime ∧ x < f j ∧ f j ≤ 2 ^ k * x := by
  induction k generalizing x with
  | zero =>
      exact ⟨Fin.elim0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
  | succ k ih =>
      obtain ⟨p, hp, hxp, hpu⟩ := Nat.exists_prime_lt_and_le_two_mul x (by omega)
      obtain ⟨f, hf, hb⟩ := ih p hp.pos
      refine ⟨Fin.cons p f, Fin.cons_injective_of_injective ?_ hf, ?_⟩
      · rintro ⟨j, hj⟩
        exact (ne_of_lt (hb j).2.1) hj.symm
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp only [Fin.cons_zero]
          refine ⟨hp, hxp, hpu.trans ?_⟩
          have hk : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
          rw [pow_succ]
          nlinarith
        · simp only [Fin.cons_succ]
          refine ⟨(hb j).1, hxp.trans (hb j).2.1, (hb j).2.2.trans ?_⟩
          rw [pow_succ]
          simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (2 ^ k) hpu

lemma prime_grid (ℓ R h : ℕ) (hℓ : 0 < ℓ) (hR : 0 < R)
    (hsep : 2 ^ (3 * ℓ) * R ^ 2 < R ^ h) :
    ∃ G : Grid ℓ,
      (∀ i : Fin 3, ∀ j, R ^ 2 < G.q ⟨i.val, by omega⟩ j ∧
        G.q ⟨i.val, by omega⟩ j ≤ 2 ^ (3 * ℓ) * R ^ 2) ∧
      (∀ j, R ^ h < G.q 3 j ∧ G.q 3 j ≤ 2 ^ ℓ * R ^ h) := by
  obtain ⟨f, hf, hb⟩ := prime_chain (3 * ℓ) (R ^ 2) (pow_pos hR _)
  obtain ⟨g, hg, hc⟩ := prime_chain ℓ (R ^ h) (pow_pos hR _)
  let q : Fin 4 → Fin ℓ → ℕ := fun i j =>
    if hi : i.val < 3 then f (finProdFinEquiv (⟨i.val, hi⟩, j)) else g j
  have hqprime : ∀ i j, (q i j).Prime := by
    intro i j
    dsimp [q]
    split
    · exact (hb _).1
    · exact (hc _).1
  have hqinj : Function.Injective (fun ij : Fin 4 × Fin ℓ => q ij.1 ij.2) := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ he
    by_cases hi : i.val < 3 <;> by_cases hi' : i'.val < 3
    · simp only [q, dif_pos hi, dif_pos hi'] at he
      have hh := finProdFinEquiv.injective (hf he)
      have hij : i = i' := Fin.ext (congrArg (fun z : Fin 3 × Fin ℓ => z.1.val) hh)
      exact Prod.ext hij (congrArg (fun z : Fin 3 × Fin ℓ => z.2) hh)
    · simp only [q, dif_pos hi, dif_neg hi'] at he
      exact False.elim ((hb _).2.2.trans_lt (hsep.trans (hc j').2.1) |>.ne he)
    · simp only [q, dif_neg hi, dif_pos hi'] at he
      exact False.elim ((hb _).2.2.trans_lt (hsep.trans (hc j).2.1) |>.ne he.symm)
    · simp only [q, dif_neg hi, dif_neg hi'] at he
      have hii : i = i' := Fin.ext (by have := i.isLt; have := i'.isLt; omega)
      exact Prod.ext hii (hg he)
  refine ⟨⟨q, hqprime, hqinj⟩, ?_, ?_⟩
  · intro i j
    simp only [q, dif_pos i.isLt]
    exact (hb _).2
  · intro j
    simp only [q, show ¬ (3 : Fin 4).val < 3 by decide, dif_neg]
    exact (hc _).2

end AngLarge.Realization
