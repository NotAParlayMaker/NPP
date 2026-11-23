import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_239

private theorem outputSupport (gs : List BinaryGate) (out n : ℕ) :
    ∃ S : Finset ℕ, S.card ≤ gs.length + 1 ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ j ∈ S, x.getD j false = y.getD j false) →
        (BinaryCircuit.mk gs out).eval x = (BinaryCircuit.mk gs out).eval y := by
  induction gs generalizing n with
  | nil => exact ⟨{out}, by simp, fun _ _ _ _ h => h out (by simp)⟩
  | cons g gs ih =>
    obtain ⟨T, hcard, hT⟩ := ih (n + 1)
    let S := if n ∈ T then insert g.left (insert g.right (T.erase n)) else T
    refine ⟨S, ?_, ?_⟩
    · simp only [S, List.length_cons]
      split_ifs with hn
      · have := Finset.card_insert_le g.left (insert g.right (T.erase n))
        have := Finset.card_insert_le g.right (T.erase n)
        have := Finset.card_erase_add_one hn
        omega
      · omega
    · intro x y hx hy h
      apply hT
      · simp [hx]
      · simp [hy]
      · intro j hj
        rcases lt_trichotomy j n with hlt | rfl | hgt
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          apply h j
          by_cases hn : n ∈ T <;> simp [S, hn, hj, hlt.ne]
        · have hl := h g.left (by simp [S, hj])
          have hr := h g.right (by simp [S, hj])
          rw [List.getD_append_right _ _ _ _ hx.le, List.getD_append_right _ _ _ _ hy.le]
          rw [hl, hr, hx, hy]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_239

open PEqualNP.Outside.L_meta_239

theorem PEqualNP.Outside.L_meta_239 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      (∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x) →
      ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n f s → n ≤ s + 1 := by
  intro n f hdep s ⟨C, hsize, heval⟩
  obtain ⟨S, hcard, hS⟩ := outputSupport C.gates C.output n
  have hsub : Finset.range n ⊆ S := by
    intro j hj
    let i : Fin n := ⟨j, Finset.mem_range.mp hj⟩
    by_contra hmissing
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    rw [← heval, ← heval]
    apply hS _ _ (by simp) (by simp)
    intro k hk
    by_cases hkn : k < n
    · have hne : (⟨k, hkn⟩ : Fin n) ≠ i :=
        fun e => hmissing ((show k = j from congrArg Fin.val e) ▸ hk)
      simp [hkn, Function.update_of_ne hne]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  simpa using (Finset.card_le_card hsub).trans (hcard.trans (Nat.add_le_add_right hsize 1))
