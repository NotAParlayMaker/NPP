import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_713 : ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r := by
  classical
  intro n m r S B h
  induction B using Finset.induction_on with
  | empty => simp
  | @insert a B ha ih =>
    let T := Finset.univ.filter (fun i : Fin m => a ∈ S i)
    let U := Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)
    have hi : (Finset.univ.filter (fun i : Fin m => ∃ x ∈ insert a B, x ∈ S i)) = T ∪ U := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_union, T, U]
      aesop
    rw [hi, Finset.card_insert_of_notMem ha]
    have hT : T.card ≤ r := h a
    have hc := Finset.card_union_le T U
    change U.card ≤ B.card * r at ih
    nlinarith
