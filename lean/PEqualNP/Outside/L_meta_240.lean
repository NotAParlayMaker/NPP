import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_240

private lemma getD_ofFn_false (n o : ℕ) :
    (List.ofFn (fun _ : Fin n => false)).getD o false = false := by
  by_cases ho : o < (List.ofFn (fun _ : Fin n => false)).length
  · rw [List.getD_eq_getElem _ _ ho]
    simp
  · exact List.getD_eq_default _ _ (Nat.le_of_not_lt ho)

end PEqualNP.Outside.L_meta_240

open PEqualNP.Outside.L_meta_240 in
theorem PEqualNP.Outside.L_meta_240 : ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => true) s ↔ 1 ≤ s := by
  intro n s
  constructor
  · rintro ⟨C, hsize, heval⟩
    cases h : C.gates with
    | nil =>
      have hx := heval (fun _ => false)
      simp only [BinaryCircuit.eval, BinaryCircuit.wires, h, List.foldl_nil,
        getD_ofFn_false] at hx
      cases hx
    | cons g gs =>
      simp only [BinaryCircuit.size, h, List.length_cons] at hsize
      omega
  · intro hs
    refine ⟨{ gates := [{ op := fun _ _ => true, left := 0, right := 0 }], output := n }, ?_, ?_⟩
    · simpa [BinaryCircuit.size] using hs
    · intro x
      have hlen : (List.ofFn x).length = n := List.length_ofFn
      simp only [BinaryCircuit.eval, BinaryCircuit.wires, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hlen]
