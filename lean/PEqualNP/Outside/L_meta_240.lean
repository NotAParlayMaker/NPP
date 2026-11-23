import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_240 : ∀ n s : ℕ,
    PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => true) s ↔ 1 ≤ s := by
  intro n s
  constructor
  · intro h
    obtain ⟨C, hC, hf⟩ := h
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      have hsz : C.size = 0 := Nat.le_zero.mp hC
      have hgates : C.gates = [] := List.length_eq_zero_iff.mp hsz
      have heval : ∀ l : List Bool, C.eval l = l.getD C.output false := by
        intro l
        simp [PEqualNP.MetaComplexity.BinaryCircuit.eval,
          PEqualNP.MetaComplexity.BinaryCircuit.wires, hgates]
      by_cases hlt : C.output < n
      · let x0 : Fin n → Bool := Function.update (fun _ => true) ⟨C.output, hlt⟩ false
        have he := hf x0
        rw [heval (List.ofFn x0)] at he
        have hlen : C.output < (List.ofFn x0).length := by simpa [List.length_ofFn] using hlt
        rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn] at he
        simp [x0] at he
      · have he := hf (fun _ => true)
        rw [heval (List.ofFn (fun _ : Fin n => true))] at he
        have hlen : (List.ofFn (fun _ : Fin n => true) : List Bool).length ≤ C.output := by
          simpa [List.length_ofFn] using Nat.le_of_not_lt hlt
        rw [List.getD_eq_default _ _ hlen] at he
        simp at he
    · omega
  · intro hs
    refine ⟨⟨[⟨fun _ _ => true, 0, 0⟩], n⟩, ?_, ?_⟩
    · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hs
    · intro x
      have hw : PEqualNP.MetaComplexity.BinaryCircuit.wires
          (⟨[⟨fun _ _ => true, 0, 0⟩], n⟩ : PEqualNP.MetaComplexity.BinaryCircuit) (List.ofFn x)
          = List.ofFn x ++ [true] := by
        simp [PEqualNP.MetaComplexity.BinaryCircuit.wires]
      rw [PEqualNP.MetaComplexity.BinaryCircuit.eval, hw]
      have hlen : n < (List.ofFn x ++ [true]).length := by simp
      rw [List.getD_eq_getElem _ _ hlen, List.getElem_append]
      simp
