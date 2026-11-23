import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_238 : ∀ s : ℕ,
    PEqualNP.MetaComplexity.HasBinarySize 2 (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔ 1 ≤ s := by
  intro s
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
      by_cases hlt : C.output < 2
      · interval_cases ho : C.output
        · have he := hf ![false, true]
          rw [heval (List.ofFn ![false, true])] at he
          have hlen : 0 < (List.ofFn ![false, true] : List Bool).length := by simp
          rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn] at he
          simp at he
        · have he := hf ![true, false]
          rw [heval (List.ofFn ![true, false])] at he
          have hlen : 1 < (List.ofFn ![true, false] : List Bool).length := by simp
          rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn] at he
          simp at he
      · have he := hf ![false, true]
        rw [heval (List.ofFn ![false, true])] at he
        have hlen : (List.ofFn ![false, true] : List Bool).length ≤ C.output := by
          simpa [List.length_ofFn] using Nat.le_of_not_lt hlt
        rw [List.getD_eq_default _ _ hlen] at he
        simp at he
    · omega
  · intro hs
    refine ⟨⟨[⟨fun a b => xor a b, 0, 1⟩], 2⟩, ?_, ?_⟩
    · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hs
    · intro x
      have hw : PEqualNP.MetaComplexity.BinaryCircuit.wires
          (⟨[⟨fun a b => xor a b, 0, 1⟩], 2⟩ : PEqualNP.MetaComplexity.BinaryCircuit) (List.ofFn x)
          = List.ofFn x ++ [xor (x 0) (x 1)] := by
        simp [PEqualNP.MetaComplexity.BinaryCircuit.wires]
      rw [PEqualNP.MetaComplexity.BinaryCircuit.eval, hw]
      have hlen : 2 < (List.ofFn x ++ [xor (x 0) (x 1)]).length := by simp
      rw [List.getD_eq_getElem _ _ hlen, List.getElem_append]
      simp