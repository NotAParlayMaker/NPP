import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.R_meta_2766_1

abbrev E2766 : (Fin 9 → Bool) → Bool := fun x =>
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

abbrev Hyps2766 (C : Circuit) : Prop :=
  C.gates.length = 15 ∧
  C.output = 23 ∧
  C.gates[0]? = some ⟨.or, [0, 3]⟩ ∧
  (∀ (i : ℕ) (hi : i < C.gates.length),
    let g := C.gates[i]
    let ok : ℕ → Prop := fun a => a < 9 + i ∨ a = 24
    let rank : ℕ → ℕ := fun a => if a < 9 then a else if a = 24 then 9 else a + 1
    g = ⟨.and, []⟩ ∨
    (∃ a, ok a ∧ g = ⟨.not, [a]⟩) ∨
    ∃ a b, ok a ∧ ok b ∧ rank a ≤ rank b ∧
      (g = ⟨.and, [a, b]⟩ ∨ g = ⟨.or, [a, b]⟩)) ∧
  C.gates.countP (fun g => g.op.eval [false]) = 0

abbrev Goal2766 (C : Circuit) : Prop := circuitFun 9 C ≠ E2766

lemma no_true_gate2766 (C : Circuit)
    (hcount : C.gates.countP (fun g => g.op.eval [false]) = 0)
    (g : Gate) (hg : g ∈ C.gates) : g.op.eval [false] = false := by
  have := List.countP_eq_zero.mp hcount g hg
  simpa using this

lemma gate1_form2766 (C : Circuit) (h : Hyps2766 C) :
    C.gates[1]? = some ⟨.and, []⟩ ∨
    ∃ (op : GateOp) (a b : ℕ),
      (op = .and ∨ op = .or) ∧ (a < 10 ∨ a = 24) ∧ (b < 10 ∨ b = 24) ∧
      (if a < 9 then a else if a = 24 then 9 else a + 1) ≤
        (if b < 9 then b else if b = 24 then 9 else b + 1) ∧
      C.gates[1]? = some ⟨op, [a, b]⟩ := by
  obtain ⟨hlen, -, -, hshape, hcount⟩ := h
  have h1lt : 1 < C.gates.length := by omega
  have h1 := hshape 1 h1lt
  dsimp only at h1
  rcases h1 with hAnd | ⟨a, ha, hNot⟩ | ⟨a, b, ha, hb, hrank, hAB⟩
  · left
    rw [List.getElem?_eq_getElem h1lt, hAnd]
  · exfalso
    have hg1 : (⟨.not, [a]⟩ : Gate) ∈ C.gates := by
      rw [← hNot]; exact List.getElem_mem h1lt
    have hfalse := no_true_gate2766 C hcount _ hg1
    exact Bool.noConfusion hfalse
  · rcases hAB with hAB | hAB
    · right
      exact ⟨.and, a, b, Or.inl rfl, ha, hb, hrank, by
        rw [List.getElem?_eq_getElem h1lt, hAB]⟩
    · right
      exact ⟨.or, a, b, Or.inr rfl, ha, hb, hrank, by
        rw [List.getElem?_eq_getElem h1lt, hAB]⟩

end PEqualNP.Outside.R_meta_2766_1

theorem PEqualNP.Outside.R_meta_2766_1 :
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, []⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 0]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 1]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 2]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 3]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [0, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 1]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 2]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 3]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [1, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [2, 2]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [2, 3]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [2, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [2, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [2, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [2, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [2, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [2, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [2, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [3, 3]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [3, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [3, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [3, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [3, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [3, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [3, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [3, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [4, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [4, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [4, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [4, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [4, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [4, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [4, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [5, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [5, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [5, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [5, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [5, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [5, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [6, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [6, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [6, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [6, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [6, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [7, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [7, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [7, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [7, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [8, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [8, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [8, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [9, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [24, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.and, [24, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 0]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 1]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 2]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 3]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [0, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 1]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 2]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 3]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [1, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [2, 2]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [2, 3]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [2, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [2, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [2, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [2, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [2, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [2, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [2, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [3, 3]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [3, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [3, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [3, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [3, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [3, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [3, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [3, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [4, 4]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [4, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [4, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [4, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [4, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [4, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [4, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [5, 5]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [5, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [5, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [5, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [5, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [5, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [6, 6]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [6, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [6, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [6, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [6, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [7, 7]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [7, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [7, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [7, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [8, 8]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [8, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [8, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [9, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [24, 9]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    (∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → C.gates[1]? = some ⟨.or, [24, 24]⟩ → PEqualNP.Outside.R_meta_2766_1.Goal2766 C) →
    ∀ C : Circuit, PEqualNP.Outside.R_meta_2766_1.Hyps2766 C → PEqualNP.Outside.R_meta_2766_1.Goal2766 C := by
  intro h_nil h_and_0_0 h_and_0_1 h_and_0_2 h_and_0_3 h_and_0_4 h_and_0_5 h_and_0_6 h_and_0_7 h_and_0_8 h_and_0_9 h_and_0_24 h_and_1_1 h_and_1_2 h_and_1_3 h_and_1_4 h_and_1_5 h_and_1_6 h_and_1_7 h_and_1_8 h_and_1_9 h_and_1_24 h_and_2_2 h_and_2_3 h_and_2_4 h_and_2_5 h_and_2_6 h_and_2_7 h_and_2_8 h_and_2_9 h_and_2_24 h_and_3_3 h_and_3_4 h_and_3_5 h_and_3_6 h_and_3_7 h_and_3_8 h_and_3_9 h_and_3_24 h_and_4_4 h_and_4_5 h_and_4_6 h_and_4_7 h_and_4_8 h_and_4_9 h_and_4_24 h_and_5_5 h_and_5_6 h_and_5_7 h_and_5_8 h_and_5_9 h_and_5_24 h_and_6_6 h_and_6_7 h_and_6_8 h_and_6_9 h_and_6_24 h_and_7_7 h_and_7_8 h_and_7_9 h_and_7_24 h_and_8_8 h_and_8_9 h_and_8_24 h_and_9_9 h_and_24_9 h_and_24_24 h_or_0_0 h_or_0_1 h_or_0_2 h_or_0_3 h_or_0_4 h_or_0_5 h_or_0_6 h_or_0_7 h_or_0_8 h_or_0_9 h_or_0_24 h_or_1_1 h_or_1_2 h_or_1_3 h_or_1_4 h_or_1_5 h_or_1_6 h_or_1_7 h_or_1_8 h_or_1_9 h_or_1_24 h_or_2_2 h_or_2_3 h_or_2_4 h_or_2_5 h_or_2_6 h_or_2_7 h_or_2_8 h_or_2_9 h_or_2_24 h_or_3_3 h_or_3_4 h_or_3_5 h_or_3_6 h_or_3_7 h_or_3_8 h_or_3_9 h_or_3_24 h_or_4_4 h_or_4_5 h_or_4_6 h_or_4_7 h_or_4_8 h_or_4_9 h_or_4_24 h_or_5_5 h_or_5_6 h_or_5_7 h_or_5_8 h_or_5_9 h_or_5_24 h_or_6_6 h_or_6_7 h_or_6_8 h_or_6_9 h_or_6_24 h_or_7_7 h_or_7_8 h_or_7_9 h_or_7_24 h_or_8_8 h_or_8_9 h_or_8_24 h_or_9_9 h_or_24_9 h_or_24_24 C hC
  rcases PEqualNP.Outside.R_meta_2766_1.gate1_form2766 C hC with h | ⟨op, a, b, hop, ha, hb, hrank, hgate⟩
  · exact h_nil C hC h
  · rcases hop with rfl | rfl
    · -- second gate is AND[a,b]
      have ha11 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 24 := by omega
      have hb11 : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 24 := by omega
      rcases ha11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact h_and_0_0 C hC hgate
        · exact h_and_0_1 C hC hgate
        · exact h_and_0_2 C hC hgate
        · exact h_and_0_3 C hC hgate
        · exact h_and_0_4 C hC hgate
        · exact h_and_0_5 C hC hgate
        · exact h_and_0_6 C hC hgate
        · exact h_and_0_7 C hC hgate
        · exact h_and_0_8 C hC hgate
        · exact h_and_0_9 C hC hgate
        · exact h_and_0_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact h_and_1_1 C hC hgate
        · exact h_and_1_2 C hC hgate
        · exact h_and_1_3 C hC hgate
        · exact h_and_1_4 C hC hgate
        · exact h_and_1_5 C hC hgate
        · exact h_and_1_6 C hC hgate
        · exact h_and_1_7 C hC hgate
        · exact h_and_1_8 C hC hgate
        · exact h_and_1_9 C hC hgate
        · exact h_and_1_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_and_2_2 C hC hgate
        · exact h_and_2_3 C hC hgate
        · exact h_and_2_4 C hC hgate
        · exact h_and_2_5 C hC hgate
        · exact h_and_2_6 C hC hgate
        · exact h_and_2_7 C hC hgate
        · exact h_and_2_8 C hC hgate
        · exact h_and_2_9 C hC hgate
        · exact h_and_2_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_and_3_3 C hC hgate
        · exact h_and_3_4 C hC hgate
        · exact h_and_3_5 C hC hgate
        · exact h_and_3_6 C hC hgate
        · exact h_and_3_7 C hC hgate
        · exact h_and_3_8 C hC hgate
        · exact h_and_3_9 C hC hgate
        · exact h_and_3_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_and_4_4 C hC hgate
        · exact h_and_4_5 C hC hgate
        · exact h_and_4_6 C hC hgate
        · exact h_and_4_7 C hC hgate
        · exact h_and_4_8 C hC hgate
        · exact h_and_4_9 C hC hgate
        · exact h_and_4_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_and_5_5 C hC hgate
        · exact h_and_5_6 C hC hgate
        · exact h_and_5_7 C hC hgate
        · exact h_and_5_8 C hC hgate
        · exact h_and_5_9 C hC hgate
        · exact h_and_5_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_and_6_6 C hC hgate
        · exact h_and_6_7 C hC hgate
        · exact h_and_6_8 C hC hgate
        · exact h_and_6_9 C hC hgate
        · exact h_and_6_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_and_7_7 C hC hgate
        · exact h_and_7_8 C hC hgate
        · exact h_and_7_9 C hC hgate
        · exact h_and_7_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_and_8_8 C hC hgate
        · exact h_and_8_9 C hC hgate
        · exact h_and_8_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_and_9_9 C hC hgate
        · exact absurd hrank (by decide)
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_and_24_9 C hC hgate
        · exact h_and_24_24 C hC hgate
    · -- second gate is OR[a,b]
      have ha11 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 24 := by omega
      have hb11 : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 24 := by omega
      rcases ha11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact h_or_0_0 C hC hgate
        · exact h_or_0_1 C hC hgate
        · exact h_or_0_2 C hC hgate
        · exact h_or_0_3 C hC hgate
        · exact h_or_0_4 C hC hgate
        · exact h_or_0_5 C hC hgate
        · exact h_or_0_6 C hC hgate
        · exact h_or_0_7 C hC hgate
        · exact h_or_0_8 C hC hgate
        · exact h_or_0_9 C hC hgate
        · exact h_or_0_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact h_or_1_1 C hC hgate
        · exact h_or_1_2 C hC hgate
        · exact h_or_1_3 C hC hgate
        · exact h_or_1_4 C hC hgate
        · exact h_or_1_5 C hC hgate
        · exact h_or_1_6 C hC hgate
        · exact h_or_1_7 C hC hgate
        · exact h_or_1_8 C hC hgate
        · exact h_or_1_9 C hC hgate
        · exact h_or_1_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_or_2_2 C hC hgate
        · exact h_or_2_3 C hC hgate
        · exact h_or_2_4 C hC hgate
        · exact h_or_2_5 C hC hgate
        · exact h_or_2_6 C hC hgate
        · exact h_or_2_7 C hC hgate
        · exact h_or_2_8 C hC hgate
        · exact h_or_2_9 C hC hgate
        · exact h_or_2_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_or_3_3 C hC hgate
        · exact h_or_3_4 C hC hgate
        · exact h_or_3_5 C hC hgate
        · exact h_or_3_6 C hC hgate
        · exact h_or_3_7 C hC hgate
        · exact h_or_3_8 C hC hgate
        · exact h_or_3_9 C hC hgate
        · exact h_or_3_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_or_4_4 C hC hgate
        · exact h_or_4_5 C hC hgate
        · exact h_or_4_6 C hC hgate
        · exact h_or_4_7 C hC hgate
        · exact h_or_4_8 C hC hgate
        · exact h_or_4_9 C hC hgate
        · exact h_or_4_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_or_5_5 C hC hgate
        · exact h_or_5_6 C hC hgate
        · exact h_or_5_7 C hC hgate
        · exact h_or_5_8 C hC hgate
        · exact h_or_5_9 C hC hgate
        · exact h_or_5_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_or_6_6 C hC hgate
        · exact h_or_6_7 C hC hgate
        · exact h_or_6_8 C hC hgate
        · exact h_or_6_9 C hC hgate
        · exact h_or_6_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_or_7_7 C hC hgate
        · exact h_or_7_8 C hC hgate
        · exact h_or_7_9 C hC hgate
        · exact h_or_7_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_or_8_8 C hC hgate
        · exact h_or_8_9 C hC hgate
        · exact h_or_8_24 C hC hgate
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_or_9_9 C hC hgate
        · exact absurd hrank (by decide)
      · rcases hb11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact absurd hrank (by decide)
        · exact h_or_24_9 C hC hgate
        · exact h_or_24_24 C hC hgate
