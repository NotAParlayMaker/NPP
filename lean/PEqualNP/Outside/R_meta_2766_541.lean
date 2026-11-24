import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2766_541
    (hconst : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.gates.length = 15 → C.output = 23 →
      C.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩ →
      (∀ (i : ℕ) (h : i < C.gates.length),
        C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ ∨
        ∃ a b : ℕ, (a < 9 + i ∨ a = 24) ∧ (b < 9 + i ∨ b = 24) ∧
          (if a < 9 then a else if a = 24 then 9 else a + 1) ≤
            (if b < 9 then b else if b = 24 then 9 else b + 1) ∧
          (C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ ∨
            C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩)) →
      C.gates[1]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ →
      PEqualNP.MetaComplexity.circuitFun 9 C ≠ fun x : Fin 9 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun n => x (Fin.ofNat 9 (n / 10)) && x (Fin.ofNat 9 (n % 10))))
    (hand : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.gates.length = 15 → C.output = 23 →
      C.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩ →
      (∀ (i : ℕ) (h : i < C.gates.length),
        C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ ∨
        ∃ a b : ℕ, (a < 9 + i ∨ a = 24) ∧ (b < 9 + i ∨ b = 24) ∧
          (if a < 9 then a else if a = 24 then 9 else a + 1) ≤
            (if b < 9 then b else if b = 24 then 9 else b + 1) ∧
          (C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ ∨
            C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩)) →
      (∃ a b : ℕ, C.gates[1]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩) →
      PEqualNP.MetaComplexity.circuitFun 9 C ≠ fun x : Fin 9 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun n => x (Fin.ofNat 9 (n / 10)) && x (Fin.ofNat 9 (n % 10))))
    (hor : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.gates.length = 15 → C.output = 23 →
      C.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩ →
      (∀ (i : ℕ) (h : i < C.gates.length),
        C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ ∨
        ∃ a b : ℕ, (a < 9 + i ∨ a = 24) ∧ (b < 9 + i ∨ b = 24) ∧
          (if a < 9 then a else if a = 24 then 9 else a + 1) ≤
            (if b < 9 then b else if b = 24 then 9 else b + 1) ∧
          (C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ ∨
            C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩)) →
      (∃ a b : ℕ, C.gates[1]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩) →
      PEqualNP.MetaComplexity.circuitFun 9 C ≠ fun x : Fin 9 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun n => x (Fin.ofNat 9 (n / 10)) && x (Fin.ofNat 9 (n % 10)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C hC hcount
  obtain ⟨hlen, hout, h0, hshape⟩ := hC
  have hf : (fun x4 : Fin 9 → Bool => x4 0 && x4 1 || x4 1 && x4 2 || x4 2 && x4 3 ||
      x4 3 && x4 4 || x4 4 && x4 0 || x4 0 && x4 5 || x4 1 && x4 6 || x4 2 && x4 7 ||
      x4 3 && x4 8 || x4 5 && x4 7 || x4 6 && x4 8 || x4 8 && x4 5) =
      fun x : Fin 9 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun n => x (Fin.ofNat 9 (n / 10)) && x (Fin.ofNat 9 (n % 10))) := by
    funext x
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  rw [hf]
  have hnot : ∀ g ∈ C.gates, g.op.eval [false] = false := by
    intro g hg
    have := (List.countP_eq_zero.mp hcount) g hg
    simpa using this
  have hshape' : ∀ (i : ℕ) (h : i < C.gates.length),
      C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ ∨
      ∃ a b : ℕ, (a < 9 + i ∨ a = 24) ∧ (b < 9 + i ∨ b = 24) ∧
        (if a < 9 then a else if a = 24 then 9 else a + 1) ≤
          (if b < 9 then b else if b = 24 then 9 else b + 1) ∧
        (C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ ∨
          C.gates[i] = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩) := by
    intro i h
    rcases hshape i h with h1 | ⟨a, _, h2⟩ | ⟨a, b, ha, hb, hab, h3⟩
    · exact Or.inl h1
    · exfalso
      have := hnot _ (List.getElem_mem h)
      rw [h2] at this
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at this
    · exact Or.inr ⟨a, b, ha, hb, hab, h3⟩
  have h1lt : 1 < C.gates.length := by omega
  have hg1 : C.gates[1]? = some C.gates[1] := List.getElem?_eq_getElem h1lt
  rcases hshape' 1 h1lt with hc | ⟨a, b, _, _, _, ha | ho⟩
  · exact hconst C hlen hout h0 hshape' (by rw [hg1, hc])
  · exact hand C hlen hout h0 hshape' ⟨a, b, by rw [hg1, ha]⟩
  · exact hor C hlen hout h0 hshape' ⟨a, b, by rw [hg1, ho]⟩
