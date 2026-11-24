import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3837_1
    (hA : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x3.gates[1]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∀ (x6 : Fin (11 : ℕ)) (x7 : Bool), ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval (x2 x8 ++ [x7 != (x2 x8).getD (↑x6) Bool.false]) ≠ x1 x8)
    (hB : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x3.gates[1]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 1) → ∀ (x6 : Fin (11 : ℕ)) (x7 : Bool), ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval (x2 x8 ++ [x7 != (x2 x8).getD (↑x6) Bool.false]) ≠ x1 x8)
    (hC : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), x3.gates[1]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs = [a, b] ∧ a < 11 ∧ b < 11) → ∀ (x6 : Fin (11 : ℕ)) (x7 : Bool), ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval (x2 x8 ++ [x7 != (x2 x8).getD (↑x6) Bool.false]) ≠ x1 x8)
    (hD : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), x3.gates[1]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs = [a, b] ∧ (11 ≤ a ∨ 11 ≤ b)) → ∀ (x6 : Fin (11 : ℕ)) (x7 : Bool), ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval (x2 x8 ++ [x7 != (x2 x8).getD (↑x6) Bool.false]) ≠ x1 x8) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → ∀ (x6 : Fin (11 : ℕ)) (x7 : Bool), ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval (x2 x8 ++ [x7 != (x2 x8).getD (↑x6) Bool.false]) ≠ x1 x8 := by
  intro x1 x2 x3 hfan hsize
  have hlen : x3.gates.length = 13 := hsize
  have h1lt : 1 < x3.gates.length := by omega
  obtain ⟨g, hg⟩ : ∃ g, x3.gates[1]? = some g := ⟨x3.gates[1]'h1lt, List.getElem?_eq_getElem h1lt⟩
  have hgeq : g = x3.gates[1]'h1lt := Option.some.inj (hg.symm.trans (List.getElem?_eq_getElem h1lt))
  have hgmem : g ∈ x3.gates := by rw [hgeq]; exact List.getElem_mem h1lt
  rcases hfan g hgmem with ⟨hop, hin⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hopA | hopO | hopN
  ·
    rcases Nat.lt_or_ge g.inputs.length 2 with hl | hl
    · exact hB x3 hfan hsize ⟨g, hg, Or.inl hopA, by omega⟩
    · have hl2 : g.inputs.length = 2 := by omega
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := List.length_eq_two.mp hl2
      rcases Nat.lt_or_ge a 11 with ha | ha
      · rcases Nat.lt_or_ge b 11 with hb | hb
        · exact hC x3 hfan hsize ⟨g, a, b, hg, Or.inl hopA, hab, ha, hb⟩
        · exact hD x3 hfan hsize ⟨g, a, b, hg, Or.inl hopA, hab, Or.inr hb⟩
      · exact hD x3 hfan hsize ⟨g, a, b, hg, Or.inl hopA, hab, Or.inl ha⟩
  ·
    rcases Nat.lt_or_ge g.inputs.length 2 with hl | hl
    · exact hB x3 hfan hsize ⟨g, hg, Or.inr hopO, by omega⟩
    · have hl2 : g.inputs.length = 2 := by omega
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := List.length_eq_two.mp hl2
      rcases Nat.lt_or_ge a 11 with ha | ha
      · rcases Nat.lt_or_ge b 11 with hb | hb
        · exact hC x3 hfan hsize ⟨g, a, b, hg, Or.inr hopO, hab, ha, hb⟩
        · exact hD x3 hfan hsize ⟨g, a, b, hg, Or.inr hopO, hab, Or.inr hb⟩
      · exact hD x3 hfan hsize ⟨g, a, b, hg, Or.inr hopO, hab, Or.inl ha⟩
  · exact hA x3 hfan hsize ⟨g, hg, hopN⟩
