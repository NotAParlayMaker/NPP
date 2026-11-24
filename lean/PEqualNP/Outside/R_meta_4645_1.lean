import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4645_1
    (hA : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = !x3 (0 : Fin (9 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (x1.gates.length ≤ 1 ∨ ∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (16 : ℕ) ≤ x1.size)
    (hB : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = !x3 (0 : Fin (9 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 1) → (16 : ℕ) ≤ x1.size)
    (hC : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = !x3 (0 : Fin (9 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), x1.gates[1]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs = [a, b] ∧ a < 10 ∧ b < 10) → (16 : ℕ) ≤ x1.size)
    (hD : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = !x3 (0 : Fin (9 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), x1.gates[1]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs = [a, b] ∧ (10 ≤ a ∨ 10 ≤ b)) → (16 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = !x3 (0 : Fin (9 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro x1 hfan hwire hfun
  by_contra hsmall
  push_neg at hsmall
  rcases Nat.lt_or_ge x1.gates.length 2 with hl | hl
  · have hx := hA x1 hfan hwire hfun (Or.inl (by omega)); omega
  · have h1lt : 1 < x1.gates.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, x1.gates[1]? = some g := ⟨x1.gates[1]'h1lt, List.getElem?_eq_getElem h1lt⟩
    have hgeq : g = x1.gates[1]'h1lt := Option.some.inj (hg.symm.trans (List.getElem?_eq_getElem h1lt))
    have hgmem : g ∈ x1.gates := by rw [hgeq]; exact List.getElem_mem h1lt
    rcases hfan g hgmem with ⟨hop, hin⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hopA | hopO | hopN
    ·
      rcases Nat.lt_or_ge g.inputs.length 2 with hl | hl
      · have hx := hB x1 hfan hwire hfun ⟨g, hg, Or.inl hopA, by omega⟩; omega
      · have hl2 : g.inputs.length = 2 := by omega
        obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := List.length_eq_two.mp hl2
        rcases Nat.lt_or_ge a 10 with ha | ha
        · rcases Nat.lt_or_ge b 10 with hb | hb
          · have hx := hC x1 hfan hwire hfun ⟨g, a, b, hg, Or.inl hopA, hab, ha, hb⟩; omega
          · have hx := hD x1 hfan hwire hfun ⟨g, a, b, hg, Or.inl hopA, hab, Or.inr hb⟩; omega
        · have hx := hD x1 hfan hwire hfun ⟨g, a, b, hg, Or.inl hopA, hab, Or.inl ha⟩; omega
    ·
      rcases Nat.lt_or_ge g.inputs.length 2 with hl | hl
      · have hx := hB x1 hfan hwire hfun ⟨g, hg, Or.inr hopO, by omega⟩; omega
      · have hl2 : g.inputs.length = 2 := by omega
        obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := List.length_eq_two.mp hl2
        rcases Nat.lt_or_ge a 10 with ha | ha
        · rcases Nat.lt_or_ge b 10 with hb | hb
          · have hx := hC x1 hfan hwire hfun ⟨g, a, b, hg, Or.inr hopO, hab, ha, hb⟩; omega
          · have hx := hD x1 hfan hwire hfun ⟨g, a, b, hg, Or.inr hopO, hab, Or.inr hb⟩; omega
        · have hx := hD x1 hfan hwire hfun ⟨g, a, b, hg, Or.inr hopO, hab, Or.inl ha⟩; omega
    · have hx := hA x1 hfan hwire hfun (Or.inr ⟨g, hg, hopN⟩); omega
