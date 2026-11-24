import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4284_1
    (hB : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 = (0 : ℕ) →         (10 : ℕ) ≤ x2 →           x2 ≤ x3 →             x3 < (23 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1[0]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 1) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false && x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))))
    (hC : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 = (0 : ℕ) →         (10 : ℕ) ≤ x2 →           x2 ≤ x3 →             x3 < (23 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), x1[0]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs = [a, b] ∧ a < 10 ∧ b < 10) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false && x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))))
    (hD : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 = (0 : ℕ) →         (10 : ℕ) ≤ x2 →           x2 ≤ x3 →             x3 < (23 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), x1[0]? = Option.some g ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs = [a, b] ∧ (10 ≤ a ∨ 10 ≤ b)) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false && x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 = (0 : ℕ) →         (10 : ℕ) ≤ x2 →           x2 ≤ x3 →             x3 < (23 : ℕ) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]);                 (x11.getD x2 Bool.false && x11.getD x3 Bool.false) ≠ (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 x3 hlen hfan hnot h10 hx23 hlt
  have h0lt : 0 < x1.length := by omega
  obtain ⟨g, hg⟩ : ∃ g, x1[0]? = some g := ⟨x1[0]'h0lt, List.getElem?_eq_getElem h0lt⟩
  have hgeq : g = x1[0]'h0lt := Option.some.inj (hg.symm.trans (List.getElem?_eq_getElem h0lt))
  have hgmem : g ∈ x1 := by rw [hgeq]; exact List.getElem_mem h0lt
  rcases hfan g hgmem with ⟨hop, hin⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hopA | hopO | hopN
  ·
    rcases Nat.lt_or_ge g.inputs.length 2 with hl | hl
    · exact hB x1 x2 x3 hlen hfan hnot h10 hx23 hlt ⟨g, hg, Or.inl hopA, by omega⟩
    · have hl2 : g.inputs.length = 2 := by omega
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := List.length_eq_two.mp hl2
      rcases Nat.lt_or_ge a 10 with ha | ha
      · rcases Nat.lt_or_ge b 10 with hb | hb
        · exact hC x1 x2 x3 hlen hfan hnot h10 hx23 hlt ⟨g, a, b, hg, Or.inl hopA, hab, ha, hb⟩
        · exact hD x1 x2 x3 hlen hfan hnot h10 hx23 hlt ⟨g, a, b, hg, Or.inl hopA, hab, Or.inr hb⟩
      · exact hD x1 x2 x3 hlen hfan hnot h10 hx23 hlt ⟨g, a, b, hg, Or.inl hopA, hab, Or.inl ha⟩
  ·
    rcases Nat.lt_or_ge g.inputs.length 2 with hl | hl
    · exact hB x1 x2 x3 hlen hfan hnot h10 hx23 hlt ⟨g, hg, Or.inr hopO, by omega⟩
    · have hl2 : g.inputs.length = 2 := by omega
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := List.length_eq_two.mp hl2
      rcases Nat.lt_or_ge a 10 with ha | ha
      · rcases Nat.lt_or_ge b 10 with hb | hb
        · exact hC x1 x2 x3 hlen hfan hnot h10 hx23 hlt ⟨g, a, b, hg, Or.inr hopO, hab, ha, hb⟩
        · exact hD x1 x2 x3 hlen hfan hnot h10 hx23 hlt ⟨g, a, b, hg, Or.inr hopO, hab, Or.inr hb⟩
      · exact hD x1 x2 x3 hlen hfan hnot h10 hx23 hlt ⟨g, a, b, hg, Or.inr hopO, hab, Or.inl ha⟩
  · have hpos : 0 < List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 := by
      rw [List.countP_eq_length_filter, List.length_pos_iff_ne_nil]
      intro hnil
      have hmem : g ∈ x1.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) := by
        rw [List.mem_filter]
        exact ⟨hgmem, by rw [hopN]; rfl⟩
      rw [hnil] at hmem
      simp at hmem
    omega
