import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5790_1
    (minor : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => (x2.wires (List.ofFn x7)).getD x3 Bool.false;       ∃ (x8 : Fin (10 : ℕ) → Bool), x8 (9 : Fin (10 : ℕ)) = Bool.false ∧ (if x4 = Bool.true then !x7 x8 else x7 x8) ≠ x1 x8)
    (restrictCircuit : let F := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (C : Circuit) (b : Bool), FanInTwo C → C.size ≤ 17 →
        (∀ x, (if b then !(C.eval (List.ofFn x)) else C.eval (List.ofFn x)) = F x) →
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 15 ∧
          ∀ x : Fin 10 → Bool, x 9 = false →
            (if b then !(D.eval (List.ofFn x)) else D.eval (List.ofFn x)) = F x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         x2.size ≤ (16 : ℕ) →           have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));           have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;           ∃ (x11 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x10 x11 x3 else x10 x11 x3) ≠ x9 x11 := by
  intro g C o b hg hC _ cap
  dsimp only
  by_contra! agrees
  let D : Circuit := ⟨g :: C.gates, o⟩
  have legal : FanInTwo D := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hg a (by simp)
    · exact hC a ha
  have small : D.size ≤ 17 := by
    change C.gates.length + 1 ≤ 17
    change C.gates.length ≤ 16 at cap
    omega
  obtain ⟨E, hE, sizeE, ev⟩ := restrictCircuit D b legal small agrees
  obtain ⟨x, hx, different⟩ := minor E E.output b hE sizeE
  exact different (ev x hx)
