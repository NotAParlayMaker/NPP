import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3821_1
    (hleft :
      let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
        x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
        x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.MetaComplexity.FanInTwo D →
        let U := fun x : Fin 10 → Bool =>
          (D.wires (List.ofFn x)).getD a false || (D.wires (List.ofFn x)).getD b false
        (∀ x, G x = false → U x = G x) →
        (∃ i : Fin 10, D.size + 1 ≤ 15 + D.gates.countP (fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i.val)) →
        ∃ s : Equiv.Perm (Fin 10), (∀ x, G (x ∘ s) = G x) ∧
          PEqualNP.MetaComplexity.HasCircuitSize 9 (fun y => U (Fin.lastCases false y ∘ s)) 15)
    (hright :
      let G := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
        x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
        x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 18 →
        let W := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
        let U := fun x => W x a || W x b
        (∃ x, W x a = true ∧ W x b = false) →
        (∃ x, W x a = false ∧ W x b = true) →
        (∀ x, G x = false ∨ (List.ofFn x).count true ≤ 2 → U x = G x) →
        (∀ i : Fin 10, 15 + D.gates.countP (fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i.val) < D.size + 1) →
        ∃ (s : Equiv.Perm (Fin 10)) (v : Bool),
          (∀ x, G (x ∘ s) = G x) ∧ PEqualNP.MetaComplexity.HasCircuitSize 9
            (fun y => U (Fin.lastCases v y ∘ s)) (if v then 10 else 15)) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12) := by
  classical
  dsimp only
  intro D a b fan size ha hb rows
  by_cases high : ∃ i : Fin 10, D.size + 1 ≤ 15 + D.gates.countP (fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i.val)
  · obtain ⟨s, auto, E, fanE, sizeE, sim⟩ :=
      hleft D a b fan (fun x hx => rows x (Or.inl hx)) high
    exact ⟨s, false, E, auto, fanE, sizeE, sim⟩
  · have low (i : Fin 10) : 15 + D.gates.countP (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i.val) < D.size + 1 :=
      Nat.lt_of_not_ge (fun h => high ⟨i,h⟩)
    obtain ⟨s, v, auto, E, fanE, sizeE, sim⟩ := hright D a b fan size ha hb rows low
    exact ⟨s, v, E, auto, fanE, sizeE, sim⟩
