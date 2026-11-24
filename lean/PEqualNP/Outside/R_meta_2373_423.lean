import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A formula can use the first gate repeatedly. The complementary search
-- requires either a later inverter or a repeated intermediate wire.
theorem PEqualNP.Outside.R_meta_2373_423
  (tree : ∀ (t : Gate) (C : Circuit) (a b : ℕ),
    FanInTwo (Circuit.mk [t] 0) → Monotone2 C →
    (∀ i, 11 ≤ i → ([a,b] ++ C.gates.flatMap Gate.inputs).count i ≤ 1) →
    let G := fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
    let W := fun (x : Fin 10 → Bool) (j : ℕ) => (C.wires ((Circuit.mk [t] 0).wires (List.ofFn x))).getD j false
    (∀ x,(W x a || W x b) = G x) → 18 ≤ C.size)
  (rest : ∀ (t : Gate) (C : Circuit) (a b : ℕ),
    FanInTwo (Circuit.mk [t] 0) → FanInTwo C → C.size ≤ 17 →
    ((∃ g ∈ C.gates,g.op = .not) ∨ ∃ i,11 ≤ i ∧ 2 ≤ ([a,b] ++ C.gates.flatMap Gate.inputs).count i) →
    let G := fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
    let W := fun (x : Fin 10 → Bool) (j : ℕ) => (C.wires ((Circuit.mk [t] 0).wires (List.ofFn x))).getD j false
    (∃ x,W x a = true ∧ W x b = false) → (∃ x,W x a = false ∧ W x b = true) →
    ¬ ∀ x,(W x a || W x b)=G x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro t C a b ht hc lim
  dsimp only
  let W := fun (x : Fin 10 → Bool) (j : ℕ) => (C.wires ((Circuit.mk [t] 0).wires (List.ofFn x))).getD j false
  let G := fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
  intro left right off
  by_contra fail
  have expand (x : Fin 10 → Bool) : G x = (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))) := by
    simp only [G,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  have compute (x : Fin 10 → Bool) : (W x a || W x b)=G x := by
    rw [expand]
    cases e : (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))
    · obtain ⟨ha,hb⟩ := off x e
      change W x a=false at ha
      change W x b=false at hb
      rw [ha,hb]; rfl
    · cases h : W x a || W x b
      · obtain ⟨ha,hb⟩ := Bool.or_eq_false_iff.mp h
        exact (fail ⟨x,e,ha,hb⟩).elim
      · rfl
  by_cases bad : (∃ g ∈ C.gates,g.op=.not) ∨ ∃ i,11 ≤ i ∧ 2 ≤ ([a,b] ++ C.gates.flatMap Gate.inputs).count i
  · exact rest t C a b ht hc lim bad left right compute
  · have mono : Monotone2 C := by
      intro g hg
      obtain ⟨op,len⟩ := hc g hg
      refine ⟨?_,len⟩
      rcases op with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact (bad (Or.inl ⟨g,hg,h⟩)).elim
    have once (i) (hi : 11 ≤ i) : ([a,b] ++ C.gates.flatMap Gate.inputs).count i ≤1 := by
      by_contra! h
      exact bad (Or.inr ⟨i,hi,by omega⟩)
    have bound := tree t C a b ht mono once compute
    omega
