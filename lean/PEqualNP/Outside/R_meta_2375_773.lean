import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2375_773
    (kinds : ∀ (n : ℕ) (g : Gate), FanInTwo (⟨[g],0⟩ : Circuit) →
      let V := fun x : Fin n → Bool => g.op.eval (g.inputs.map fun w => (List.ofFn x).getD w false)
      (∃ b : Bool, ∀ x, V x = b) ∨
      (∃ i : Fin n, ∀ x, V x = x i) ∨
      (∃ i : Fin n, ∀ x, V x = !x i) ∨
      (∃ i j : Fin n, i ≠ j ∧ ∃ b : Bool, ∀ x,
        V x = if b then x i && x j else x i || x j))
    (orbits :
      let target := (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)))
      ∀ i j : Fin 10, ∃ σ : Equiv.Perm (Fin 10), σ i = 0 ∧
        σ j = (if i = j then 0 else if target (pairInput i j) then 1 else 2) ∧
        ∀ x, target (x ∘ σ) = target x)
    (relabel : ∀ (n : ℕ) (σ : Fin n → Fin n) (C : Circuit), FanInTwo C →
      ∃ (D : Circuit) (wire : ℕ → ℕ), FanInTwo D ∧ D.size = C.size ∧
        ∀ (x : Fin n → Bool) (b : Bool) (w : ℕ),
          (D.wires (List.ofFn x ++ [b])).getD (wire w) false =
          (C.wires (List.ofFn (x ∘ σ) ++ [b])).getD w false)
    (lower :
      let target := (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)))
      ∀ (D : Circuit) (u v : ℕ) (A : (Fin 10 → Bool) → Bool), FanInTwo D → D.size ≤ 17 →
      ((∃ b : Bool, A = fun _ => b) ∨ (A = fun x => x 0) ∨ (A = fun x => !x 0) ∨
        ∃ j : Fin 10, (j = 1 ∨ j = 2) ∧ ∃ b : Bool,
          A = fun x => if b then x 0 && x j else x 0 || x j) →
      let read := fun (x : Fin 10 → Bool) (w : ℕ) => (D.wires (List.ofFn x ++ [A x])).getD w false
      (∃ x, read x u = true ∧ read x v = false) →
      (∃ x, read x u = false ∧ read x v = true) →
      (∀ x, target x = true → read x u = true ∧ read x v = true) →
      ∃ x, target x = false ∧ read x u = true ∧ read x v = true) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  intro g C u v firstModel model budget postedTarget postedRead uOnly vOnly both
  let target := (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)))
  let V := fun x : Fin 10 → Bool => g.op.eval (g.inputs.map fun w => (List.ofFn x).getD w false)
  let canonical := fun A : (Fin 10 → Bool) → Bool =>
    (∃ b : Bool, A = fun _ => b) ∨ (A = fun x => x 0) ∨ (A = fun x => !x 0) ∨
      ∃ j : Fin 10, (j = 1 ∨ j = 2) ∧ ∃ b : Bool,
        A = fun x => if b then x 0 && x j else x 0 || x j
  have setup : ∃ (σ : Equiv.Perm (Fin 10)) (A : (Fin 10 → Bool) → Bool),
      (∀ x, target (x ∘ σ) = target x) ∧ canonical A ∧ ∀ x, V (x ∘ σ) = A x := by
    rcases kinds 10 g firstModel with ⟨b, constant⟩ | ⟨i, copy⟩ | ⟨i, invert⟩ | ⟨i, j, distinct, b, binary⟩
    · exact ⟨Equiv.refl _, fun _ => b, fun _ => rfl, Or.inl ⟨b, rfl⟩, fun x => constant x⟩
    · obtain ⟨σ, first, _, preserves⟩ := orbits i i
      refine ⟨σ, fun x => x 0, preserves, Or.inr (Or.inl rfl), ?_⟩
      intro x
      simpa only [V, Function.comp_apply, first] using copy (x ∘ σ)
    · obtain ⟨σ, first, _, preserves⟩ := orbits i i
      refine ⟨σ, fun x => !x 0, preserves, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      intro x
      simpa only [V, Function.comp_apply, first] using invert (x ∘ σ)
    · obtain ⟨σ, first, second, preserves⟩ := orbits i j
      have pairSide : σ j = 1 ∨ σ j = 2 := by
        rw [second, if_neg distinct]
        split <;> simp
      refine ⟨σ, fun x => if b then x 0 && x (σ j) else x 0 || x (σ j),
        preserves, Or.inr (Or.inr (Or.inr ⟨σ j, pairSide, b, rfl⟩)), ?_⟩
      intro x
      simpa only [V, Function.comp_apply, first] using binary (x ∘ σ)
  obtain ⟨σ, A, preserves, allowed, derived⟩ := setup
  obtain ⟨D, wire, dModel, dSize, dEval⟩ := relabel 10 σ C model
  have small : D.size ≤ 17 := by rwa [dSize]
  let read := fun (x : Fin 10 → Bool) (w : ℕ) => (D.wires (List.ofFn x ++ [A x])).getD w false
  have same (x : Fin 10 → Bool) (w : ℕ) : read x (wire w) = postedRead (x ∘ σ) w := by
    change read x (wire w) = (C.wires (List.ofFn (x ∘ σ) ++ [V (x ∘ σ)])).getD w false
    rw [derived x]
    exact dEval x (A x) w
  have inputs (x : Fin 10 → Bool) : (x ∘ σ.symm) ∘ σ = x := by
    funext i
    simp [Function.comp_apply]
  have uWitness : ∃ x, read x (wire u) = true ∧ read x (wire v) = false := by
    obtain ⟨x, hx⟩ := uOnly
    refine ⟨x ∘ σ.symm, ?_⟩
    rwa [same, same, inputs]
  have vWitness : ∃ x, read x (wire u) = false ∧ read x (wire v) = true := by
    obtain ⟨x, hx⟩ := vOnly
    refine ⟨x ∘ σ.symm, ?_⟩
    rwa [same, same, inputs]
  have positives (x : Fin 10 → Bool) (hx : target x = true) :
      read x (wire u) = true ∧ read x (wire v) = true := by
    rw [same, same]
    apply both
    change target (x ∘ σ) = true
    rwa [preserves]
  obtain ⟨x, hx, hu, hv⟩ := lower D (wire u) (wire v) A dModel small allowed uWitness vWitness positives
  refine ⟨x ∘ σ, ?_, ?_, ?_⟩
  · change target (x ∘ σ) = false
    rwa [preserves]
  · exact (same x u).symm.trans hu
  · exact (same x v).symm.trans hv
