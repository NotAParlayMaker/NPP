import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2371_773
    (kinds : ∀ (n : ℕ) (g : Gate), FanInTwo (⟨[g],0⟩ : Circuit) →
      let V := fun x : Fin n → Bool => g.op.eval (g.inputs.map fun w => (List.ofFn x).getD w false)
      (∃ b : Bool, ∀ x, V x = b) ∨
      (∃ i : Fin n, ∀ x, V x = x i) ∨
      (∃ i : Fin n, ∀ x, V x = !x i) ∨
      (∃ i j : Fin n, i ≠ j ∧ ∃ b : Bool, ∀ x,
        V x = if b then x i && x j else x i || x j))
    (orbits :
      let target := (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)))
      ∀ i j : Fin 10, ∃ σ : Fin 10 → Fin 10, σ i = 0 ∧
        σ j = (if i = j then 0 else if target (pairInput i j) then 1 else 2) ∧
        ∀ x, target (x ∘ σ) = target x)
    (relabel : ∀ (n : ℕ) (σ : Fin n → Fin n) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool) (b : Bool),
        D.eval (List.ofFn x ++ [b]) = C.eval (List.ofFn (x ∘ σ) ++ [b]))
    (lower :
      let target := (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)))
      ∀ (D : Circuit) (negate : Bool) (A : (Fin 10 → Bool) → Bool), FanInTwo D → D.size ≤ 17 →
      ((∃ b : Bool, A = fun _ => b) ∨ (A = fun x => x 0) ∨ (A = fun x => !x 0) ∨
        ∃ j : Fin 10, (j = 1 ∨ j = 2) ∧ ∃ b : Bool,
          A = fun x => if b then x 0 && x j else x 0 || x j) →
      ∃ x : Fin 10 → Bool, (if negate then !D.eval (List.ofFn x ++ [A x])
        else D.eval (List.ofFn x ++ [A x])) ≠ target x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         ∃ (x10 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x9 x10 x3 else x9 x10 x3) ≠ x8 x10 := by
  intro g C w negate firstModel model budget postedTarget postedRead
  let target := (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)))
  let V := fun x : Fin 10 → Bool => g.op.eval (g.inputs.map fun w => (List.ofFn x).getD w false)
  let canonical := fun A : (Fin 10 → Bool) → Bool =>
    (∃ b : Bool, A = fun _ => b) ∨ (A = fun x => x 0) ∨ (A = fun x => !x 0) ∨
      ∃ j : Fin 10, (j = 1 ∨ j = 2) ∧ ∃ b : Bool,
        A = fun x => if b then x 0 && x j else x 0 || x j
  have setup : ∃ (σ : Fin 10 → Fin 10) (A : (Fin 10 → Bool) → Bool),
      (∀ x, target (x ∘ σ) = target x) ∧ canonical A ∧ ∀ x, V (x ∘ σ) = A x := by
    rcases kinds 10 g firstModel with ⟨b, constant⟩ | ⟨i, copy⟩ | ⟨i, invert⟩ | ⟨i, j, distinct, b, binary⟩
    · exact ⟨id, fun _ => b, fun _ => rfl, Or.inl ⟨b, rfl⟩, fun x => constant (x ∘ id)⟩
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
  let B : Circuit := ⟨C.gates, w⟩
  obtain ⟨D, dModel, dSize, dEval⟩ := relabel 10 σ B model
  have small : D.size ≤ 17 := by
    rw [dSize]
    exact budget
  obtain ⟨x, mismatch⟩ := lower D negate A dModel small allowed
  refine ⟨x ∘ σ, ?_⟩
  change (if negate then !B.eval (List.ofFn (x ∘ σ) ++ [V (x ∘ σ)])
    else B.eval (List.ofFn (x ∘ σ) ++ [V (x ∘ σ)])) ≠ target (x ∘ σ)
  simp only [derived x, ← dEval x (A x), preserves x]
  exact mismatch
