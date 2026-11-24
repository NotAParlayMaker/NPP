import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

-- The last two point stars provide four reusable disjunctions of line inputs.
-- Four final gates attach both stars to the output of the smaller circuit.
theorem PEqualNP.Outside.R_meta_4125_482
    (attach : let ext := fun x : Fin 14 → Bool => List.ofFn x ++
        [x 9 || x 11, (x 9 || x 11) || x 12, x 10 || x 13, (x 10 || x 13) || x 12]
      let stars := fun x : Fin 14 → Bool =>
        (x 5 && ((x 9 || x 11) || x 12)) || (x 6 && ((x 10 || x 13) || x 12))
      let legal := fun (d : ℕ) (C : Circuit) => ∀ (i : ℕ) (g : Gate), C.gates[i]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<d+i ∧ b<d+i
      let mark := fun (d : ℕ) (C : Circuit) (b : Bool) =>
        ((linearParts C (fun i => decide (i = if b = true then 7 else 0))
          (List.ofFn fun i : Fin d => decide (i.val = 0 ∨ i.val = 7))).getD C.output (false,false)).2
      ∀ C : Circuit, legal 18 C → (∃ x, C.eval (ext x) = true) →
      ∃ D : Circuit, D.size ≤ C.size+8 ∧ legal 14 D ∧
        (∀ x, D.eval (List.ofFn x) = (C.eval (ext x) || stars x)) ∧
        ∀ b, mark 14 D b = mark 18 C b)
    (smaller : let ext := fun x : Fin 14 → Bool => List.ofFn x ++
        [x 9 || x 11, (x 9 || x 11) || x 12, x 10 || x 13, (x 10 || x 13) || x 12]
      let adj := fun p l : Fin 7 => p=l ∨ p=l+1 ∨ p=l+3
      let hit := fun x : Fin 14 → Bool => ∃ p l, adj p l ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
      let legal := fun (d : ℕ) (C : Circuit) => ∀ (i : ℕ) (g : Gate), C.gates[i]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<d+i ∧ b<d+i
      let mark := fun (d : ℕ) (C : Circuit) (b : Bool) =>
        ((linearParts C (fun i => decide (i = if b = true then 7 else 0))
          (List.ofFn fun i : Fin d => decide (i.val = 0 ∨ i.val = 7))).getD C.output (false,false)).2
      ∃ C : Circuit, C.size ≤ 19 ∧ legal 18 C ∧
        (∀ p l, p.val < 5 → adj p l → C.eval (ext (fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l))) = true) ∧
        (∀ x, ¬hit x → (∀ y, (∀ i, x i=true → y i=true) → x ≠ y → hit y) → C.eval (ext x)=false) ∧
        ∀ b, mark 18 C b = false) :
    have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (7 : ℕ)) (x3 : Fin (7 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ))) ∧ x1 (Fin.castAdd (7 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (7 : ℕ) x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ (∀ (x3 x4 : Fin (7 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ)) → x2.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x3 ∨ x6 = Fin.natAdd (7 : ℕ) x4)) = Bool.true) ∧ (∀ (x3 : Fin (14 : ℕ) → Bool), ¬x1 x3 → (∀ (x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x3 x6 = Bool.true → x5 x6 = Bool.true) → x3 ≠ x5 → x1 x5) → x2.eval (List.ofFn x3) = Bool.false) ∧ ∀ (x3 : Bool), ((PEqualNP.ReadK.linearParts x2 (fun (x4 : ℕ) => Decidable.decide (x4 = if x3 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (↑x4 = (0 : ℕ) ∨ ↑x4 = (7 : ℕ)))).getD x2.output (Bool.false, Bool.false)).2 = Bool.false := by
  dsimp only at smaller attach ⊢
  obtain ⟨C, budget, law, positives, negatives, reread⟩ := smaller
  obtain ⟨D, size, shape, ordinary, marked⟩ := attach C law ⟨_, positives 0 0 (by decide) (Or.inl rfl)⟩
  refine ⟨D, by omega, shape, ?_, ?_, fun b => (marked b).trans (reread b)⟩
  · intro p l edge
    rw [ordinary]
    by_cases small : p.val < 5
    · rw [positives p l small edge]
      rfl
    · rw [Bool.or_eq_true]
      right
      have check : ∀ p l : Fin 7, ¬p.val < 5 → (p=l ∨ p=l+1 ∨ p=l+3) →
          let x := fun i : Fin 14 => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
          (x 5 && ((x 9 || x 11) || x 12)) || (x 6 && ((x 10 || x 13) || x 12)) = true := by
        decide
      exact check p l small edge
  · intro x no maximal
    rw [ordinary, negatives x no maximal]
    simp only [Bool.false_or]
    apply Bool.eq_false_iff.mpr
    intro bad
    apply no
    simp only [Bool.or_eq_true, Bool.and_eq_true] at bad
    rcases bad with ⟨hp,(hl|hl)|hl⟩ | ⟨hp,(hl|hl)|hl⟩
    · exact ⟨5,2,by decide,hp,hl⟩
    · exact ⟨5,4,by decide,hp,hl⟩
    · exact ⟨5,5,by decide,hp,hl⟩
    · exact ⟨6,3,by decide,hp,hl⟩
    · exact ⟨6,6,by decide,hp,hl⟩
    · exact ⟨6,5,by decide,hp,hl⟩
