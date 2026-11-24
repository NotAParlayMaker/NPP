import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2625_1
    (suffix :
      ∃ (op : GateOp) (a b : Fin 26) (D : Circuit),
      (op = GateOp.and ∨ op = GateOp.or) ∧
      ((a.val, b.val) = (13, 14) ∨ (a.val, b.val) = (0, 1) ∨
        (a.val, b.val) = (0, 13) ∨ (a.val, b.val) = (0, 14)) ∧
      Monotone2 D ∧ D.size ≤ 62 ∧
      (∀ (p l : Fin (13 : ℕ)),
        (∃ d : Fin (13 : ℕ), (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9) ∧ p = l + d) →
          let f : Fin ((13 : ℕ) + (13 : ℕ)) → Bool :=
            fun i => Decidable.decide (i = Fin.castAdd (13 : ℕ) p ∨ i = Fin.natAdd (13 : ℕ) l)
          D.eval (List.ofFn f ++ [op.eval [f a, f b]]) = Bool.true) ∧
      ∀ (pair : ℕ × ℕ),
        (pair = ((7 : ℕ), (904 : ℕ)) ∨ pair = ((13 : ℕ), (2848 : ℕ)) ∨
          pair = ((19 : ℕ), (708 : ℕ)) ∨ pair = ((21 : ℕ), (2720 : ℕ)) ∨
          pair = ((25 : ℕ), (2656 : ℕ)) ∨ pair = ((37 : ℕ), (2440 : ℕ)) ∨
          pair = ((41 : ℕ), (2370 : ℕ)) ∨ pair = ((133 : ℕ), (808 : ℕ))) →
        ∀ (t : Fin (13 : ℕ)), (t = 1 ∨ t = 3 ∨ t = 9) →
          ∀ (q : Fin (13 : ℕ)) (flag : Bool),
            let f : Fin ((13 : ℕ) + (13 : ℕ)) → Bool := (fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1)) pair t q flag
            D.eval (List.ofFn f ++ [op.eval [f a, f b]]) = Bool.false)
    (prepend :
      ∀ (n k : ℕ) (a b : Fin n) (op : GateOp) (D : Circuit),
      (op = GateOp.and ∨ op = GateOp.or) →
      Monotone2 D → D.size ≤ k →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ k + 1 ∧
        ∀ x : Fin n → Bool,
          C.eval (List.ofFn x) = D.eval (List.ofFn x ++ [op.eval [x a, x b]])) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), (∃ x7 ∈ x1, x5 = x6 + x7) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 (x3 x5 x7 x9 x10) = Bool.false := by
  obtain ⟨op, a, b, D, hop, _hrep, monoD, sizeD, posD, negD⟩ := suffix
  obtain ⟨C, monoC, sizeC, evalC⟩ := prepend 26 62 a b op D hop monoD sizeD
  exact (show have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), (∃ x7 ∈ x1, x5 = x6 + x7) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 (x3 x5 x7 x9 x10) = Bool.false from by
    intros
    refine ⟨C, monoC, sizeC, ?_, ?_⟩
    · intro x5 x6 hinc
      have hform : ∀ d : Fin (13 : ℕ),
          d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} :
            Finset (Fin (13 : ℕ))) →
          d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9 := by decide
      obtain ⟨d, hd, heq⟩ := hinc
      have hdis : ∃ d : Fin (13 : ℕ), (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9) ∧ x5 = x6 + d :=
        ⟨d, hform d hd, heq⟩
      let f : Fin ((13 : ℕ) + (13 : ℕ)) → Bool :=
        fun i => Decidable.decide (i = Fin.castAdd (13 : ℕ) x5 ∨ i = Fin.natAdd (13 : ℕ) x6)
      have he := evalC (f : Fin 26 → Bool)
      change C.eval (List.ofFn (f : Fin 26 → Bool)) = Bool.true
      rw [he]
      exact posD x5 x6 hdis
    · intro x5 hx5 x7 hx7 x9 x10
      have hpair :
          x5 = ((7 : ℕ), (904 : ℕ)) ∨ x5 = ((13 : ℕ), (2848 : ℕ)) ∨
          x5 = ((19 : ℕ), (708 : ℕ)) ∨ x5 = ((21 : ℕ), (2720 : ℕ)) ∨
          x5 = ((25 : ℕ), (2656 : ℕ)) ∨ x5 = ((37 : ℕ), (2440 : ℕ)) ∨
          x5 = ((41 : ℕ), (2370 : ℕ)) ∨ x5 = ((133 : ℕ), (808 : ℕ)) := by
        have hx : x5 ∈ [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)),
            ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)),
            ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))] := hx5
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      have ht : x7 = 1 ∨ x7 = 3 ∨ x7 = 9 := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx7
        rcases hx7 with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      let f : Fin ((13 : ℕ) + (13 : ℕ)) → Bool := (fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1)) x5 x7 x9 x10
      have he := evalC (f : Fin 26 → Bool)
      change C.eval (List.ofFn (f : Fin 26 → Bool)) = Bool.false
      rw [he]
      exact negD x5 hpair x7 ht x9 x10)

