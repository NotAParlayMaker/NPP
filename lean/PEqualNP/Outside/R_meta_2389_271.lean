import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2389_271
    (h1500 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 ∧ (∀ x : Fin 26 → Bool, (∀ wa : Fin 13, (Finset.univ.filter (fun pa : Fin 13 => (∃ da : ℕ, da ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wa.val + da) % 13 = pa.val) ∧ x (Fin.castAdd 13 pa) = true)).card ≤ 2) → PEqualNP.MetaComplexity.circuitFun 26 C x = true → ∃ pb wb : Fin 13, (∃ db : ℕ, db ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wb.val + db) % 13 = pb.val) ∧ x (Fin.castAdd 13 pb) = true ∧ x (Fin.natAdd 13 wb) = true) ∧ (∀ pc wc : Fin 13, (∃ dc : ℕ, dc ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wc.val + dc) % 13 = pc.val) → PEqualNP.MetaComplexity.circuitFun 26 C (fun k : Fin 26 => decide (k = Fin.castAdd 13 pc ∨ k = Fin.natAdd 13 wc)) = true)))
    (h2145 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((¬∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∧ ¬∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false)
    (h_boundary :
      let E (p l : Fin 13) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      ¬ ∃ C : Circuit, IsAO2 26 C ∧ C.size ≤ 63 ∧
        ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 ∧
        ¬ HasLineDegree 26 (Finset.range 13) C 1 ∧
        (∀ p l : Fin 13, E p l → C.eval (List.ofFn fun i : Fin 26 =>
          decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) ∧
        (∀ A : Finset (Fin 13),
          (∀ p ∉ A, ∃ l : Fin 13, E p l ∧ ∀ z ∈ A, ¬ E z l) →
          C.eval (List.ofFn fun i : Fin 26 => Fin.addCases (fun p => decide (p ∈ A))
            (fun l => decide (∀ p ∈ A, ¬ E p l)) i) = false)) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (64 : ℕ) ≤ x1.size := by
  classical
  intro C hw hx
  by_contra small
  by_cases linear : HasLineDegree 26 (Finset.Ico 13 26) C 1 ∨ HasLineDegree 26 (Finset.range 13) C 1
  · let edge (p l : Fin 13) : Prop := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
    have nat_offsets : ∀ p l : Fin 13,
        (∃ d ∈ ({0,1,3,9} : Finset ℕ), (l.val+d)%13 = p.val) ↔ edge p l := by
      simp [edge]
      decide
    have fin_offsets : ∀ p l : Fin 13,
        (∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = l+d) ↔ edge p l := by
      simp [edge]

    have sides : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide
    have pts : ∀ p q : Fin 13, Fin.castAdd 13 p = Fin.castAdd 13 q → p = q := by decide
    have lns : ∀ p q : Fin 13, Fin.natAdd 13 p = Fin.natAdd 13 q → p = q := by decide
    have hm : Monotone2 C := fun g hg => ⟨hw.1 g hg, Nat.le_of_eq (hw.2.2 g hg)⟩
    have hs : C.size ≤ 63 := by omega
    rcases linear with hl | hp
    · apply h1500
      refine ⟨C, hm, hs, hl, ?_, ?_⟩
      · intro x _ h
        obtain ⟨p,l,hpl,hp,hl⟩ := (hx x).1 h
        exact ⟨p,l,(nat_offsets p l).2 hpl,hp,hl⟩
      · intro p l h
        exact (hx _).2 ⟨p,l,(nat_offsets p l).1 h,by simp,by simp⟩
    · apply h2145
      refine ⟨C, hm, hs, hp, ?_, ?_⟩
      · intro p l h
        exact (hx _).2 ⟨p,l,(fin_offsets p l).1 h,by simp,by simp⟩
      · intro A _ _
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨p,l,hpl,hp,hl⟩ := (hx _).1 h
        have pin : p ∈ A := by
          rcases of_decide_eq_true hp with ⟨q,hq,eq⟩ | ⟨l',eq,_⟩
          · exact (pts p q eq).symm ▸ hq
          · exact (sides p l' eq).elim
        rcases of_decide_eq_true hl with ⟨q,_,eq⟩ | ⟨l',eq,hn⟩
        · exact sides q l eq.symm
        · have ll := lns l l' eq
          subst l'
          exact hn p pin ((fin_offsets p l).2 hpl)
  · apply h_boundary
    refine ⟨C, hw, by omega, (fun h => linear (Or.inl h)), (fun h => linear (Or.inr h)), ?_, ?_⟩
    · intro p l he
      exact (hx _).2 ⟨p, l, he, by simp, by simp⟩
    · intro A hclosed
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, l, he, hp, hl⟩ := (hx _).1 h
      simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
      exact hl p hp he
