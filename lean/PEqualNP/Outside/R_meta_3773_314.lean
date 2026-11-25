import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit on the raw inputs handles every flag other than (0,0).
-- The marked AND restores that one flag at the output.
theorem PEqualNP.Outside.R_meta_3773_314
    (residual :
      let d : Finset (Fin 13) := {0,1,3,9}
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 61 ∧
        (∀ p l : Fin 13, p + l ∈ d → (p ≠ 0 ∨ l ≠ 0) →
          D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l))) = true) ∧
        ∀ S : Finset (Fin 13), S.card ≤ 3 →
          D.eval (List.ofFn fun i : Fin (13+13) => Fin.addCases
            (fun p : Fin 13 => decide (p ∈ S)) (fun l : Fin 13 => decide (∀ p ∈ S, p+l ∉ d)) i) = false ∧
          D.eval (List.ofFn fun i : Fin (13+13) => Fin.addCases
            (fun p : Fin 13 => decide (∀ l ∈ S, p+l ∉ d)) (fun l : Fin 13 => decide (l ∈ S)) i) = false)
    (compileFlag : ∀ D : Circuit, Monotone2 D → ∃ C : Circuit, Monotone2 C ∧
      C.size ≤ D.size + 2 ∧ (∃ g : Gate, C.gates.head? = some g ∧ g.op = GateOp.and ∧ g.inputs = [0,13]) ∧
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = ((x 0 && x 13) || D.eval (List.ofFn x))) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false := by
  dsimp only at residual ⊢
  obtain ⟨D,hm,hs,hp,hn⟩ := residual
  obtain ⟨C,cm,cs,⟨g,hg,hop,hinputs⟩,heval⟩ := compileFlag D hm
  refine ⟨C,cm,by omega,⟨g,hg,Or.inl ⟨hop,hinputs⟩⟩,?_,?_⟩
  · intro p l hflag
    rw [heval]
    by_cases h : p = 0 ∧ l = 0
    · rcases h with ⟨rfl,rfl⟩
      have hit : (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 (0 : Fin 13))
          (Fin.natAdd 13 (0 : Fin 13)) (0 : Fin 26) &&
        PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 (0 : Fin 13))
          (Fin.natAdd 13 (0 : Fin 13)) (13 : Fin 26)) = true := by decide +kernel
      rw [hit]
      rfl
    · rw [hp p l hflag (not_and_or.mp h)]
      simp
  · intro S hsize
    let d : Finset (Fin 13) := {0,1,3,9}
    have hzero : (0:Fin 13) + 0 ∈ d := by decide +kernel
    obtain ⟨hnp,hnl⟩ := hn S hsize
    constructor
    · rw [heval,hnp,Bool.or_false]
      change (decide ((0:Fin 13) ∈ S) && decide (∀ p ∈ S, p + (0:Fin 13) ∉ d)) = false
      by_cases h : (0:Fin 13) ∈ S
      · simp [h]
        exact ⟨0,h,by simpa only [add_zero] using hzero⟩
      · simp [h]
    · rw [heval,hnl,Bool.or_false]
      change (decide (∀ l ∈ S, (0:Fin 13) + l ∉ d) && decide ((0:Fin 13) ∈ S)) = false
      by_cases h : (0:Fin 13) ∈ S
      · simp [h]
        exact ⟨0,h,by simpa only [add_zero] using hzero⟩
      · simp [h]
