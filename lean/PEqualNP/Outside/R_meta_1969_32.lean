import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Order the union of the strict ancestors first, then the two marked gates,
-- then the other gates used by the output. Keep the old order within each group.
theorem PEqualNP.Outside.R_meta_1969_32
    (pack : ∀ (n : ℕ) (C : Circuit) (i j : ℕ),
      let ok (D : Circuit) := IsAO2 n D ∧ ∀ g ∈ D.gates, g.inputs.Nodup
      let anc := InCone n C
      let old (s : Bool) := if s then j else i
      ok C → i ≠ j → ¬ anc i j → ¬ anc j i →
      (∀ s, anc (old s) (C.output - n)) →
      ∃ (D : Circuit) (k : ℕ), ok D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C ∧
        D.output + 1 = n + D.size ∧
        (∀ t < D.size - 1, InCone n D t (D.size - 1)) ∧
        (∀ t < k, InCone n D t k ∨ InCone n D t (k+1)) ∧
        (∀ b : Fin 2, opnd D (k+1) b < n+k) ∧
        ∀ s : Bool, let a := if s then k+1 else k
          (gateAt D a).op = (gateAt C (old s)).op ∧
          gateVal n D a = gateVal n C (old s) ∧
          ∀ b : Fin 2, wireVal n D (opnd D a b) = wireVal n C (opnd C (old s) b))
    (bound : ∀ (D : Circuit) (k : ℕ),
      IsAO2 14 D → (∀ g ∈ D.gates, g.inputs.Nodup) →
      D.output + 1 = 14 + D.size →
      (∀ t < D.size - 1, InCone 14 D t (D.size - 1)) →
      (∀ t < k, InCone 14 D t k ∨ InCone 14 D t (k+1)) →
      (∀ b : Fin 2, opnd D (k+1) b < 14+k) →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      (∀ s : Bool, let a := if s then k+1 else k
        let u : Fin 14 := if s then 7 else 0
        (gateAt D a).op = .and ∧ gateVal 14 D a (pairInput 0 7) = true ∧
        ∀ b : Fin 2, wireVal 14 D (opnd D a b) (pairInput u u) = false) →
      28 ≤ D.size) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 ≠ x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  rintro ⟨C, hsize, hwf, heval, i, j, hne, hij, hji, hi, hilive, hipair, hi0,
    hj, hjlive, hjpair, hj7⟩
  have hcfg (k : ℕ) (hk : k < C.gates.length) :
      ((gateAt C k).op = .and ∨ (gateAt C k).op = .or) ∧
      ∃ a b : ℕ, (gateAt C k).inputs = [a,b] ∧ a ≠ b ∧ a < 14+k ∧ b < 14+k := by
    apply hwf k
    change C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩)
    rw [List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  have hao : IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
      have h := (hcfg k hk).1
      change (C.gates.getD k ⟨.or, []⟩).op = .and ∨
        (C.gates.getD k ⟨.or, []⟩).op = .or at h
      rwa [List.getD_eq_getElem _ _ hk] at h
    · intro k hk w hw
      obtain ⟨a,b,hab,_,ha,hb⟩ := (hcfg k hk).2
      change w ∈ (gateAt C k).inputs at hw
      rw [hab] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      exact hw.elim (fun e => e.symm ▸ ha) (fun e => e.symm ▸ hb)
    · intro g hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
      obtain ⟨a,b,hab,_,_,_⟩ := (hcfg k hk).2
      rw [← List.getD_eq_getElem _ ⟨GateOp.or, []⟩ hk]
      change (gateAt C k).inputs.length = 2
      simp [hab]
  have hdistinct : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
    obtain ⟨a,b,hab,hab',_,_⟩ := (hcfg k hk).2
    rw [← List.getD_eq_getElem _ ⟨GateOp.or, []⟩ hk]
    change (gateAt C k).inputs.Nodup
    simpa [hab] using hab'
  have neither (a b : ℕ) (hab : a ≠ b) (hba : ¬ InCone 14 C b a)
      (live : 14+b = C.output ∨ InCone 14 C b (C.output-14)) : 14+a ≠ C.output := by
    intro eq
    rcases live with e | h
    · omega
    · apply hba
      simpa [← eq] using h
  have il := hilive.resolve_left (neither i j hne hji hjlive)
  have jl := hjlive.resolve_left (neither j i hne.symm hij hilive)
  obtain ⟨D, k, ⟨hD, hND⟩, hle, hfun, hout, hcone, hprefix, hback, hkeep⟩ :=
    pack 14 C i j ⟨hao, hdistinct⟩ hne hij hji (by intro s; cases s <;> assumption)
  have hspec (x : Fin 14 → Bool) :
      D.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    have eq := congrFun hfun x
    change D.eval (List.ofFn x) = C.eval (List.ofFn x) at eq
    rw [eq]
    exact heval x
  have hmin := bound D k hD hND hout hcone hprefix hback hspec (by
    intro s
    obtain ⟨hop, hv, hw⟩ := hkeep s
    cases s
    · exact ⟨hop.trans hi, (congrFun hv _).trans hipair,
        fun b => (congrFun (hw b) _).trans (hi0 b)⟩
    · exact ⟨hop.trans hj, (congrFun hv _).trans hjpair,
        fun b => (congrFun (hw b) _).trans (hj7 b)⟩)
  omega
