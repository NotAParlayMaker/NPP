import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2069_713
    (centers : ∀ C : Circuit, TopForm.IsAO2 26 C → C.size ≤ 64 →
      (∀ x : Fin 26 → Bool, circuitFun 26 C x = true ↔ ∃ p l : Fin 13,
        p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ x, gateVal 26 C j x = true → circuitFun 26 C x = true) →
      let side := TopForm.side (n := 26) C
      let birth := fun j => j<C.size ∧ (gateAt C j).op = GateOp.and ∧ (side j 0).Nonempty ∧ (side j 1).Nonempty
      ∃ P L : Finset (Fin 13), P.card + L.card ≤ 13 ∧
        (∀ p l : Fin 13, p-l ∈ ([0,1,3,9] : List (Fin 13)) → p∈P ∨ l∈L) ∧
        ∀ j, birth j → ∃ b : Fin 2, (∃ p ∈ P, side j b = {Fin.castAdd 13 p}) ∨
          ∃ l ∈ L, side j b = {Fin.natAdd 13 l})
    (rigidity : ∀ C : Circuit, TopForm.IsAO2 26 C → C.size ≤ 64 →
      (∀ x : Fin 26 → Bool, circuitFun 26 C x = true ↔ ∃ p l : Fin 13,
        p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ x, gateVal 26 C j x = true → circuitFun 26 C x = true) →
      let side := TopForm.side (n := 26) C
      let birth := fun j => j<C.size ∧ (gateAt C j).op = GateOp.and ∧ (side j 0).Nonempty ∧ (side j 1).Nonempty
      (∃ points : Bool, ∀ j, birth j → ∃ (b : Fin 2) (v : Fin 13),
        side j b = {if points then Fin.castAdd 13 v else Fin.natAdd 13 v}) →
      TopForm.andPairs 26 C = 0) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∀ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 → ∀ (x17 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x17)).getD ((26 : ℕ) + x14) Bool.false = Bool.true → x4.eval (List.ofFn x17) = Bool.true) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  dsimp only
  intro C p l dp dl bound gates computes nested safe _edge _traceP _traceL
  have orientation : ∀ P L : Finset (Fin 13), P.card+L.card ≤ 13 →
      (∀ p l : Fin 13, p-l ∈ ([0,1,3,9] : List (Fin 13)) → p∈P ∨ l∈L) →
      P=∅ ∨ L=∅ := by
    intro P L card covers
    have sub : Finset.univ \ P ⊆ L := by
      intro v hv
      have h := covers v v (by simp)
      exact h.resolve_left (Finset.mem_sdiff.mp hv).2
    have comp : Finset.univ \ P = L := by
      apply Finset.eq_of_subset_of_card_le sub
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ P)]
      simp only [Finset.card_univ,Fintype.card_fin]
      omega
    have next (p : Fin 13) (hp : p ∈ P) : p+1 ∈ P := by
      have edge : (p+1)-p ∈ ([0,1,3,9] : List (Fin 13)) := by simp
      rcases covers (p+1) p edge with h|h
      · exact h
      · rw [← comp] at h
        exact False.elim ((Finset.mem_sdiff.mp h).2 hp)
    by_cases empty : P = ∅
    · exact Or.inl empty
    right
    obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have reach : ∀ d : Fin 13, p + d ∈ P := by
      intro d
      induction d using Fin.induction with
      | zero => simpa using hp
      | succ k ih =>
        have step : (p + k.castSucc) + 1 = p + k.succ := by
          rw [add_assoc]
          congr 1
          exact Fin.ext (by simp)
        exact step ▸ next _ ih
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    rw [← comp] at hl
    apply (Finset.mem_sdiff.mp hl).2
    simpa using reach (l-p)
  have ao : TopForm.IsAO2 26 C := by
    constructor
    · intro g mem
      obtain ⟨j,hj,eq⟩ := List.getElem_of_mem mem
      exact (gates j g (by rw [← eq, List.getElem?_eq_getElem hj])).1
    constructor
    · intro j hj i hi
      obtain ⟨a,b,inputs,_ne,ca,cb⟩ := (gates j _ (List.getElem?_eq_getElem hj)).2
      have same : gateAt C j = C.gates[j] := by
        change C.gates.getD j _ = _
        simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
      rw [same,inputs] at hi
      rcases List.mem_cons.mp hi with h|h
      · simpa [h] using ca
      · simpa using (List.mem_singleton.mp h) ▸ cb
    · intro g mem
      obtain ⟨j,hj,eq⟩ := List.getElem_of_mem mem
      obtain ⟨_,_,ins,_⟩ := (gates j g (by rw [← eq, List.getElem?_eq_getElem hj])).2
      simp [ins]
  have fn : ∀ x : Fin 26 → Bool, circuitFun 26 C x = true ↔ ∃ p l : Fin 13,
        p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    intro x
    change C.eval (List.ofFn x) = true ↔ _
    simpa only [List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton] using computes x
  obtain ⟨P,L,size,covers,owned⟩ := centers C ao bound fn safe
  have noNested := rigidity C ao bound fn safe (by
    rcases orientation P L size covers with hp|hl
    · refine ⟨false,?_⟩
      intro j hj
      obtain ⟨b,h|⟨v,_,h⟩⟩ := owned j hj
      · simp [hp] at h
      · exact ⟨b,v,h⟩
    · refine ⟨true,?_⟩
      intro j hj
      obtain ⟨b,⟨v,_,h⟩|h⟩ := owned j hj
      · exact ⟨b,v,h⟩
      · simp [hl] at h)
  omega
