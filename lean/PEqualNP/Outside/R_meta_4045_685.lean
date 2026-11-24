import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4045_685
    (aliasSound : ∀ C : Circuit, IsAO2 26 C →
        let R (v : Fin 26) := C.gates.foldl (fun s g =>
          have a : ℕ := s.getD (g.inputs.getD 0 0) v.val
          have b : ℕ := s.getD (g.inputs.getD 1 0) v.val
          have o : Bool := g.op.eval [false,true]
          s ++ [if a = b then a else if a = v.val then if o = true then b else a else
            if b = v.val then if o = true then a else b else s.length]) (List.range 26)
        ∀ (v : Fin 26) (j : ℕ), j < C.size → ∀ x : Fin 26 → Bool, x v = false →
          wireVal 26 C ((R v).getD (26+j) v.val) x = wireVal 26 C (26+j) x)
    (flatLower : ∀ C : Circuit, IsAO2 26 C →
        (∀ x : Fin 26 → Bool, wireVal 26 C C.output x = true ↔
          ∃ p l : Fin 13, p ∈ singerLines3 l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (¬(∃ i j : ℕ, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j)) → 64 ≤ C.size)
    (residual : ∀ C : Circuit, IsAO2 26 C → C.size ≤ 62 →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, wireVal 26 C C.output x = true ↔
          ∃ p l : Fin 13, p ∈ singerLines3 l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        (∃ i j : ℕ, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) →
        let R (v : Fin 26) := C.gates.foldl (fun s g =>
          have a : ℕ := s.getD (g.inputs.getD 0 0) v.val
          have b : ℕ := s.getD (g.inputs.getD 1 0) v.val
          have o : Bool := g.op.eval [false,true]
          s ++ [if a = b then a else if a = v.val then if o = true then b else a else
            if b = v.val then if o = true then a else b else s.length]) (List.range 26)
        (∀ v : Fin 26, ((Finset.range C.size).filter fun j => (R v).getD (26+j) v.val < 26+j).card ≤ 4) →
        ∃ (v : Fin 26) (J : Finset ℕ), 5 ≤ J.card ∧ ∀ j ∈ J, j < C.size ∧
          ∃ k < 26+j, ∀ x : Fin 26 → Bool, x v = false → wireVal 26 C (26+j) x = wireVal 26 C k x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool), (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) → x1.size ≤ (62 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) → (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) → ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12) := by
  intro C W hgate size hW correct
  classical
  have ao : IsAO2 26 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
      exact (hgate j g hj).1
    · intro j hj i hi
      have gat : C.gates[j]? = some (gateAt C j) := by
        have eq : gateAt C j = C.gates[j]'hj := by
          change C.gates.getD j ⟨.or,[]⟩ = _
          exact List.getD_eq_getElem _ _ hj
        rw [eq]
        exact List.getElem?_eq_getElem hj
      obtain ⟨_,a,b,form,_,ha,hb⟩ := hgate j _ gat
      rw [form] at hi
      have choice : i = a ∨ i = b := by simpa using hi
      rcases choice with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨_,a,b,form,_,_,_⟩ := hgate j g hj
      rw [form]
      rfl
  have nd : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨_,a,b,form,ne,_,_⟩ := hgate j g hj
    simp [form,ne]
  have val (x : Fin 26 → Bool) (i : ℕ) : W x i = wireVal 26 C i x := hW x i
  have inc : ∀ p l : Fin 13,
      (p=l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ↔ p ∈ singerLines3 l := by decide
  have computes (x : Fin 26 → Bool) : wireVal 26 C C.output x = true ↔
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    rw [← val, correct x]
    simp only [inc]
  have nest : ∃ i j : ℕ, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j := by
    by_contra flat
    have big := flatLower C ao computes flat
    omega
  let R (v : Fin 26) := C.gates.foldl (fun s g =>
          have a : ℕ := s.getD (g.inputs.getD 0 0) v.val
          have b : ℕ := s.getD (g.inputs.getD 1 0) v.val
          have o : Bool := g.op.eval [false,true]
          s ++ [if a = b then a else if a = v.val then if o = true then b else a else
            if b = v.val then if o = true then a else b else s.length]) (List.range 26)
  let killed (v : Fin 26) := (Finset.range C.size).filter (fun j => (R v).getD (26+j) v.val < 26+j)
  by_cases enough : ∃ v : Fin 26, 5 ≤ (killed v).card
  · obtain ⟨v,more⟩ := enough
    refine ⟨v,killed v,more,?_⟩
    intro j hj
    obtain ⟨whereJ,earlier⟩ := Finset.mem_filter.mp hj
    have within := Finset.mem_range.mp whereJ
    refine ⟨within,true,false,(R v).getD (26+j) v.val,earlier,?_⟩
    intro x hx
    simp only [val,Bool.true_and,Bool.or_false]
    exact (aliasSound C ao v j within x hx).symm
  · have few : ∀ v : Fin 26, (killed v).card ≤ 4 := by
      intro v
      by_contra h
      exact enough ⟨v,by omega⟩
    obtain ⟨v,J,more,hasAlias⟩ := residual C ao size nd computes nest few
    refine ⟨v,J,more,?_⟩
    intro j hj
    obtain ⟨within,k,earlier,same⟩ := hasAlias j hj
    refine ⟨within,true,false,k,earlier,?_⟩
    intro x hx
    simp only [val,Bool.true_and,Bool.or_false]
    exact same x hx
