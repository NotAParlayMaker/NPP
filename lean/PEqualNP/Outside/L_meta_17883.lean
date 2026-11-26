import Mathlib
import PEqualNP.Defs
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
theorem PEqualNP.Outside.L_meta_17883 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : List (ℕ × ℕ)),   have x6 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x3] : PEqualNP.CircuitLowerBounds.Gate }], output := x2.output : PEqualNP.CircuitLowerBounds.Circuit };   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → List (ℕ × ℕ) → Prop := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : List (ℕ × ℕ)) => ∀ x10 < x8.size, PEqualNP.ReadTwo.isAnd x8 x10 → ∃ x13 ∈ x9, ∃ x14 ∈ [x13.1, x13.2], x14 = x7 + x10 ∨ x7 ≤ x14 ∧ PEqualNP.EdgeOwnership.InCone x7 x8 x10 (x14 - x7);   PEqualNP.TopForm.IsAO2 x1 x2 → x3 < x1 + x2.size → x7 x1 x2 ((x3, x4) :: x5) → x7 x1 x6 ((x1 + x2.size, x4) :: x5)) := by
  intro n C a b T
  let g : Gate := ⟨.and,[a,a]⟩
  let D : Circuit := ⟨C.gates++[g],C.output⟩
  intro appended live _ bound active j hj isAnd
  change j<D.size at hj
  change ReadTwo.isAnd D j at isAnd
  have size : D.size=C.size+1 := by simp [D,Circuit.size]
  by_cases early : j<C.size
  · have gate : gateAt D j=gateAt C j := by
      simp [D,gateAt,List.getD_eq_getElem?_getD,List.getElem?_append_left (show j<C.gates.length from early)]
    have orig : ReadTwo.isAnd C j := ⟨early,by simpa only [gate] using isAnd.2⟩
    let cs := EdgeOwnership.cones n C
    have len (gs : List Gate) (s : List (List ℕ)) :
        (gs.foldl (EdgeOwnership.coneStep n) s).length=s.length+gs.length := by
      induction gs generalizing s with
      | nil => simp
      | cons gate gates ih =>
        rw [List.foldl_cons,ih]
        simp [EdgeOwnership.coneStep]
        omega
    have length : cs.length=C.size := by simp [cs,EdgeOwnership.cones,len,Circuit.size]
    let nodes := (g.inputs.filter fun w => decide (n≤w ∧ w<n+cs.length)).flatMap
      (fun w => (w-n)::cs.getD (w-n) [])
    have ends : EdgeOwnership.cones n D=cs++[nodes] := by
      unfold EdgeOwnership.cones
      simp only [D,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rfl
    let reach (A : Circuit) (w : ℕ) := w=n+j ∨ n≤w ∧ EdgeOwnership.InCone n A j (w-n)
    have keep {w : ℕ} : reach C w → reach D w := by
      rintro (direct | ⟨lo,h⟩)
      · exact Or.inl direct
      · change j∈cs.getD (w-n) [] at h
        have bnd : w-n<cs.length := by
          by_contra! absent
          simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none absent] at h
        refine Or.inr ⟨lo,?_⟩
        change j∈(EdgeOwnership.cones n D).getD (w-n) []
        simpa only [ends,List.getD_eq_getElem?_getD,List.getElem?_append_left bnd] using h
    have move : reach C a → reach D (n+C.size) := by
      intro h
      have lo : n≤a := h.elim (fun e => by omega) (fun t => t.1)
      refine Or.inr ⟨by omega,?_⟩
      change j∈(EdgeOwnership.cones n D).getD (n+C.size-n) []
      rw [Nat.add_sub_cancel_left,ends,←length]
      have last : (cs++[nodes]).getD cs.length []=nodes := by simp
      rw [last]
      apply List.mem_flatMap.mpr
      refine ⟨a,List.mem_filter.mpr ⟨by simp [g],?_⟩,?_⟩
      · exact decide_eq_true_iff.mpr ⟨lo,by omega⟩
      · rcases h with direct | ⟨_,oldCone⟩
        · exact List.mem_cons.mpr (Or.inl (by omega))
        · exact List.mem_cons_of_mem _ oldCone
    obtain ⟨e,he,w,hw,uses⟩ := active j early orig
    rcases List.mem_cons.mp he with first | later
    · subst e
      rcases List.mem_cons.mp hw with h | h
      · subst w
        exact ⟨(n+C.size,b),List.mem_cons_self ..,n+C.size,by simp,move uses⟩
      · have eqw : w=b := List.mem_singleton.mp h
        subst w
        exact ⟨(n+C.size,b),List.mem_cons_self ..,b,by simp,keep uses⟩
    · exact ⟨e,List.mem_cons_of_mem _ later,w,hw,keep uses⟩
  · have eq : j=C.size := by omega
    exact ⟨(n+C.size,b),List.mem_cons_self ..,n+C.size,by simp,Or.inl (by omega)⟩
