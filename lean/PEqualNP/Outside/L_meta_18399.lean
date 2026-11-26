import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18399_aux

open PEqualNP.CircuitLowerBounds

private def run (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem go (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .or)
    (s a b : List Bool) (ha : a.length = s.length) (hb : b.length = s.length)
    (h : ∀ i, s.getD i false = (a.getD i false || b.getD i false)) (i : ℕ) :
    (gs.foldl run s).getD i false = ((gs.foldl run a).getD i false || (gs.foldl run b).getD i false) := by
  induction gs generalizing s a b with
  | nil => exact h i
  | cons g gs ih =>
    apply ih (fun t ht => hg t (by simp [ht])) (run s g) (run a g) (run b g) (by simp [run,ha]) (by simp [run,hb])
    intro j
    by_cases hj : j < s.length
    · simpa only [run,List.getD_eq_getElem?_getD,List.getElem?_append_left hj,List.getElem?_append_left (show j < a.length by omega),List.getElem?_append_left (show j < b.length by omega)] using h j
    by_cases he : j = s.length
    · subst j
      have hop := hg g (by simp)
      simp only [run,hop,GateOp.eval,List.any_map,Function.comp_def,List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),List.getElem?_append_right (show a.length ≤ s.length by omega),List.getElem?_append_right (show b.length ≤ s.length by omega),ha,hb,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true,Bool.or_eq_true]
      constructor
      · rintro ⟨k,hk,hv⟩
        change s.getD k false = true at hv
        rw [h,Bool.or_eq_true] at hv
        rcases hv with hv|hv
        · exact Or.inl ⟨k,hk,hv⟩
        · exact Or.inr ⟨k,hk,hv⟩
      · rintro (⟨k,hk,hv⟩|⟨k,hk,hv⟩)
        · exact ⟨k,hk,(h k).trans (by change (_ || _) = true; rw [show a.getD k false = true from hv]; rfl)⟩
        · exact ⟨k,hk,(h k).trans (by rw [show b.getD k false = true from hv]; simp)⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (show (run s g).length ≤ j by simp [run]; omega),List.getElem?_eq_none (show (run a g).length ≤ j by simp [run]; omega),List.getElem?_eq_none (show (run b g).length ≤ j by simp [run]; omega)]

private theorem orCase : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (¬ (∃ (j : Fin x4.gates.length), (x4.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), (∀ x10 ∈ x3, x10.1 ∈ x8 ∨ x10.2 ∈ x9) ∧ x3.card + x8.card + x9.card ≤ x4.size + (1 : ℕ) := by

  intro n m E C rect ao correct none
  have ors (g) (hg : g ∈ C.gates) : g.op = GateOp.or := by
    apply (ao.1 _ hg).resolve_left
    intro e
    obtain ⟨j,hj,he⟩ := List.getElem_of_mem hg
    exact none ⟨⟨j,hj⟩,by simpa [he] using e⟩
  have empty : E = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨a,b⟩ hmem
    let l : Fin (n+m) → Bool := fun z => decide (z = Fin.castAdd m a)
    let r : Fin (n+m) → Bool := fun z => decide (z = Fin.natAdd n b)
    let lr : Fin (n+m) → Bool := fun z => l z || r z
    have low (i : Fin n) (j : Fin m) : Fin.castAdd m i ≠ Fin.natAdd n j := by
      intro he
      have := congrArg Fin.val he
      change i.val = n+j.val at this
      omega
    have h0 : PEqualNP.MetaComplexity.circuitFun (n+m) C l = false := by simp [correct,l,Ne.symm (low _ _)]
    have h1 : PEqualNP.MetaComplexity.circuitFun (n+m) C r = false := by simp [correct,r,low]
    have h2 : PEqualNP.MetaComplexity.circuitFun (n+m) C lr = true := by
      rw [correct,decide_eq_true_eq]
      exact ⟨a,b,hmem,by simp [lr,l],by simp [lr,r]⟩
    have he := go C.gates ors (List.ofFn lr) (List.ofFn l) (List.ofFn r) (by simp) (by simp) (fun i => by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
      by_cases h : i < n+m <;> simp [h,lr]) C.output
    change PEqualNP.MetaComplexity.circuitFun (n+m) C lr = (PEqualNP.MetaComplexity.circuitFun (n+m) C l || PEqualNP.MetaComplexity.circuitFun (n+m) C r) at he
    simp [h0,h1,h2] at he
  subst E
  exact ⟨∅,∅,by simp,by simp⟩

end PEqualNP.Outside.L_meta_18399_aux

open PEqualNP.Outside.L_meta_18399_aux in
theorem PEqualNP.Outside.L_meta_18399 : (∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (¬∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ)) := orCase
