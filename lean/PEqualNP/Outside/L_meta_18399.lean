import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18399
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Split (a b c : List Bool) : Prop :=
  ∀ i, c.getD i false = true → a.getD i false = true ∨ b.getD i false = true

theorem foldSplit (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .or) :
    ∀ a b c : List Bool, a.length = c.length → b.length = c.length → Split a b c →
      Split (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs with
  | nil => intro a b c _ _ h; exact h
  | cons g gs ih =>
    intro a b c ha hb hs
    simp only [List.foldl_cons]
    apply ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
    · simp [step, ha]
    · simp [step, hb]
    · intro i hi
      unfold step at hi ⊢
      by_cases h : i < c.length
      · rw [List.getD_append _ _ _ _ h] at hi
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hs i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), ha, hb]
        by_cases hz : i - c.length = 0
        · rw [hz] at hi ⊢
          simp only [List.getD_cons_zero, hg g List.mem_cons_self, GateOp.eval,
            List.any_map, Function.comp_apply, id_eq, List.any_eq_true] at hi ⊢
          obtain ⟨j, hj, hv⟩ := hi
          rcases hs j hv with h' | h'
          · exact Or.inl ⟨j, hj, h'⟩
          · exact Or.inr ⟨j, hj, h'⟩
        · obtain ⟨k, hk⟩ : ∃ k, i - c.length = k + 1 := ⟨i - c.length - 1, by omega⟩
          rw [hk] at hi
          simp at hi

open PEqualNP.EdgeOwnership

theorem splitInput {n : ℕ} (u v : Fin n) :
    Split (List.ofFn fun i => decide (i = u)) (List.ofFn fun i => decide (i = v))
      (List.ofFn (pairInput u v)) := by
  intro i hi
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    simpa [pairInput] using hi
  · rw [List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt h))] at hi
    contradiction

end PEqualNP.Outside.L_meta_18399

open PEqualNP.EdgeOwnership PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_18399 in
theorem PEqualNP.Outside.L_meta_18399 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (¬∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C _ legal computes noAnd
  have onlyOr : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    rcases legal.1 g hg with ha | ho
    · obtain ⟨i, hi⟩ := List.getElem_of_mem hg
      exact (noAnd ⟨⟨i, hi.1⟩, by simpa [hi.2] using ha⟩).elim
    · exact ho
  have empty : E = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨p,l⟩ hp
    let u := Fin.castAdd m p
    let v := Fin.natAdd n l
    have accepts : PEqualNP.MetaComplexity.circuitFun (n+m) C (pairInput u v) = true := by
      rw [computes]
      exact decide_eq_true ⟨p,l,hp,by simp [pairInput,u,v],by simp [pairInput,u,v]⟩
    rcases foldSplit C.gates onlyOr _ _ _ (by simp) (by simp) (splitInput u v) C.output accepts with left | right
    · change PEqualNP.MetaComplexity.circuitFun _ C _ = true at left
      rw [computes] at left
      obtain ⟨p',l',_,_,h⟩ := of_decide_eq_true left
      have e : Fin.natAdd n l' = Fin.castAdd m p := of_decide_eq_true h
      have hv := congrArg Fin.val e
      change n + l'.val = p.val at hv
      omega
    · change PEqualNP.MetaComplexity.circuitFun _ C _ = true at right
      rw [computes] at right
      obtain ⟨p',l',_,h,_⟩ := of_decide_eq_true right
      have e : Fin.castAdd m p' = Fin.natAdd n l := of_decide_eq_true h
      have hv := congrArg Fin.val e
      change p'.val = n + l.val at hv
      omega
  subst E
  exact ⟨∅, ∅, by simp, by simp⟩
