import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18344
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

def single (j w : Fin 10) : Bool := decide (w = j)

theorem pairSplit (u v : Fin 10) : Split (List.ofFn (single u)) (List.ofFn (single v))
    (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) := by
  intro i hi
  by_cases h : i < 10
  · rw [List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn]
    simpa [single, PEqualNP.EdgeOwnership.pairInput] using hi
  · rw [List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt h))] at hi
    contradiction

end PEqualNP.Outside.L_meta_18344

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_18344 in
theorem PEqualNP.Outside.L_meta_18344 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (¬∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (10 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (10 : ℕ) (x6 % (10 : ℕ))) := by
  intro C hm _ hno
  by_contra! hf
  have hor : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    have h : g.op = .and ∨ g.op = .or := by simpa using (hm g hg).1
    rcases h with ha | ho
    · obtain ⟨i, hi⟩ := List.getElem_of_mem hg
      exact (hno ⟨⟨i, hi.1⟩, by simpa [hi.2] using ha⟩).elim
    · exact ho
  have hp : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 10) 1)) = true := by
    rw [hf]; decide
  rcases foldSplit C.gates hor _ _ _ (by simp) (by simp) (pairSplit 0 1) C.output hp with ha | hb
  · change C.eval (List.ofFn (single 0)) = true at ha
    rw [hf] at ha
    exact (by decide : _ ≠ true) ha
  · change C.eval (List.ofFn (single 1)) = true at hb
    rw [hf] at hb
    exact (by decide : _ ≠ true) hb
