import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18253
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

def single (j w : Fin 14) : Bool := decide (w = j)

theorem separated : ∀ p l : Fin 7, (Fin.castAdd 7 p : Fin 14) ≠ Fin.natAdd 7 l := by decide

theorem pairSplit (u v : Fin 14) : Split (List.ofFn (single u)) (List.ofFn (single v))
    (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) := by
  intro i hi
  by_cases h : i < 14
  · rw [List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn]
    simpa [single, PEqualNP.EdgeOwnership.pairInput] using hi
  · rw [List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt h))] at hi
    contradiction

end PEqualNP.Outside.L_meta_18253

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_18253 in
theorem PEqualNP.Outside.L_meta_18253 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true → ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x3 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (20 : ℕ) ≤ {x4 ∈ PEqualNP.HeptadCover.incidences PEqualNP.CircuitLowerBounds.fanoLines | x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x4.1) (Fin.natAdd (7 : ℕ) x4.2))) = Bool.true}.card → (¬∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (26 : ℕ) ≤ x1.size := by
  intro C hm sound count hno
  classical
  have hor : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    have h : g.op = .and ∨ g.op = .or := by simpa using (hm g hg).1
    rcases h with ha | ho
    · obtain ⟨i, hi⟩ := List.getElem_of_mem hg
      exact (hno ⟨⟨i, hi.1⟩, by simpa [hi.2] using ha⟩).elim
    · exact ho
  obtain ⟨⟨p, l⟩, hit⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 20) count)
  have hp := (Finset.mem_filter.mp hit).2
  rcases foldSplit C.gates hor _ _ _ (by simp) (by simp)
    (pairSplit (Fin.castAdd 7 p) (Fin.natAdd 7 l)) C.output hp with hl | hr
  · obtain ⟨_, t, _, _, ht⟩ := sound _ hl
    have he : Fin.natAdd 7 t = Fin.castAdd 7 p := by simpa [single] using ht
    exact (separated p t he.symm).elim
  · obtain ⟨s, _, _, hs, _⟩ := sound _ hr
    have he : Fin.castAdd 7 s = Fin.natAdd 7 l := by simpa [single] using hs
    exact (separated s l he).elim
