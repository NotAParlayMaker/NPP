import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1793_1
    (halias :
    let base := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 && x 1]
    let target := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ a : ℕ,
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval (base x ++ [(base x).getD a false]) ≠ target x)
    (hraw :
    let base := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 && x 1]
    let target := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ u v : Fin 9, u < v →
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval (base x ++ [x u || x v]) ≠ target x)
    (hmixed :
    let base := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 && x 1]
    let target := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    ∀ i : Fin 9, 2 ≤ i.val →
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval (base x ++ [(x 0 && x 1) || x i]) ≠ target x) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins hlen C hfan hsize
  let base := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 && x 1]
  let target := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let wire := fun (x : Fin 9 → Bool) (i : ℕ) => (base x).getD i false
  let goal := fun fn : (Fin 9 → Bool) → Bool =>
    ∃ x : Fin 9 → Bool, C.eval (base x ++ [fn x]) ≠ target x
  change goal (fun x => PEqualNP.CircuitLowerBounds.GateOp.or.eval (pins.map (wire x)))
  have transfer {left right : (Fin 9 → Bool) → Bool}
      (h : ∀ x, left x = right x) (hr : goal right) : goal left := by
    obtain ⟨x, hx⟩ := hr
    exact ⟨x, by simpa only [h x] using hx⟩
  have aliasGoal (i : ℕ) : goal (fun x => wire x i) := halias i C hfan hsize
  have rawWire (x : Fin 9 → Bool) (i : Fin 9) : wire x i.val = x i := by
    change ((List.ofFn x) ++ [x 0 && x 1]).getD i.val false = x i
    rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
    have hindex : i.val < (List.ofFn x).length := by simpa using i.isLt
    rw [List.getD_eq_getElem _ _ hindex, List.getElem_ofFn]
  have forcedWire (x : Fin 9 → Bool) : wire x 9 = (x 0 && x 1) := by
    change ((List.ofFn x) ++ [x 0 && x 1]).getD 9 false = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have missingWire (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) : wire x i = false := by
    exact List.getD_eq_default _ _ (by simpa [base] using hi)
  have mixedGoal (i : Fin 9) : goal (fun x => (x 0 && x 1) || x i) := by
    by_cases h0 : i = 0
    · subst i
      apply transfer ?_ (aliasGoal 0)
      intro x
      have hw : wire x 0 = x 0 := rawWire x (0 : Fin 9)
      rw [hw]
      cases hx : x 0 <;> simp [hx]
    by_cases h1 : i = 1
    · subst i
      apply transfer ?_ (aliasGoal 1)
      intro x
      have hw : wire x 1 = x 1 := rawWire x (1 : Fin 9)
      rw [hw]
      cases hx : x 1 <;> simp [hx]
    have h2 : 2 ≤ i.val := by
      by_contra! h
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      rcases hi with hi | hi
      · exact h0 (Fin.ext hi)
      · exact h1 (Fin.ext hi)
    exact hmixed i h2 C hfan hsize
  have pairGoal (a b : ℕ) : goal (fun x => wire x a || wire x b) := by
    by_cases ha : 10 ≤ a
    · exact transfer (fun x => by rw [missingWire x a ha] <;> rfl) (aliasGoal b)
    by_cases hb : 10 ≤ b
    · exact transfer (fun x => by simp [missingWire x b hb]) (aliasGoal a)
    by_cases hab : a = b
    · subst b
      exact transfer (fun x => by simp) (aliasGoal a)
    by_cases ha9 : a = 9
    · subst a
      let j : Fin 9 := ⟨b, by omega⟩
      exact transfer (fun x => by rw [forcedWire x, ← rawWire x j] <;> rfl) (mixedGoal j)
    by_cases hb9 : b = 9
    · subst b
      let i : Fin 9 := ⟨a, by omega⟩
      exact transfer
        (fun x => by rw [forcedWire x, ← rawWire x i]; exact Bool.or_comm _ _) (mixedGoal i)
    let i : Fin 9 := ⟨a, by omega⟩
    let j : Fin 9 := ⟨b, by omega⟩
    by_cases hlt : a < b
    · have hij : i < j := hlt
      exact transfer (fun x => by rw [← rawWire x i, ← rawWire x j])
        (hraw i j hij C hfan hsize)
    · have hji : j < i := by
        change b < a
        omega
      exact transfer (fun x => by rw [← rawWire x i, ← rawWire x j, Bool.or_comm])
        (hraw j i hji C hfan hsize)
  rcases pins with _ | ⟨a, pins⟩
  · exact transfer (fun x => (missingWire x 10 (by decide)).symm) (aliasGoal 10)
  rcases pins with _ | ⟨b, pins⟩
  · apply transfer ?_ (aliasGoal a)
    intro x
    change (wire x a || false) = wire x a
    simp
  have hpins : pins = [] := by
    cases pins <;> simp_all
  subst pins
  apply transfer ?_ (pairGoal a b)
  intro x
  change (wire x a || (wire x b || false)) = (wire x a || wire x b)
  simp
