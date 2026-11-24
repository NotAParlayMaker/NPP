import PEqualNP.Defs

set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.R_meta_3178_1
    (hAdjacent : ∀ (k : Fin (9 : ℕ)) (C : PEqualNP.CircuitLowerBounds.Circuit), (k = (1 : Fin (9 : ℕ)) ∨ k = (4 : Fin (9 : ℕ)) ∨ k = (5 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (13 : ℕ) → ∃ (x : Fin (9 : ℕ) → Bool), C.eval ((List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) ++ [x (0 : Fin (9 : ℕ)) || x k]) ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (hOther : ∀ (k : Fin (9 : ℕ)) (C : PEqualNP.CircuitLowerBounds.Circuit), 0 < (k : ℕ) ∧ (k : ℕ) < (9 : ℕ) → ¬(k = (1 : Fin (9 : ℕ)) ∨ k = (4 : Fin (9 : ℕ)) ∨ k = (5 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (13 : ℕ) → ∃ (x : Fin (9 : ℕ) → Bool), C.eval ((List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]) ++ [x (0 : Fin (9 : ℕ)) || x k]) ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (0 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  classical
  intro xs hlen hlt hmem hpair C hfan hsize
  obtain ⟨hnotAll,hzero⟩ := hpair
  obtain ⟨a,b,hxs⟩ : ∃ a b : ℕ, xs = [a,b] := by
    cases xs with
    | nil => simp at hlen
    | cons a rest =>
      cases rest with
      | nil => simp at hlen
      | cons b tail =>
        cases tail with
        | nil => exact ⟨a,b,rfl⟩
        | cons c tail' => simp at hlen
  rw [hxs] at hlt hnotAll hzero
  have hzero' : 0 = a ∨ 0 = b := by simpa using hzero
  obtain ⟨k,hkpos,hk9,hform⟩ :
      ∃ k : ℕ, 0 < k ∧ k < 9 ∧ (xs = [0,k] ∨ xs = [k,0]) := by
    rcases hzero' with ha | hb
    · subst a
      have hother : ¬(b = 0 ∨ b = 9) := by
        intro hb09
        apply hnotAll
        intro i hi
        simp at hi
        rcases hi with rfl | rfl
        · exact Or.inl rfl
        · exact hb09
      have hblt : b < 10 := hlt b (by simp)
      refine ⟨b, by omega, by omega, Or.inl ?_⟩
      exact hxs
    · subst b
      have hother : ¬(a = 0 ∨ a = 9) := by
        intro ha09
        apply hnotAll
        intro i hi
        simp at hi
        rcases hi with rfl | rfl
        · exact ha09
        · exact Or.inl rfl
      have halt : a < 10 := hlt a (by simp)
      refine ⟨a, by omega, by omega, Or.inr ?_⟩
      exact hxs
  let j : Fin 9 := ⟨k,hk9⟩
  have hj : (j : ℕ) = k := rfl
  have hb : 0 < (j : ℕ) ∧ (j : ℕ) < 9 := ⟨hkpos,hk9⟩
  let near : Prop := j = (1 : Fin 9) ∨ j = (4 : Fin 9) ∨ j = (5 : Fin 9)
  have hget0 (x : Fin 9 → Bool) :
      (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := by
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hgetj (x : Fin 9 → Bool) :
      (List.ofFn x ++ [!x 0]).getD k false = x j := by
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [dif_pos hk9, Option.getD_some]
    rfl
  have heval (x : Fin 9 → Bool) :
      PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (xs.map fun i => (List.ofFn x ++ [!x 0]).getD i false) = (x 0 || x j) := by
    change (xs.map fun i => (List.ofFn x ++ [!x 0]).getD i false).any id = (x 0 || x j)
    rcases hform with hxs | hxs
    · simp only [hxs, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, hget0, hgetj]
      simp
    · simp only [hxs, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, hget0, hgetj, Bool.or_comm]
      simp
  by_cases hn : near
  · obtain ⟨x,hx⟩ := hAdjacent j C hn hfan hsize
    refine ⟨x,?_⟩
    simpa only [heval] using hx
  · obtain ⟨x,hx⟩ := hOther j C hb hn hfan hsize
    refine ⟨x,?_⟩
    simpa only [heval] using hx
