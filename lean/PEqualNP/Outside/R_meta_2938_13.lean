import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 2048 in
theorem PEqualNP.Outside.R_meta_2938_13
    (baseline : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (15 : ℕ) ≤ x1.size)
    (install :
      let first (x : Fin 9 → Bool) := x 0 && x 2
      let raw (x : Fin 9 → Bool) := List.ofFn x ++ [first x]
      let s (pins : List (Fin 11)) (x : Fin 9 → Bool) :=
        GateOp.or.eval (pins.map fun i => (raw x).getD i.val false)
      ∀ (pins : List (Fin 11)) (C : Circuit), pins.length = 2 → FanInTwo C →
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size + 2 ∧
          ((∃ k : Fin 11, ∀ x : Fin 9 → Bool,
            s pins x = (List.ofFn x ++ [false, first x]).getD k.val false) →
            D.size ≤ C.size + 1) ∧
          ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) =
            C.eval (raw x ++ [s pins x]))
    (mixed :
      let graph (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (i : Fin 9), i ≠ 0 → i ≠ 2 →
        ∀ C : Circuit, FanInTwo C → C.size = 13 →
          ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2] ++
            [x i || (x 0 && x 2)]) ≠ graph x)
    (pure :
      let graph (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (i j : Fin 9), i < j → ∀ C : Circuit, FanInTwo C → C.size = 13 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2] ++ [x i || x j]) ≠ graph x) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length = (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins two C hC hsize
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp two
  by_contra! computes
  dsimp only at computes
  push Not at computes
  let graph (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let first (x : Fin 9 → Bool) := x 0 && x 2
  let w (x : Fin 9 → Bool) := List.ofFn x ++ [first x]
  let padded (x : Fin 9 → Bool) := List.ofFn x ++ [false, first x]
  let second (x : Fin 9 → Bool) := GateOp.or.eval ([a,b].map fun i => (w x).getD i.val false)
  change ∀ x, C.eval (w x ++ [second x]) = graph x at computes
  obtain ⟨D, hD, hcost, short, heval⟩ := install [a, b] C rfl hC
  have need := baseline D hD (fun x => (heval x).trans (computes x))
  have tight : C.size = 13 := by omega
  have noAlias : ¬ (∃ k : Fin 11, ∀ x : Fin 9 → Bool,
      second x = (padded x).getD k.val false) := by
    intro uses
    have upper := short uses
    omega
  have wRaw (x : Fin 9 → Bool) (j : Fin 9) : (w x).getD j.val false = x j := by
    have h : j.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using j.isLt
    change (List.ofFn x ++ [first x]).getD j.val false = x j
    rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h, List.getElem_ofFn]
  have pRaw (x : Fin 9 → Bool) (j : Fin 9) :
      (padded x).getD (Fin.castAdd 2 j).val false = x j := by
    have h : j.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using j.isLt
    change (List.ofFn x ++ [false, first x]).getD j.val false = x j
    rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h, List.getElem_ofFn]
  have wFirst (x : Fin 9 → Bool) : (w x).getD 9 false = first x := by simp [w]
  have wEnd (x : Fin 9 → Bool) : (w x).getD 10 false = false := by simp [w]
  have pFirst (x : Fin 9 → Bool) : (padded x).getD 10 false = first x := by simp [padded]
  have pFalse (x : Fin 9 → Bool) : (padded x).getD 9 false = false := by simp [padded]
  have single (i : Fin 11) :
      ∃ k : Fin 11, ∀ x : Fin 9 → Bool, (w x).getD i.val false = (padded x).getD k.val false := by
    have hbound := i.isLt
    by_cases h : i.val < 9
    · let j : Fin 9 := ⟨i.val, h⟩
      exact ⟨Fin.castAdd 2 j, fun x => (wRaw x j).trans (pRaw x j).symm⟩
    by_cases h9 : i.val = 9
    · refine ⟨10, fun x => ?_⟩
      change (w x).getD i.val false = (padded x).getD 10 false
      rw [h9, wFirst, pFirst]
    have h10 : i.val = 10 := by omega
    refine ⟨9, fun x => ?_⟩
    change (w x).getD i.val false = (padded x).getD 9 false
    rw [h10, wEnd, pFalse]
  have value (x : Fin 9 → Bool) :
      second x = ((w x).getD a.val false || (w x).getD b.val false) := by
    change [(w x).getD a.val false, (w x).getD b.val false].any id = _
    simp only [List.any_cons, List.any_nil, id, Bool.or_false]
  have acap := a.isLt
  have bcap := b.isLt
  by_cases ha10 : a.val = 10
  · obtain ⟨k, hk⟩ := single b
    exact noAlias ⟨k, fun x => by rw [value, ha10, wEnd, Bool.false_or, hk x]⟩
  by_cases hb10 : b.val = 10
  · obtain ⟨k, hk⟩ := single a
    exact noAlias ⟨k, fun x => by rw [value, hb10, wEnd, Bool.or_false, hk x]⟩
  by_cases repeatPin : a = b
  · obtain ⟨k, hk⟩ := single a
    exact noAlias ⟨k, fun x => by rw [value, ← repeatPin, Bool.or_self, hk x]⟩
  have different : a.val ≠ b.val := fun eq => repeatPin (Fin.ext eq)
  have excludeMixed (j : Fin 9) (form : ∀ x : Fin 9 → Bool, second x = (x j || first x)) :
      False := by
    by_cases zero : j = 0
    · subst j
      refine noAlias ⟨Fin.castAdd 2 (0 : Fin 9), fun x => ?_⟩
      rw [form, pRaw]
      cases h : x 0 <;> simp [first, h]
    by_cases two : j = 2
    · subst j
      refine noAlias ⟨Fin.castAdd 2 (2 : Fin 9), fun x => ?_⟩
      rw [form, pRaw]
      cases h : x 2 <;> simp [first, h]
    obtain ⟨x, bad⟩ := mixed j zero two C hC tight
    exact bad (by simpa only [form x] using computes x)
  by_cases ha9 : a.val = 9
  · let j : Fin 9 := ⟨b.val, by omega⟩
    apply excludeMixed j
    intro x
    have hm : (w x).getD b.val false = x j := wRaw x j
    rw [value, ha9, wFirst, hm, Bool.or_comm]
  by_cases hb9 : b.val = 9
  · let i : Fin 9 := ⟨a.val, by omega⟩
    apply excludeMixed i
    intro x
    have hm : (w x).getD a.val false = x i := wRaw x i
    rw [value, hb9, wFirst, hm]
  let i : Fin 9 := ⟨a.val, by omega⟩
  let j : Fin 9 := ⟨b.val, by omega⟩
  have distinct : i ≠ j := by
    intro eq
    have eqv : i.val = j.val := congrArg Fin.val eq
    exact different eqv
  have values (x : Fin 9 → Bool) : second x = (x i || x j) :=
    (value x).trans (congrArg₂ (· || ·) (wRaw x i) (wRaw x j))
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · obtain ⟨x, bad⟩ := pure i j ordered C hC tight
    exact bad (by simpa only [values x] using computes x)
  · obtain ⟨x, bad⟩ := pure j i ordered C hC tight
    have reverseValue : second x = (x j || x i) := (values x).trans (Bool.or_comm _ _)
    exact bad (by simpa only [reverseValue] using computes x)
