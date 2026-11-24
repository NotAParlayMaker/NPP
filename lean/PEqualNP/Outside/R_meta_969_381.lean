import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Preseed one gate from the three input distances in the cube.
-- A suffix need only accept the edge masks and reject the maximal independent masks.
theorem PEqualNP.Outside.R_meta_969_381
    (rows : ∀ x : Fin 8 → Bool,
  let edge := ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true
  (edge → ∃ m ∈ ([3, 5, 17, 10, 34, 12, 68, 136, 48, 80, 160, 192] : List ℕ),
    ∀ i : Fin 8, m.testBit i.val = true → x i = true) ∧
  (¬ edge → ∃ m ∈ ([24, 36, 66, 105, 129, 150] : List ℕ),
    ∀ i : Fin 8, x i = true → m.testBit i.val = true))
    (search : ∃ (d : Fin 3) (useAnd : Bool) (S : Circuit),
      Monotone2 S ∧ S.size ≤ 10 ∧
      let b : Fin 8 := if d = 0 then 1 else if d = 1 then 3 else 7
      let input := fun m : ℕ =>
        let x := fun i : Fin 8 => m.testBit i.val
        List.ofFn x ++ [if useAnd then x 0 && x b else x 0 || x b]
      (∀ m ∈ ([3, 5, 17, 10, 34, 12, 68, 136, 48, 80, 160, 192] : List ℕ), S.eval (input m) = true) ∧
      (∀ m ∈ ([24, 36, 66, 105, 129, 150] : List ℕ), S.eval (input m) = false)) :
∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by

  obtain ⟨d,useAnd,S,mono,budget,accept,reject⟩ := search
  let b : Fin 8 := if d = 0 then 1 else if d = 1 then 3 else 7
  let g : Gate := ⟨if useAnd then .and else .or,[0,b.val]⟩
  let C : Circuit := ⟨g :: S.gates,S.output⟩
  let wiresStep (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have andEval (bits : List Bool) : GateOp.and.eval bits = bits.all id := rfl
  have orEval (bits : List Bool) : GateOp.or.eval bits = bits.any id := rfl
  have getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
      w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
      (w ++ [b]).getD m false = b := by
    subst hm
    simp [List.getD_eq_getElem?_getD]

  have getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
      (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    simp [List.getD_eq_getElem?_getD, hi]

  have foldMono (gs : List Gate)
      (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
      (w1 w2 : List Bool) (hlen : w1.length = w2.length)
      (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
      ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
        (gs.foldl wiresStep w2).getD k false = true := by
    induction gs generalizing w1 w2 with
    | nil => exact hle
    | cons g gs ih =>
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
        simpa using hM g List.mem_cons_self
      have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
        fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
      apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
      · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
      · intro k hk
        by_cases hlt : k < w1.length
        · have hlt2 : k < w2.length := hlen ▸ hlt
          simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
          simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
          exact hle k hk
        · by_cases heq : k = w1.length
          · subst heq
            have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
              simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
            change (w2 ++ [_]).getD w1.length false = true
            rw [getD_append_last_eq w2 _ w1.length hlen.symm]
            rcases hg with hand | hor
            · rw [hand] at hk1 ⊢
              simp only [andEval, List.all_eq_true, List.mem_map, id_eq,
                forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
              intro i hi
              exact hle i (hk1 i hi)
            · rw [hor] at hk1 ⊢
              simp only [orEval, List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
              obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
              exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
          · have hge : (wiresStep w1 g).length ≤ k := by
              simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
              omega
            rw [getD_ge_length _ k hge] at hk
            cases hk

  have gateMono : Monotone2 C := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · cases useAnd <;> simp [g]
    · exact mono h hh
  have lift (x y : Fin 8 → Bool) (le : ∀ i, x i = true → y i = true)
      (h : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
    apply foldMono C.gates (fun g hg => (gateMono g hg).1)
      (List.ofFn x) (List.ofFn y) (by simp) _ C.output h
    intro i hi
    by_cases small : i < 8
    · rw [getD_ofFn x i small] at hi
      rw [getD_ofFn y i small]
      exact le _ hi
    · rw [getD_ge_length _ _ (by simp; omega)] at hi
      cases hi
  have evalSeed (m : ℕ) :
      C.eval (List.ofFn (fun i : Fin 8 => m.testBit i.val)) =
        S.eval (List.ofFn (fun i : Fin 8 => m.testBit i.val) ++
          [if useAnd then m.testBit 0 && m.testBit b.val else m.testBit 0 || m.testBit b.val]) := by
    let x : Fin 8 → Bool := fun i => m.testBit i.val
    change (S.gates.foldl wiresStep (wiresStep (List.ofFn x) g)).getD S.output false =
      (S.gates.foldl wiresStep (List.ofFn x ++
        [if useAnd then x 0 && x b else x 0 || x b])).getD S.output false
    have readB := getD_ofFn x b.val b.isLt
    have read0 := getD_ofFn x 0 (by decide)
    have seed : wiresStep (List.ofFn x) g = List.ofFn x ++
        [if useAnd then x 0 && x b else x 0 || x b] := by
      change List.ofFn x ++ [(if useAnd then GateOp.and else .or).eval
        [(List.ofFn x).getD 0 false, (List.ofFn x).getD b.val false]] = _
      rw [read0, readB]
      cases useAnd <;> simp [andEval, orEval]
    rw [seed]
  refine ⟨C,gateMono,?_,?_⟩
  · change S.gates.length + 1 ≤ 11
    have : S.gates.length ≤ 10 := budget
    omega
  · intro x
    constructor
    · intro computes
      by_contra outside
      obtain ⟨m,hm,le⟩ := (rows x).2 outside
      have fromX := lift x (fun i => m.testBit i.val) le computes
      have r := reject m hm
      change S.eval (List.ofFn (fun i : Fin 8 => m.testBit i.val) ++
        [if useAnd then m.testBit 0 && m.testBit b.val else m.testBit 0 || m.testBit b.val]) = false at r
      rw [evalSeed, r] at fromX
      cases fromX
    · intro edge
      obtain ⟨m,hm,le⟩ := (rows x).1 edge
      apply lift (fun i => m.testBit i.val) x le
      rw [evalSeed]
      exact accept m hm
