import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Five raw ORs feed three parallel ANDs, two sharing the first raw OR.
-- At size 22 the five raw pairs can be (6,9), (7,10), (5,8), (4,5), (8,10).
-- That construction uses seven further ORs before the four output terms.
-- The search asks for six, allowing all five raw pairs to change.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1342_319
    (search :
      let f := fun x : Fin 11 → Bool => ∃ u v : Fin 11,
        (([1536, 272, 1056, 192, 1280, 768, 1152, 512, 512, 0, 0] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
      ∃ (p : Fin 5 → Fin 11 × Fin 11) (s : Fin 6 → Fin 25 × Fin 25)
          (t : Fin 4 → Fin 25 × Fin 25),
        let o := fun (x : Fin 11 → Bool) (i : Fin 5) => x (p i).1 || x (p i).2
        let j := fun x => [o x 0 && o x 1, o x 0 && o x 2, o x 3 && o x 4]
        (∀ i : Fin 3, ∃ x, ¬f x ∧ (j x).getD i.val false = true) ∧
        ∀ x, let initial := List.ofFn x ++ List.ofFn (o x) ++ j x
             let w := (List.ofFn s).foldl (fun (v : List Bool) q =>
               v ++ [v.getD q.1.val false || v.getD q.2.val false]) initial
             ((List.ofFn t).any (fun q => w.getD q.1.val false && w.getD q.2.val false)) = true ↔ f x)
    (finish : ∀ (s : Fin 6 → Fin 25 × Fin 25) (t : Fin 4 → Fin 25 × Fin 25),
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 13 ∧ ∀ z : List Bool, z.length = 19 →
        let w := (List.ofFn s).foldl (fun (v : List Bool) q =>
          v ++ [v.getD q.1.val false || v.getD q.2.val false]) z
        D.eval z = (List.ofFn t).any (fun q => w.getD q.1.val false && w.getD q.2.val false)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  obtain ⟨p, s, t, _, hs⟩ := search
  obtain ⟨D, hm, hd, hD⟩ := finish s t
  let inputOr (i : Fin 5) : Gate := ⟨.or, [(p i).1.val, (p i).2.val]⟩
  let first : List Gate := [inputOr 0, inputOr 1, inputOr 2, inputOr 3, inputOr 4]
  let marks : List Gate := [⟨.and, [11, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [14, 15]⟩]
  let C : Circuit := ⟨first ++ marks ++ D.gates, D.output⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ first ++ marks ++ D.gates at hg
    rcases List.mem_append.mp hg with h | h
    · simp only [first, marks, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [inputOr]
    · exact hm g h
  · intro x
    let o (i : Fin 5) := x (p i).1 || x (p i).2
    let j := [o 0 && o 1, o 0 && o 2, o 3 && o 4]
    let start := List.ofFn x ++ List.ofFn o ++ j
    have length : start.length = 19 := by simp [start, j]
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have evalOr (a b : Bool) : GateOp.eval .or [a, b] = (a || b) := by
      cases a <;> cases b <;> rfl
    have evalAnd (a b : Bool) : GateOp.eval .and [a, b] = (a && b) := by
      cases a <;> cases b <;> rfl
    have readRaw (r : List Bool) (i : Fin 11) :
        (List.ofFn x ++ r).getD i.val false = x i := by
      rw [List.getD_append _ _ _ _ (by simp)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp
    have nextOr (r : List Bool) (i : Fin 5) :
        step (List.ofFn x ++ r) (inputOr i) = List.ofFn x ++ (r ++ [o i]) := by
      simp only [step, inputOr, o, List.map_cons, List.map_nil, evalOr, readRaw, List.append_assoc]
    have bank : first.foldl step (List.ofFn x) = List.ofFn x ++ List.ofFn o := by
      change first.foldl step (List.ofFn x ++ []) = _
      simp only [first, List.foldl_cons, List.foldl_nil, nextOr, List.nil_append,
        List.cons_append]
      rfl
    have initial : (first ++ marks).foldl step (List.ofFn x) = start := by
      rw [List.foldl_append, bank]
      have xs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10] := by
        simp [List.ofFn_succ]
      dsimp only [start]
      have os : List.ofFn o = [o 0, o 1, o 2, o 3, o 4] := by simp [List.ofFn_succ]
      rw [xs, os]
      simp only [marks, step, j, List.foldl_cons, List.foldl_nil, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, evalAnd, List.getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some]
    have eqEval : C.eval (List.ofFn x) = D.eval start := by
      change (((first ++ marks) ++ D.gates).foldl step (List.ofFn x)).getD D.output false = _
      rw [List.foldl_append, initial]
      rfl
    have table : ∀ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ↔
        (([1536, 272, 1056, 192, 1280, 768, 1152, 512, 512, 0, 0] : List ℕ).getD u.val 0).testBit v.val = true := by decide +kernel
    rw [eqEval, hD start length]
    simpa only [table] using hs x
  · change (first ++ marks ++ D.gates).length ≤ 21
    have count : D.gates.length ≤ 13 := hd
    simp only [List.length_append]
    change 8 + D.gates.length ≤ 21
    omega
