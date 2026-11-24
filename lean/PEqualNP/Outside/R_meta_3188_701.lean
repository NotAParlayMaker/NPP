import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_3188_701
    (complete : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      (∀ r ∈ rows, r < 2^n) → Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      FormulaSat (enc n s g rows))
    (impossible :
      let p : List ℕ := [515, 518, 524, 24, 529, 545, 66, 644, 264, 160, 320, 288]
      let n : List ℕ := [42, 50, 581, 104, 628, 138, 713, 208, 773, 788, 897, 402]
      ¬ FormulaSat (enc 10 14 (fun r => p.contains r) (p ++ n))) :
  have x1 : Fin (9 : ℕ) → BitVec (24 : ℕ) := fun (x1 : Fin (9 : ℕ)) =>   have x2 : ℕ × ℕ := [((49 : ℕ), (1348 : ℕ)), ((67 : ℕ), (2083 : ℕ)), ((134 : ℕ), (788 : ℕ)), ((268 : ℕ), (105 : ℕ)), ((24 : ℕ), (2706 : ℕ)), ((2592 : ℕ), (27 : ℕ)), ((1088 : ℕ), (220 : ℕ)), ((640 : ℕ), (3296 : ℕ)), ((3328 : ℕ), (3840 : ℕ))].getD ↑x1 ((0 : ℕ), (0 : ℕ));   BitVec.ofNat (24 : ℕ) ((4096 : ℕ) * x2.1 + x2.2); have x2 : List (BitVec (24 : ℕ)) := List.ofFn x1 ++ [x1 (0 : Fin (9 : ℕ)) ||| x1 (2 : Fin (9 : ℕ))]; ∀ (x3 : List (BitVec (24 : ℕ))),   BitVec.ofNat (24 : ℕ) ((4095 : ℕ) * (4096 : ℕ)) ∈ x2 ++ x3 →     (∀ (x5 : Fin x3.length),         have x6 : List (BitVec (24 : ℕ)) := x2 ++ List.take (↑x5) x3;         x3.get x5 ∉ x6 ∧ x3.get x5 ≠ (0 : BitVec (24 : ℕ)) ∧ x3.get x5 ≠ (-1 : BitVec (24 : ℕ)) ∧ ∃ x7 ∈ x6, ∃ x8 ∈ x6, x3.get x5 = x7 &&& x8 ∨ x3.get x5 = x7 ||| x8) →       (15 : ℕ) ≤ x3.length := by
  let col (i : Fin 9) : BitVec 24 :=
    let pair := ([(49,1348),(67,2083),(134,788),(268,105),(24,2706),(2592,27),(1088,220),(640,3296),(3328,3840)] : List (ℕ × ℕ)).getD i.val (0,0)
    BitVec.ofNat 24 (4096 * pair.1 + pair.2)
  let raw := List.ofFn col ++ [col 0 ||| col 2]
  let target := BitVec.ofNat 24 (4095 * 4096)

  change ∀ seq : List (BitVec 24),
    target ∈ raw ++ seq →
      (∀ j : Fin seq.length,
        let old := raw ++ seq.take j.val
        seq.get j ∉ old ∧ seq.get j ≠ 0 ∧ seq.get j ≠ -1 ∧
          ∃ a ∈ old, ∃ b ∈ old, seq.get j = a &&& b ∨ seq.get j = a ||| b) →
      15 ≤ seq.length
  intro seq last ops
  by_contra! small
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let val (r : ℕ) (s : BitVec 24) := s.getLsbD r
  let shape (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  have extract (xs ys : List (BitVec 24))
      (h : ∀ j : Fin ys.length, ∃ a ∈ xs ++ ys.take j.val, ∃ b ∈ xs ++ ys.take j.val,
        ys.get j = a &&& b ∨ ys.get j = a ||| b) :
      ∃ gs : List Gate, gs.length = ys.length ∧ (∀ g ∈ gs, shape g) ∧
        ∀ r : ℕ, gs.foldl step (xs.map (val r)) = (xs ++ ys).map (val r) := by
    induction ys generalizing xs with
    | nil => exact ⟨[], rfl, by simp, by simp⟩
    | cons y ys ih =>
      have hhead : ∃ a ∈ xs, ∃ b ∈ xs, y = a &&& b ∨ y = a ||| b := by
        simpa using h ⟨0, by simp⟩
      obtain ⟨a, ha, b, hb, hgate⟩ := hhead
      obtain ⟨i, hi, ea⟩ := List.mem_iff_getElem.mp ha
      obtain ⟨j, hj, eb⟩ := List.mem_iff_getElem.mp hb
      have sub (r k : ℕ) (hk : k < xs.length) :
          (xs.map (val r)).getD k false = val r xs[k] := by
        rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_map]
      have one : ∃ g : Gate, shape g ∧
          ∀ r, step (xs.map (val r)) g = (xs ++ [y]).map (val r) := by
        rcases hgate with eq | eq
        · refine ⟨⟨.and,[i,j]⟩, by simp [shape], fun r => ?_⟩
          simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, List.map_append]
          rw [sub r i hi, sub r j hj, ea, eb]
          simp [val, eq]
        · refine ⟨⟨.or,[i,j]⟩, by simp [shape], fun r => ?_⟩
          simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, List.map_append]
          rw [sub r i hi, sub r j hj, ea, eb]
          simp [val, eq]
      obtain ⟨g, hg, same⟩ := one
      have tail : ∀ k : Fin ys.length, ∃ a ∈ (xs ++ [y]) ++ ys.take k.val,
          ∃ b ∈ (xs ++ [y]) ++ ys.take k.val,
            ys.get k = a &&& b ∨ ys.get k = a ||| b := by
        intro k
        simpa [List.append_assoc] using h k.succ
      obtain ⟨gs, hs, hgs, run⟩ := ih (xs ++ [y]) tail
      refine ⟨g :: gs, by simp [hs], ?_, fun r => ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hg
        · exact hgs _ hu
      · rw [List.foldl_cons, same, run]
        simp [List.append_assoc]
  obtain ⟨gs, len, wf, rows⟩ := extract raw seq (fun j => (ops j).2.2.2)
  obtain ⟨i, hi, hit⟩ := List.mem_iff_getElem.mp last
  let C : Circuit := ⟨gs,i⟩
  have mono : Monotone2 C := fun g hg => wf g hg
  have eval (j : ℕ) : C.eval (raw.map (val j)) = val j target := by
    change (gs.foldl step (raw.map (val j))).getD i false = _
    rw [rows, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, hit]
  let p : List ℕ := [515, 518, 524, 24, 529, 545, 66, 644, 264, 160, 320, 288]
  let n : List ℕ := [42, 50, 581, 104, 628, 138, 713, 208, 773, 788, 897, 402]
  let all := n ++ p
  let entry (j : Fin 24) := all.getD j.val 0
  have cert : ∀ j : Fin 24,
      (List.ofFn fun k : Fin 10 => (entry j).testBit k.val) = raw.map (val j.val) ∧
      p.contains (entry j) = val j.val target := by
    decide +kernel
  have count : all.length = 24 := by decide
  have bound : ∀ r ∈ p ++ n, r < 2^10 := by
    intro r hr
    exact of_decide_eq_true (List.all_eq_true.mp
      (show (p ++ n).all (fun m => decide (m < 2^10)) = true from by decide +kernel) r hr)
  apply impossible
  apply complete 10 14 (fun r => p.contains r) (p ++ n) C bound mono
  · change gs.length ≤ 14
    omega
  · intro r hr
    have mem : r ∈ all := by simpa only [all, List.mem_append, or_comm] using hr
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp mem
    let k : Fin 24 := ⟨j, by simpa only [count] using hj⟩
    have idx : entry k = r := by
      change all.getD j 0 = r
      rw [List.getD_eq_getElem _ _ hj, eq]
    obtain ⟨e,u⟩ := cert k
    rw [← idx, e, u]
    exact eval k.val
