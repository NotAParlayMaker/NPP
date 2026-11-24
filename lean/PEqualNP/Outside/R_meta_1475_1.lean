import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1475_1
  (hlocal : let ends : Fin 15 → Fin 6 × Fin 6 := ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 34 ∧
      C.output < 21 + C.size ∧ ∀ x : Fin 21 → Bool,
        C.eval (List.ofFn x) = true ↔ ∃ k : Fin 15,
          x (Fin.castAdd 6 k) = true ∧
          (x (Fin.natAdd 15 (ends k).1) = true ∨ x (Fin.natAdd 15 (ends k).2) = true))
  (hor : ∀ (n m N : ℕ) (C D : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 D →
    C.output < n + C.size → D.output < m + D.size →
    ∀ (f : Fin n → Fin N) (g : Fin m → Fin N),
    ∃ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 E ∧ E.size ≤ C.size + D.size + 1 ∧
      ∀ x : Fin N → Bool, E.eval (List.ofFn x) =
        (C.eval (List.ofFn (fun i => x (f i))) || D.eval (List.ofFn (fun i => x (g i))))) :
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  have eval_and (l : List Bool) :
      PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.and l = l.all id := rfl
  have eval_or (l : List Bool) :
      PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or l = l.any id := rfl
  have block_def (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
      PEqualNP.MetaComplexity.blockGates B a t v1 rest lead =
      (List.range rest.length).map (fun i =>
        (⟨PEqualNP.CircuitLowerBounds.GateOp.or,
          [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0,
           rest.getD i 0]⟩ : PEqualNP.CircuitLowerBounds.Gate)) ++
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and,
        [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩ ::
      (if lead then [] else [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, B + rest.length]⟩]) := rfl
  have cover_nil (B : ℕ) (lead : Bool) (a : ℕ) :
      PEqualNP.MetaComplexity.coverGatesB B lead a [] = [] := rfl
  have cover_empty (B : ℕ) (lead : Bool) (a t : ℕ) (os : List (ℕ × List ℕ)) :
      PEqualNP.MetaComplexity.coverGatesB B lead a ((t, []) :: os) =
        PEqualNP.MetaComplexity.coverGatesB B lead a os := rfl
  have cover_cons (B : ℕ) (lead : Bool) (a t v1 : ℕ) (rest : List ℕ)
      (os : List (ℕ × List ℕ)) :
      PEqualNP.MetaComplexity.coverGatesB B lead a ((t, v1 :: rest) :: os) =
      PEqualNP.MetaComplexity.blockGates B a t v1 rest lead ++
      PEqualNP.MetaComplexity.coverGatesB
        (B + (PEqualNP.MetaComplexity.blockGates B a t v1 rest lead).length) false
        (B + (PEqualNP.MetaComplexity.blockGates B a t v1 rest lead).length - 1) os := rfl
  let ends : Fin 15 → Fin 6 × Fin 6 := ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]
  let point : Fin 15 → Fin 21 := ![1, 16, 4, 0, 14, 2, 17, 5, 15, 3, 6, 18, 19, 7, 9]
  let line : Fin 6 → Fin 21 := ![0, 1, 2, 3, 5, 14]
  let f : Fin 21 → Fin 42 := fun z => Fin.addCases (motive := fun _ => Fin 42)
    (fun k : Fin 15 => Fin.castAdd 21 (point k))
    (fun i : Fin 6 => Fin.natAdd 21 (line i)) z
  let own : List (ℕ × List ℕ) := [(25, [4, 5, 8, 18, 20]), (27, [1, 6, 7, 10, 20]), (28, [0, 2, 7, 8, 11]), (29, [1, 3, 8, 9, 12]), (30, [2, 4, 9, 10, 13]), (31, [3, 5, 10, 11, 14]), (32, [4, 6, 11, 12, 15]), (33, [5, 7, 12, 13, 16]), (34, [6, 8, 13, 14, 17]), (36, [8, 10, 15, 16, 19]), (37, [9, 11, 16, 17, 20]), (38, [0, 10, 12, 17, 18]), (39, [1, 11, 13, 18, 19]), (40, [2, 12, 14, 19, 20]), (41, [0, 3, 13, 15, 20])]
  let edges : List (ℕ × ℕ) := [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]
  let localEdges : List (ℕ × ℕ) :=
    (List.ofFn fun k : Fin 15 =>
      [((f (Fin.castAdd 6 k)).val, (f (Fin.natAdd 15 (ends k).1)).val),
       ((f (Fin.castAdd 6 k)).val, (f (Fin.natAdd 15 (ends k).2)).val)]).flatten
  let otherEdges : List (ℕ × ℕ) := own.flatMap fun p => p.2.map fun w => (w, p.1)
  have hcover : edges.toFinset = localEdges.toFinset ∪ otherEdges.toFinset := by
    set_option maxRecDepth 100000 in
      decide +kernel
  have hsplit (u v : Fin 42) : (u.val, v.val) ∈ edges ↔
      (∃ k : Fin 15,
        (u.val, v.val) = ((f (Fin.castAdd 6 k)).val, (f (Fin.natAdd 15 (ends k).1)).val) ∨
        (u.val, v.val) = ((f (Fin.castAdd 6 k)).val, (f (Fin.natAdd 15 (ends k).2)).val)) ∨
      (∃ p ∈ own, ∃ w ∈ p.2, (u.val, v.val) = (w, p.1)) := by
    have hmem : (u.val, v.val) ∈ edges.toFinset ↔
        (u.val, v.val) ∈ localEdges.toFinset ∪ otherEdges.toFinset := by rw [hcover]
    have hm : (u.val, v.val) ∈ edges ↔
        (u.val, v.val) ∈ localEdges ∨ (u.val, v.val) ∈ otherEdges := by
      simpa only [List.mem_toFinset, Finset.mem_union] using hmem
    apply hm.trans
    apply or_congr
    · change (u.val, v.val) ∈ (List.ofFn fun k : Fin 15 =>
        [((f (Fin.castAdd 6 k)).val, (f (Fin.natAdd 15 (ends k).1)).val),
         ((f (Fin.castAdd 6 k)).val, (f (Fin.natAdd 15 (ends k).2)).val)]).flatten ↔ _
      rw [List.mem_flatten]
      constructor
      · rintro ⟨l, hl, hz⟩
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hl
        exact ⟨k, by simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hz⟩
      · rintro ⟨k, hk⟩
        refine ⟨_, List.mem_ofFn.mpr ⟨k, rfl⟩, ?_⟩
        simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hk
    · change (u.val, v.val) ∈ own.flatMap (fun p => p.2.map fun w => (w, p.1)) ↔ _
      rw [List.mem_flatMap]
      constructor
      · rintro ⟨p, hp, hz⟩
        obtain ⟨w, hw, hz⟩ := List.mem_map.mp hz
        exact ⟨p, hp, w, hw, hz.symm⟩
      · rintro ⟨p, hp, w, hw, hz⟩
        exact ⟨p, hp, List.mem_map.mpr ⟨w, hw, hz.symm⟩⟩
  have block_shape (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
      ∀ g ∈ PEqualNP.MetaComplexity.blockGates B a t v1 rest lead,
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    cases lead <;> simp [block_def] at hg <;> rcases hg with ⟨i, _, rfl⟩ | rfl | rfl <;> simp

  have gates_shape : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
      ∀ g ∈ PEqualNP.MetaComplexity.coverGatesB B lead a own,
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 := by
    intro own
    induction own with
    | nil => intro B lead a g hg; simp [cover_nil] at hg
    | cons p os ih =>
      obtain ⟨t, l⟩ := p
      cases l with
      | nil =>
        intro B lead a g hg
        simp only [cover_empty] at hg
        exact ih B lead a g hg
      | cons v1 rest =>
        intro B lead a g hg
        simp only [cover_cons, List.mem_append] at hg
        rcases hg with hg | hg
        · exact block_shape B a t v1 rest lead g hg
        · exact ih _ false _ g hg

  have circuit_shape (n : ℕ) (own : List (ℕ × List ℕ)) :
      PEqualNP.MetaComplexity.Monotone2 (PEqualNP.MetaComplexity.coverCircuitB n own) ∧ ∀ g ∈ (PEqualNP.MetaComplexity.coverCircuitB n own).gates, g.inputs.length = 2 := by
    have key : ∀ g ∈ (PEqualNP.MetaComplexity.coverCircuitB n own).gates,
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 := by
      intro g hg
      unfold PEqualNP.MetaComplexity.coverCircuitB at hg
      split_ifs at hg with h
      · simp at hg
      · exact gates_shape own n true 0 g hg
    refine ⟨fun g hg => ?_, fun g hg => (key g hg).2⟩
    obtain ⟨hop, hlen⟩ := key g hg
    refine ⟨?_, by omega⟩
    rcases hop with h | h <;> simp [h]



  have block_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
      (PEqualNP.MetaComplexity.blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
    cases lead <;> simp [block_def]

  have gates_length_false : ∀ (own : List (ℕ × List ℕ)) (B a : ℕ), (∀ p ∈ own, p.2 ≠ []) →
      (PEqualNP.MetaComplexity.coverGatesB B false a own).length =
        (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length := by
    intro own
    induction own with
    | nil => intro B a h; simp [cover_nil]
    | cons p os ih =>
      obtain ⟨t, l⟩ := p
      cases l with
      | nil => intro B a h; simp at h
      | cons v1 rest =>
        intro B a h
        have ih' := ih (B + (PEqualNP.MetaComplexity.blockGates B a t v1 rest false).length)
          (B + (PEqualNP.MetaComplexity.blockGates B a t v1 rest false).length - 1)
          (fun p hp => h p (List.mem_cons_of_mem _ hp))
        simp only [cover_cons, List.length_append]
        rw [ih', block_length]
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        simp
        omega

  have circuit_size (n : ℕ) (own : List (ℕ × List ℕ)) (hne : own ≠ [])
      (h : ∀ p ∈ own, p.2 ≠ []) :
      (PEqualNP.MetaComplexity.coverCircuitB n own).size + 1 =
        (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length := by
    match own, hne, h with
    | (t, []) :: os, _, h => simp at h
    | (t, v1 :: rest) :: os, _, h =>
        have ih := gates_length_false os (n + (PEqualNP.MetaComplexity.blockGates n 0 t v1 rest true).length)
          (n + (PEqualNP.MetaComplexity.blockGates n 0 t v1 rest true).length - 1)
          (fun p hp => h p (List.mem_cons_of_mem _ hp))
        have hgl : (PEqualNP.MetaComplexity.coverGatesB n true 0 ((t, v1 :: rest) :: os)).length =
            rest.length + 1 + ((os.map (fun p : ℕ × List ℕ => p.2.length)).sum + os.length) := by
          simp only [cover_cons, List.length_append]
          rw [ih, block_length]
          simp
        have hnn : PEqualNP.MetaComplexity.coverGatesB n true 0 ((t, v1 :: rest) :: os) ≠ [] := by
          intro h0
          have h1 := congrArg List.length h0
          rw [hgl] at h1
          simp at h1
        unfold PEqualNP.MetaComplexity.coverCircuitB PEqualNP.CircuitLowerBounds.Circuit.size
        rw [ite_eq_right hnn]
        simp only [hgl, List.map_cons, List.sum_cons, List.length_cons]
        omega




  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

  have fold_app (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool, ∃ t : List Bool,
      gs.foldl step w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (step w g)
      refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_, ?_⟩
      · rw [List.foldl_cons, ht]; simp [step]
      · simp [hl]

  have getD_app_left {w t : List Bool} {i : ℕ} (h : i < w.length) :
      (w ++ t).getD i false = w.getD i false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

  have getD_app_right {w t : List Bool} {i : ℕ} :
      (w ++ t).getD (w.length + i) false = t.getD i false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD]

  have getD_snoc' (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
      (l ++ [b]).getD i false = b := by
    subst h
    exact getD_app_right (w := l) (t := [b]) (i := 0)

  have fold_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := fold_app gs w
    rw [ht, List.length_append, hl]

  have fold_keep (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := fold_app gs w
    rw [ht, getD_app_left h]

  have any_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ u ∈ l, f u = g u) :
      l.any f = l.any g := by
    induction l with
    | nil => rfl
    | cons b l ih =>
      simp only [List.any_cons]
      rw [h b (by simp), ih (fun u hu => h u (by simp [hu]))]


  let cv (w : List Bool) (v1 : ℕ) (rest : List ℕ) (k : ℕ) : Bool :=
    w.getD v1 false || (rest.take k).any (fun u => w.getD u false)

  have chain_read (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
      (hv1 : v1 < B) (k : ℕ) (hk : k ≤ rest.length) :
      (w ++ (List.range k).map (fun i => cv w v1 rest (i + 1))).getD
          ((v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0) false
        = cv w v1 rest k := by
    cases k with
    | zero =>
      simp only [List.getD_cons_zero]
      rw [getD_app_left (by omega)]
      simp [cv]
    | succ j =>
      have hj : j < rest.length := by omega
      have e1 : (v1 :: (List.range rest.length).map (fun j => B + j)).getD (j + 1) 0 = B + j := by
        simp [List.getD_eq_getElem?_getD, hj]
      rw [e1, ← hw, getD_app_right]
      simp [List.getD_eq_getElem?_getD]

  have chain (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
      (hv1 : v1 < B) (hrest : ∀ u ∈ rest, u < B) :
      ∀ k ≤ rest.length,
        ((List.range k).map (fun i => (⟨PEqualNP.CircuitLowerBounds.GateOp.or,
            [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩ : PEqualNP.CircuitLowerBounds.Gate))).foldl
          step w = w ++ (List.range k).map (fun i => cv w v1 rest (i + 1)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
      rw [List.append_assoc]
      congr 2
      have hkr : k < rest.length := by omega
      have hrk : rest.getD k 0 = rest[k] := by
        simp [List.getD_eq_getElem?_getD, hkr]
      have hlt : rest[k] < w.length := by rw [hw]; exact hrest _ (List.getElem_mem hkr)
      simp only [eval_or]
      rw [chain_read w B v1 rest hw hv1 k (by omega), hrk, getD_app_left hlt]
      simp only [cv, List.take_add_one,
        List.any_append, List.any_cons, List.any_nil, List.any_cons, Bool.or_false, id]
      simp [Bool.or_assoc, List.getElem?_eq_getElem hkr]

  have block_val (w : List Bool) (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
      (hw : w.length = B) (ha : lead = false → a < B) (ht : t < B) (hv1 : v1 < B)
      (hrest : ∀ u ∈ rest, u < B) :
      ((PEqualNP.MetaComplexity.blockGates B a t v1 rest lead).foldl step w).getD
          (B + (PEqualNP.MetaComplexity.blockGates B a t v1 rest lead).length - 1) false
        = if lead then (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))
          else (w.getD a false ||
            (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))) := by
    have hc := chain w B v1 rest hw hv1 hrest rest.length le_rfl
    have hr := chain_read w B v1 rest hw hv1 rest.length le_rfl
    have hcvr : cv w v1 rest rest.length = (w.getD v1 false || rest.any (fun u => w.getD u false)) := by
      simp [cv]
    set L := (List.range rest.length).map (fun i => cv w v1 rest (i + 1)) with hL
    have hLl : L.length = rest.length := by simp [hL]
    have htW : (w ++ L).getD t false = w.getD t false := getD_app_left (by omega)
    rw [block_length]
    cases lead with
    | true =>
      simp only [block_def, ↓reduceIte, List.foldl_append, hc, List.foldl_cons, List.foldl_nil,
        step]
      rw [getD_snoc']
      · simp only [eval_and, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
        rw [htW, hr, hcvr]
        simp
      · simp [hLl, hw]
    | false =>
      have ha' : a < B := ha rfl
      simp only [block_def, Bool.false_eq_true, ↓reduceIte, List.foldl_append, hc, List.foldl_cons,
        List.foldl_nil, step]
      rw [getD_snoc']
      · simp only [eval_and, eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
        rw [getD_app_left (by simp; omega), getD_app_left (by omega), getD_snoc']
        · simp only [List.all_cons, List.all_nil]
          rw [htW, hr, hcvr]
          simp
        · simp [hLl, hw]
      · simp [hLl, hw]


  let F (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
    own.any (fun p => x.getD p.1 false && p.2.any (fun u => x.getD u false))

  have gates_nil_F (x : List Bool) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
      PEqualNP.MetaComplexity.coverGatesB B lead a own = [] → F x own = false := by
    intro own
    induction own with
    | nil => intro B lead a h; rfl
    | cons p os ih =>
      obtain ⟨t, l⟩ := p
      cases l with
      | nil =>
        intro B lead a h
        simp only [cover_empty] at h
        have hh := ih B lead a h
        simp only [F, List.any_cons, List.any_nil, Bool.and_false, Bool.false_or] at hh ⊢
        exact hh
      | cons v1 rest =>
        intro B lead a h
        simp only [cover_cons] at h
        cases lead <;> simp [block_def] at h

  have main (n : ℕ) (x : List Bool) :
      ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ) (w : List Bool),
        (∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) → w.length = B → n ≤ B →
        (∀ i < n, w.getD i false = x.getD i false) → (lead = false → a < B) →
        PEqualNP.MetaComplexity.coverGatesB B lead a own ≠ [] →
        ((PEqualNP.MetaComplexity.coverGatesB B lead a own).foldl step w).getD
            (B + (PEqualNP.MetaComplexity.coverGatesB B lead a own).length - 1) false
          = if lead then F x own else (w.getD a false || F x own) := by
    intro own
    induction own with
    | nil => intro B lead a w hown hw hnB hwx ha hne; simp [cover_nil] at hne
    | cons p os ih =>
      obtain ⟨t, l⟩ := p
      cases l with
      | nil =>
        intro B lead a w hown hw hnB hwx ha hne
        simp only [cover_empty] at hne ⊢
        rw [ih B lead a w (fun p hp => hown p (List.mem_cons_of_mem _ hp)) hw hnB hwx ha hne]
        simp [F]
      | cons v1 rest =>
        intro B lead a w hown hw hnB hwx ha hne
        have hp := hown (t, v1 :: rest) (by simp)
        have ht : t < n := hp.1
        have hv1 : v1 < n := hp.2 v1 (by simp)
        have hrest : ∀ u ∈ rest, u < n := fun u hu => hp.2 u (by simp [hu])
        have hos : ∀ p ∈ os, p.1 < n ∧ ∀ u ∈ p.2, u < n :=
          fun p hp => hown p (List.mem_cons_of_mem _ hp)
        have hbv := block_val w B a t v1 rest lead hw ha (by omega) (by omega)
          (fun u hu => by have := hrest u hu; omega)
        have hrx : rest.any (fun u => w.getD u false) = rest.any (fun u => x.getD u false) :=
          any_congr_mem (fun u hu => hwx u (hrest u hu))
        rw [hrx, hwx t ht, hwx v1 hv1] at hbv
        set bg := PEqualNP.MetaComplexity.blockGates B a t v1 rest lead with hbg
        have hm : 0 < bg.length := by rw [hbg, block_length]; omega
        set W1 := bg.foldl step w with hW1
        have hW1l : W1.length = B + bg.length := by rw [hW1, fold_length, hw]
        have hW1x : ∀ i < n, W1.getD i false = x.getD i false := by
          intro i hi
          rw [hW1, fold_keep bg w (by omega)]
          exact hwx i hi
        have hW1a : lead = false → W1.getD a false = w.getD a false := by
          intro hl
          rw [hW1, fold_keep bg w (by have := ha hl; omega)]
        have hcons : F x ((t, v1 :: rest) :: os) =
            ((x.getD t false && (x.getD v1 false || rest.any (fun u => x.getD u false))) || F x os) :=
          rfl
        rw [hcons]
        simp only [cover_cons]
        rw [← hbg, List.foldl_append, ← hW1, List.length_append]
        by_cases hnil : PEqualNP.MetaComplexity.coverGatesB (B + bg.length) false (B + bg.length - 1) os = []
        · have hF := gates_nil_F x os _ false _ hnil
          rw [hnil, List.foldl_nil, List.length_nil, Nat.add_zero, hbv]
          rw [hF]
          cases lead <;> simp
        · have ih' := ih (B + bg.length) false (B + bg.length - 1) W1 hos hW1l (by omega)
            hW1x (fun _ => by omega) hnil
          have hidx : B + (bg.length + (PEqualNP.MetaComplexity.coverGatesB (B + bg.length) false (B + bg.length - 1) os).length) - 1
              = B + bg.length + (PEqualNP.MetaComplexity.coverGatesB (B + bg.length) false (B + bg.length - 1) os).length - 1 := by
            omega
          rw [hidx, ih', hbv]
          cases lead <;> simp [Bool.or_assoc]

  have circuit_fun (n : ℕ) (own : List (ℕ × List ℕ))
      (h : ∀ p ∈ own, p.1 < n ∧ ∀ w ∈ p.2, w < n) (x : Fin n → Bool) :
      ((PEqualNP.MetaComplexity.coverCircuitB n own).eval (List.ofFn x) = true ↔
        ∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
          ∃ w ∈ p.2, (List.ofFn x).getD w false = true) := by
    have hF : (∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
          ∃ w ∈ p.2, (List.ofFn x).getD w false = true) ↔ F (List.ofFn x) own = true := by
      simp [F, List.any_eq_true]
    rw [hF]
    unfold PEqualNP.MetaComplexity.coverCircuitB PEqualNP.CircuitLowerBounds.Circuit.eval
    split_ifs with hnil
    · rw [gates_nil_F _ own n true 0 hnil, wires_eq]
      simp [List.getD_eq_getElem?_getD]
    · rw [wires_eq]
      simp only
      rw [main n (List.ofFn x) own n true 0 (List.ofFn x) h (by simp) le_rfl (fun _ _ => rfl)
        (by simp) hnil]
      simp


  have hown : ∀ p ∈ own, p.1 < 42 ∧ p.2 ≠ [] ∧ ∀ w ∈ p.2, w < 42 := by decide +kernel
  let D := PEqualNP.MetaComplexity.coverCircuitB 42 own
  have hDmono : PEqualNP.MetaComplexity.Monotone2 D := (circuit_shape 42 own).1
  have hDsize : D.size = 89 := by
    have hs := circuit_size 42 own (by decide +kernel) (fun p hp => (hown p hp).2.1)
    have hn : (own.map (fun p => p.2.length)).sum + own.length = 90 := by decide +kernel
    change D.size + 1 = _ at hs
    omega
  have hDout : D.output < 42 + D.size := by decide +kernel
  change ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 34 ∧ C.output < 21 + C.size ∧
    ∀ x : Fin 21 → Bool, C.eval (List.ofFn x) = true ↔ ∃ k : Fin 15,
      x (Fin.castAdd 6 k) = true ∧
      (x (Fin.natAdd 15 (ends k).1) = true ∨ x (Fin.natAdd 15 (ends k).2) = true) at hlocal
  obtain ⟨C, hCmono, hCsize, hCout, hCfun⟩ := hlocal
  obtain ⟨E, hEmono, hEsize, hEfun⟩ := hor 21 42 42 C D hCmono hDmono hCout hDout f id
  refine ⟨E, hEmono, by omega, ?_⟩
  intro x
  change E.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 42, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true
  rw [hEfun x, Bool.or_eq_true]
  have hxget (i : Fin 42) : (List.ofFn x).getD i.val false = x i := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
  have hDfun := circuit_fun 42 own (fun p hp => ⟨(hown p hp).1, (hown p hp).2.2⟩) x
  change D.eval (List.ofFn x) = true ↔ _ at hDfun
  change (C.eval (List.ofFn (fun i => x (f i))) = true ∨ D.eval (List.ofFn x) = true) ↔ _
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨k, hpk, hlk⟩ := (hCfun (fun i => x (f i))).mp h
      rcases hlk with hline | hline
      · exact ⟨f (Fin.castAdd 6 k), f (Fin.natAdd 15 (ends k).1),
          (hsplit _ _).mpr (Or.inl ⟨k, Or.inl rfl⟩), hpk, hline⟩
      · exact ⟨f (Fin.castAdd 6 k), f (Fin.natAdd 15 (ends k).2),
          (hsplit _ _).mpr (Or.inl ⟨k, Or.inr rfl⟩), hpk, hline⟩
    · obtain ⟨p, hp, hpx, w, hw, hwx⟩ := hDfun.mp h
      let u : Fin 42 := ⟨w, (hown p hp).2.2 w hw⟩
      let v : Fin 42 := ⟨p.1, (hown p hp).1⟩
      refine ⟨u, v, (hsplit u v).mpr (Or.inr ⟨p, hp, w, hw, rfl⟩), ?_, ?_⟩
      · exact (hxget u).symm.trans hwx
      · exact (hxget v).symm.trans hpx
  · rintro ⟨u, v, huv, hxu, hxv⟩
    rcases (hsplit u v).mp huv with hk | hp
    · left
      apply (hCfun (fun i => x (f i))).mpr
      obtain ⟨k, hk | hk⟩ := hk
      · have hu : u = f (Fin.castAdd 6 k) := Fin.ext (congrArg Prod.fst hk)
        have hv : v = f (Fin.natAdd 15 (ends k).1) := Fin.ext (congrArg Prod.snd hk)
        exact ⟨k, hu ▸ hxu, Or.inl (hv ▸ hxv)⟩
      · have hu : u = f (Fin.castAdd 6 k) := Fin.ext (congrArg Prod.fst hk)
        have hv : v = f (Fin.natAdd 15 (ends k).2) := Fin.ext (congrArg Prod.snd hk)
        exact ⟨k, hu ▸ hxu, Or.inr (hv ▸ hxv)⟩
    · right
      apply hDfun.mpr
      obtain ⟨p, hp, w, hw, heq⟩ := hp
      have he1 : u.val = w := congrArg Prod.fst heq
      have he2 : v.val = p.1 := congrArg Prod.snd heq
      refine ⟨p, hp, ?_, w, hw, ?_⟩
      · rw [← he2, hxget]; exact hxv
      · rw [← he1, hxget]; exact hxu
