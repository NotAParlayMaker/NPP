import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

-- Gate elimination at vertex 0. When x 0 is false, wire 0 and the supplied wire
-- x 0 && x 2 (wire 10) are false, so an AND or OR gate that reads one of them has
-- the value of an earlier wire and can be erased (one erasure as in L-meta-2642).
-- If three such gates exist, erasing them leaves at most 15 gates computing the edge
-- function on the inputs with x 0 false: the Petersen graph minus vertex 0, whose
-- bound is the first hypothesis. The second hypothesis is the remaining case, at
-- most two AND or OR gates reading wire 0 or wire 10.
-- Input reindexing as in R-meta-1890-1.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1890_503
    (minorBound : ∀ D : Circuit, FanInTwo D → D.size ≤ 15 → ∃ x : Fin 10 → Bool, x 0 = false ∧
      D.eval (List.ofFn x ++ [x 0 && x 2]) ≠
        (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (fewReaders : ∀ D : Circuit, FanInTwo D → D.size ≤ 18 →
      (¬ ∃ a b c : ℕ, a < b ∧ b < c ∧ ∀ m ∈ [a, b, c], ∃ g ∈ D.gates[m]?,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ (0 ∈ g.inputs ∨ 10 ∈ g.inputs)) →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 && x 2]) ≠
        (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  have transport :
      ∀ (n : ℕ) (C : Circuit) (p : Fin n → Fin n), FanInTwo C →
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (x : Fin n → Bool) (tail : List Bool),
            D.eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ p) ++ tail) := by
    intro n C p hfan
    let rename (i : ℕ) : ℕ := if hi : i < n then (p ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < n) : rename i < n := by simp [rename, hi]
    have late (i : ℕ) (hi : n ≤ i) : rename i = i := by simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let D : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g' hg').1, by simpa [mapGate] using (hfan g' hg').2⟩
    · exact List.length_map mapGate
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length)
        (lo : n ≤ x.length) (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have next : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [next]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases hn : i < n
            · have := early i hn
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x tail
    apply run C.gates _ _ (by simp) (by simp) _ C.output
    intro i
    by_cases hi : i < n
    · have hx : rename i < (List.ofFn x).length := by simpa using early i hi
      have hy : i < (List.ofFn (x ∘ p)).length := by simpa using hi
      rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy,
          List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
      simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      exact dite_eq_left hi
    · rw [late i (by omega), List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi)]
      simp
  have foldPrefix : ∀ (gs : List Gate) (w : List Bool), ∃ t,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧
        t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      rw [List.foldl_cons, ht]
      simp
  have foldLength : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        w.length + gs.length := by
    intro gs w
    obtain ⟨t, ht, hl⟩ := foldPrefix gs w
    rw [ht, List.length_append, hl]
  have foldLow : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i
        false = w.getD i false := by
    intro gs w i hi
    obtain ⟨t, ht, -⟩ := foldPrefix gs w
    rw [ht, List.getD_append _ _ _ _ hi]
  have high : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false :=
    fun w i hi => List.getD_eq_default _ _ hi
  -- One erasure, as in L-meta-2642: gate m of C on n inputs is removed and its readers
  -- read wire p, an earlier wire with the same value on the input y.
  have sim : ∀ (n m p : ℕ) (rest : List Gate) (U V : List Bool),
      (∀ i, U.getD i false = V.getD (if i < n + m then i else i + 1) false) →
      n + m ≤ U.length → V.length = U.length + 1 → p < n + m →
      U.getD p false = V.getD (n + m) false →
      ∀ i, ((rest.map (fun g : Gate => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) U).getD i false =
        (rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) V).getD
          (if i < n + m then i else i + 1) false := by
    intro n m p rest
    induction rest with
    | nil => intro U V hrel _ _ _ _; simpa using hrel
    | cons g rest ih =>
      intro U V hrel hk hlen hp hS
      have hread : ∀ r ∈ g.inputs, U.getD (eraseRedirect n m p r) false = V.getD r false := by
        intro r _
        by_cases hrk : r = n + m
        · subst hrk
          simpa [eraseRedirect] using hS
        · rw [hrel]
          congr 1
          unfold eraseRedirect
          split_ifs <;> omega
      set a := g.op.eval (g.inputs.map fun i => V.getD i false) with ha
      have hU : (U ++ [GateOp.eval g.op ((g.inputs.map (eraseRedirect n m p)).map
          fun i => U.getD i false)]) = U ++ [a] := by
        rw [List.map_map]
        congr 3
        exact List.map_congr_left fun r hr => hread r hr
      simp only [List.map_cons, List.foldl_cons]
      rw [hU, ← ha]
      apply ih
      · intro i
        rcases lt_trichotomy i U.length with hi | rfl | hi
        · have hup : (if i < n + m then i else i + 1) < V.length := by split_ifs <;> omega
          rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hup, hrel]
        · have hup : (if U.length < n + m then U.length else U.length + 1) = V.length := by
            split_ifs <;> omega
          rw [hup, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
          simp
        · rw [high _ _ (by simp; omega), high _ _ (by simp; split_ifs <;> omega)]
      · simp; omega
      · simp; omega
      · exact hp
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hS
  have eraseShape : ∀ (n : ℕ) (C : Circuit) (m p : ℕ), m < C.gates.length →
      (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map
        (fun g : Gate => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate)) ∧
      (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    intro n C m p hm
    unfold eraseGate
    rw [if_pos hm]
    exact ⟨rfl, rfl⟩
  have split : ∀ (C : Circuit) (m : ℕ) (hm : m < C.gates.length),
      C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    intro C m hm
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have eraseEval : ∀ (n : ℕ) (C : Circuit) (m p : ℕ) (y : List Bool), y.length = n →
      m < C.gates.length → p < n + m →
      (C.wires y).getD (n + m) false = (C.wires y).getD p false →
      (eraseGate n C m p).eval y = C.eval y := by
    intro n C m p y hy hm hp hc
    obtain ⟨hg, ho⟩ := eraseShape n C m p hm
    set A := (C.gates.take m).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y with hA
    have hAl : A.length = n + m := by
      rw [hA, foldLength, hy, List.length_take]; omega
    set B := A ++ [C.gates[m].op.eval (C.gates[m].inputs.map fun i => A.getD i false)] with hB
    set rest := C.gates.drop (m + 1) with hrest
    have hW : C.wires y = rest.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) B := by
      unfold Circuit.wires
      conv_lhs => rw [split C m hm]
      rw [List.foldl_append, List.foldl_cons]
    have hW' : (eraseGate n C m p).wires y = (rest.map
        (fun g : Gate => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) A := by
      unfold Circuit.wires
      rw [hg, List.foldl_append]
    have hBl : B.length = A.length + 1 := by simp [hB]
    have hstable : ∀ i, i < n + m + 1 → B.getD i false = (C.wires y).getD i false := by
      intro i hi
      rw [hW, foldLow _ _ _ (by omega)]
    have hsim := sim n m p rest A B (by
        intro i
        by_cases hi : i < n + m
        · rw [if_pos hi, hB, List.getD_append _ _ _ _ (by omega)]
        · rw [if_neg hi, high _ _ (by omega), high _ _ (by omega)])
      (by omega) hBl hp (by
        rw [hstable _ (by omega), hc, ← hstable _ (by omega), hB,
          List.getD_append _ _ _ _ (by omega)])
    unfold Circuit.eval
    rw [ho, hW', hsim, ← hW]
    by_cases hout : C.output = n + m
    · have hr : eraseRedirect n m p C.output = p := by
        unfold eraseRedirect; rw [if_pos hout]
      rw [hr, hout, if_pos hp]
      exact hc.symm
    · congr 1
      unfold eraseRedirect
      split_ifs <;> omega
  have eraseSize : ∀ (n : ℕ) (C : Circuit) (m p : ℕ), m < C.gates.length →
      (eraseGate n C m p).size + 1 = C.size := by
    intro n C m p hm
    unfold Circuit.size
    rw [(eraseShape n C m p hm).1]
    simp
    omega
  have eraseFan : ∀ (n : ℕ) (C : Circuit) (m p : ℕ), m < C.gates.length → FanInTwo C →
      FanInTwo (eraseGate n C m p) := by
    intro n C m p hm hC g hg
    rw [(eraseShape n C m p hm).1, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hC g (List.mem_of_mem_take hg)
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      obtain ⟨h1, h2⟩ := hC g' (List.mem_of_mem_drop hg')
      exact ⟨h1, by simpa using h2⟩
  have eraseKeep : ∀ (n : ℕ) (C : Circuit) (m p j : ℕ), m < C.gates.length → j < m →
      (eraseGate n C m p).gates[j]? = C.gates[j]? := by
    intro n C m p j hm hj
    rw [(eraseShape n C m p hm).1, List.getElem?_append_left (by simp; omega),
      List.getElem?_take_of_lt hj]
  -- The value of gate m read from the wires before it.
  let pre (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
  have preLen (x : Fin 10 → Bool) : (pre x).length = 11 := by simp [pre]
  have gateVal : ∀ (C : Circuit) (m : ℕ) (g : Gate) (y : List Bool), y.length = 11 →
      C.gates[m]? = some g →
      (C.wires y).getD (11 + m) false = g.op.eval (g.inputs.map fun i =>
        ((C.gates.take m).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD i false) ∧
      ∀ i, i < 11 + m → (C.wires y).getD i false = ((C.gates.take m).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD i false := by
    intro C m g y hy hg
    obtain ⟨hm, hgm⟩ := List.getElem?_eq_some_iff.mp hg
    set A := (C.gates.take m).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y with hA
    have hAl : A.length = 11 + m := by
      rw [hA, foldLength, hy, List.length_take]; omega
    have hW : C.wires y = (C.gates.drop (m + 1)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (A ++ [g.op.eval (g.inputs.map fun i => A.getD i false)]) := by
      unfold Circuit.wires
      conv_lhs => rw [split C m hm]
      rw [List.foldl_append, List.foldl_cons, hgm]
    refine ⟨?_, ?_⟩
    · rw [hW, foldLow _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
      simp [hAl]
    · intro i hi
      rw [hW, foldLow _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
  -- With x 0 = false, wire 0 and wire 10 are false, so an AND or OR gate reading one of them
  -- has the value of an earlier wire.
  have redirect : ∀ (C : Circuit) (m : ℕ) (g : Gate), FanInTwo C → C.gates[m]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) → (0 ∈ g.inputs ∨ 10 ∈ g.inputs) →
      ∃ p, p < 11 + m ∧ ∀ x : Fin 10 → Bool, x 0 = false →
        (C.wires (pre x)).getD (11 + m) false = (C.wires (pre x)).getD p false := by
    intro C m g hC hg hop hin
    have gLen : g.inputs.length ≤ 2 := (hC g (List.mem_of_getElem? hg)).2
    have dead : ∀ x : Fin 10 → Bool, x 0 = false → ∀ i, (i = 0 ∨ i = 10) →
        ((C.gates.take m).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (pre x)).getD i
            false = false := by
      intro x hx i hi
      rw [foldLow _ _ _ (by rw [preLen]; omega)]
      rcases hi with rfl | rfl
      · simp [pre, hx]
      · simp [pre, hx]
    -- the earlier wire t, or wire 10 if t is not earlier (then t reads false)
    have pick : ∀ t : ℕ, ∃ p, p < 11 + m ∧ ∀ x : Fin 10 → Bool, x 0 = false →
        ((C.gates.take m).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (pre x)).getD t
            false = (C.wires (pre x)).getD p false := by
      intro t
      by_cases ht : t < 11 + m
      · exact ⟨t, ht, fun x _ => ((gateVal C m g (pre x) (preLen x) hg).2 t ht).symm⟩
      · refine ⟨10, by omega, fun x hx => ?_⟩
        rw [(gateVal C m g (pre x) (preLen x) hg).2 10 (by omega), dead x hx 10 (Or.inr rfl),
          high _ _ (by rw [foldLength, preLen, List.length_take]; omega)]
    obtain ⟨op, ins⟩ := g
    simp only at hop hin gLen
    rcases hop with rfl | rfl
    · refine ⟨10, by omega, fun x hx => ?_⟩
      rw [(gateVal C m _ (pre x) (preLen x) hg).1, (gateVal C m _ (pre x) (preLen x) hg).2 10
        (by omega), dead x hx 10 (Or.inr rfl)]
      show (List.map _ ins).all id = false
      rcases hin with hz | hz
      · exact List.all_eq_false.mpr ⟨_, List.mem_map_of_mem hz, by
          simp only [dead x hx 0 (Or.inl rfl)]; decide⟩
      · exact List.all_eq_false.mpr ⟨_, List.mem_map_of_mem hz, by
          simp only [dead x hx 10 (Or.inr rfl)]; decide⟩
    · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, l⟩⟩⟩
      · simp at hin
      · refine ⟨10, by omega, fun x hx => ?_⟩
        have ha : a = 0 ∨ a = 10 := by simp at hin; omega
        rw [(gateVal C m _ (pre x) (preLen x) hg).1, (gateVal C m _ (pre x) (preLen x) hg).2 10
          (by omega), dead x hx 10 (Or.inr rfl)]
        simp only [List.map_cons, List.map_nil, dead x hx a ha]
        rfl
      · by_cases ha : a = 0 ∨ a = 10
        · obtain ⟨p, hp, hpx⟩ := pick c
          refine ⟨p, hp, fun x hx => ?_⟩
          rw [(gateVal C m _ (pre x) (preLen x) hg).1, ← hpx x hx]
          simp only [List.map_cons, List.map_nil, dead x hx a ha]
          show [false, _].any id = _
          simp
        · have hc : c = 0 ∨ c = 10 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
            omega
          obtain ⟨p, hp, hpx⟩ := pick a
          refine ⟨p, hp, fun x hx => ?_⟩
          rw [(gateVal C m _ (pre x) (preLen x) hg).1, ← hpx x hx]
          simp only [List.map_cons, List.map_nil, dead x hx c hc]
          show [_, false].any id = _
          simp
      · simp at gLen
  intro C π hC small
  obtain ⟨E, eFan, eSize, agree⟩ := transport 10 C π hC
  have eBound : E.size ≤ 18 := eSize.le.trans small
  by_cases three : ∃ a b c : ℕ, a < b ∧ b < c ∧ ∀ m ∈ [a, b, c], ∃ g ∈ E.gates[m]?,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ (0 ∈ g.inputs ∨ 10 ∈ g.inputs)
  · obtain ⟨a, b, c, hab, hbc, hr⟩ := three
    obtain ⟨gc, hgc, opc, inc⟩ := hr c (by simp)
    obtain ⟨gb, hgb, opb, inb⟩ := hr b (by simp)
    obtain ⟨ga, hga, opa, ina⟩ := hr a (by simp)
    rw [Option.mem_def] at hgc hgb hga
    have cLen : c < E.gates.length := (List.getElem?_eq_some_iff.mp hgc).1
    obtain ⟨pc, pcLt, pcEq⟩ := redirect E c gc eFan hgc opc inc
    have f1 := eraseFan 11 E c pc cLen eFan
    have s1 := eraseSize 11 E c pc cLen
    have hgb1 : (eraseGate 11 E c pc).gates[b]? = some gb := by
      rw [eraseKeep 11 E c pc b cLen hbc]; exact hgb
    have hga1 : (eraseGate 11 E c pc).gates[a]? = some ga := by
      rw [eraseKeep 11 E c pc a cLen (by omega)]; exact hga
    set E1 := eraseGate 11 E c pc with hE1
    have bLen : b < E1.gates.length := (List.getElem?_eq_some_iff.mp hgb1).1
    obtain ⟨pb, pbLt, pbEq⟩ := redirect E1 b gb f1 hgb1 opb inb
    have f2 := eraseFan 11 E1 b pb bLen f1
    have s2 := eraseSize 11 E1 b pb bLen
    have hga2 : (eraseGate 11 E1 b pb).gates[a]? = some ga := by
      rw [eraseKeep 11 E1 b pb a bLen hab]; exact hga1
    set E2 := eraseGate 11 E1 b pb with hE2
    have aLen : a < E2.gates.length := (List.getElem?_eq_some_iff.mp hga2).1
    obtain ⟨pa, paLt, paEq⟩ := redirect E2 a ga f2 hga2 opa ina
    have f3 := eraseFan 11 E2 a pa aLen f2
    have s3 := eraseSize 11 E2 a pa aLen
    obtain ⟨x, hx0, hx⟩ := minorBound (eraseGate 11 E2 a pa) f3 (by omega)
    refine ⟨x, ?_⟩
    rw [← agree x [x 0 && x 2]]
    have v3 := eraseEval 11 E2 a pa (pre x) (preLen x) aLen paLt (paEq x hx0)
    have v2 := eraseEval 11 E1 b pb (pre x) (preLen x) bLen pbLt (pbEq x hx0)
    have v1 := eraseEval 11 E c pc (pre x) (preLen x) cLen pcLt (pcEq x hx0)
    change (eraseGate 11 E2 a pa).eval (pre x) ≠ _ at hx
    rw [v3, v2, v1] at hx
    exact hx
  · obtain ⟨x, hx⟩ := fewReaders E eFan eBound three
    refine ⟨x, ?_⟩
    rw [← agree x [x 0 && x 2]]
    exact hx
