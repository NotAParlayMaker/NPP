import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

-- A reduction of step L-meta-5234. It normalizes a circuit by dropping the dead
-- gates after the output wire, then leaves three smaller statements: the
-- normalized monotone, one-NOT and two-NOT bounds.
theorem PEqualNP.Outside.R_meta_5234_1
    (h0 : ∀ D : Circuit, Monotone2 D → ReadsBack 11 D → D.size ≤ 18 →
      D.output = 11 + D.size - 1 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        [((0 : Fin 10),(1 : Fin 10)),((1 : Fin 10),(2 : Fin 10)),((2 : Fin 10),(3 : Fin 10)),
         ((3 : Fin 10),(4 : Fin 10)),((4 : Fin 10),(0 : Fin 10)),((0 : Fin 10),(5 : Fin 10)),
         ((1 : Fin 10),(6 : Fin 10)),((2 : Fin 10),(7 : Fin 10)),((3 : Fin 10),(8 : Fin 10)),
         ((4 : Fin 10),(9 : Fin 10)),((5 : Fin 10),(7 : Fin 10)),((7 : Fin 10),(9 : Fin 10)),
         ((9 : Fin 10),(6 : Fin 10)),((6 : Fin 10),(8 : Fin 10)),((8 : Fin 10),(5 : Fin 10))].any
          (fun e => x e.1 && x e.2))
    (h1 : ∀ D : Circuit, FanInTwo D → ReadsBack 11 D → D.size ≤ 18 →
      D.output = 11 + D.size - 1 → notCount D = 1 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        [((0 : Fin 10),(1 : Fin 10)),((1 : Fin 10),(2 : Fin 10)),((2 : Fin 10),(3 : Fin 10)),
         ((3 : Fin 10),(4 : Fin 10)),((4 : Fin 10),(0 : Fin 10)),((0 : Fin 10),(5 : Fin 10)),
         ((1 : Fin 10),(6 : Fin 10)),((2 : Fin 10),(7 : Fin 10)),((3 : Fin 10),(8 : Fin 10)),
         ((4 : Fin 10),(9 : Fin 10)),((5 : Fin 10),(7 : Fin 10)),((7 : Fin 10),(9 : Fin 10)),
         ((9 : Fin 10),(6 : Fin 10)),((6 : Fin 10),(8 : Fin 10)),((8 : Fin 10),(5 : Fin 10))].any
          (fun e => x e.1 && x e.2))
    (h2 : ∀ D : Circuit, FanInTwo D → ReadsBack 11 D → D.size ≤ 18 →
      D.output = 11 + D.size - 1 → notCount D = 2 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) ≠
        [((0 : Fin 10),(1 : Fin 10)),((1 : Fin 10),(2 : Fin 10)),((2 : Fin 10),(3 : Fin 10)),
         ((3 : Fin 10),(4 : Fin 10)),((4 : Fin 10),(0 : Fin 10)),((0 : Fin 10),(5 : Fin 10)),
         ((1 : Fin 10),(6 : Fin 10)),((2 : Fin 10),(7 : Fin 10)),((3 : Fin 10),(8 : Fin 10)),
         ((4 : Fin 10),(9 : Fin 10)),((5 : Fin 10),(7 : Fin 10)),((7 : Fin 10),(9 : Fin 10)),
         ((9 : Fin 10),(6 : Fin 10)),((6 : Fin 10),(8 : Fin 10)),((8 : Fin 10),(5 : Fin 10))].any
          (fun e => x e.1 && x e.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  intro C hFan hReads hSize hLo hHi hnc1 hnc2
  let stepf : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let D : Circuit := ⟨C.gates.take (C.output - 10), C.output⟩
  have hfoldlen : ∀ (gs : List Gate) (w : List Bool), (gs.foldl stepf w).length = w.length + gs.length := by
    intro gs w
    induction gs generalizing w with
    | nil => simp [stepf]
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepf]
      omega
  have hfoldget : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepf w).getD i false = w.getD i false := by
    intro gs w i hi
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (stepf w g) (by simp [stepf]; omega)]
      exact List.getD_append w _ false i hi
  have hfk : ∀ (l : List Gate) (m : ℕ),
      ((l.take m).filter (fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not))).length ≤
        ((l).filter (fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not))).length := by
    intro l m
    exact List.Sublist.length_le (List.Sublist.filter
      (fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not))
      (List.take_sublist m l))
  have hle : C.output - 10 ≤ C.size := by omega
  have hDsize : D.size ≤ 18 := by
    change (C.gates.take (C.output - 10)).length ≤ 18
    have hle' : C.output - 10 ≤ C.gates.length := by
      change C.output - 10 ≤ C.size
      omega
    rw [List.length_take, min_eq_left hle']
    omega
  have hDfan : FanInTwo D := by
    intro g hg
    dsimp only [D] at hg
    exact hFan g (List.mem_of_mem_take hg)
  have hDreads : ReadsBack 11 D := by
    unfold ReadsBack gateAt
    dsimp only [D]
    intro j hj i hi
    rw [List.length_take] at hj
    have hjle : j < C.output - 10 := lt_of_lt_of_le hj (min_le_left _ _)
    have hj'' : j < C.gates.length := by omega
    have hgt : (C.gates.take (C.output - 10)).getD j ⟨GateOp.or, []⟩ = C.gates.getD j ⟨GateOp.or, []⟩ := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_take]
      simp [hjle]
    rw [hgt] at hi
    change i ∈ (gateAt C j).inputs at hi
    exact hReads j hj'' i hi
  have hDo : D.output = 11 + D.size - 1 := by
    change C.output = 11 + (C.gates.take (C.output - 10)).length - 1
    rw [List.length_take, min_eq_left (by change C.output - 10 ≤ C.size; omega)]
    omega
  have hDnc : notCount D ≤ 2 := by
    have hDncC : notCount D ≤ notCount C := by
      unfold notCount
      dsimp only [D]
      exact hfk C.gates (C.output - 10)
    omega
  have hDev : ∀ (x9 : Fin 10 → Bool), D.eval (List.ofFn x9 ++ [x9 (0 : Fin 10) || x9 (2 : Fin 10)]) = C.eval (List.ofFn x9 ++ [x9 (0 : Fin 10) || x9 (2 : Fin 10)]) := by
    intro x9
    let inp := List.ofFn x9 ++ [x9 (0 : Fin 10) || x9 (2 : Fin 10)]
    have hApp : C.gates.take (C.output - 10) ++ C.gates.drop (C.output - 10) = C.gates := by
      rw [List.take_append_drop]
    dsimp only [D]
    change ((C.gates.take (C.output - 10)).foldl stepf inp).getD C.output false =
      (C.gates.foldl stepf inp).getD C.output false
    conv_rhs => rw [← hApp, List.foldl_append]
    rw [hfoldget (C.gates.drop (C.output - 10)) ((C.gates.take (C.output - 10)).foldl stepf inp) (C.output)
      (by
        have hlenPre : ((C.gates.take (C.output - 10)).foldl stepf inp).length =
            inp.length + (C.gates.take (C.output - 10)).length :=
          hfoldlen (C.gates.take (C.output - 10)) inp
        rw [hlenPre, List.length_take, min_eq_left (by change C.output - 10 ≤ C.size; omega)]
        have hleninp : inp.length = 11 := by simp [inp]
        omega)]
  have hfm : ∀ (x9 : Fin 10 → Bool),
      [((0 : Fin 10),(1 : Fin 10)),((1 : Fin 10),(2 : Fin 10)),((2 : Fin 10),(3 : Fin 10)),
       ((3 : Fin 10),(4 : Fin 10)),((4 : Fin 10),(0 : Fin 10)),((0 : Fin 10),(5 : Fin 10)),
       ((1 : Fin 10),(6 : Fin 10)),((2 : Fin 10),(7 : Fin 10)),((3 : Fin 10),(8 : Fin 10)),
       ((4 : Fin 10),(9 : Fin 10)),((5 : Fin 10),(7 : Fin 10)),((7 : Fin 10),(9 : Fin 10)),
       ((9 : Fin 10),(6 : Fin 10)),((6 : Fin 10),(8 : Fin 10)),((8 : Fin 10),(5 : Fin 10))].any
        (fun e => x9 e.1 && x9 e.2) =
      (x9 (0 : Fin 10) && x9 (1 : Fin 10) || x9 (1 : Fin 10) && x9 (2 : Fin 10) ||
       x9 (2 : Fin 10) && x9 (3 : Fin 10) || x9 (3 : Fin 10) && x9 (4 : Fin 10) ||
       x9 (4 : Fin 10) && x9 (0 : Fin 10) || x9 (0 : Fin 10) && x9 (5 : Fin 10) ||
       x9 (1 : Fin 10) && x9 (6 : Fin 10) || x9 (2 : Fin 10) && x9 (7 : Fin 10) ||
       x9 (3 : Fin 10) && x9 (8 : Fin 10) || x9 (4 : Fin 10) && x9 (9 : Fin 10) ||
       x9 (5 : Fin 10) && x9 (7 : Fin 10) || x9 (7 : Fin 10) && x9 (9 : Fin 10) ||
       x9 (9 : Fin 10) && x9 (6 : Fin 10) || x9 (6 : Fin 10) && x9 (8 : Fin 10) ||
       x9 (8 : Fin 10) && x9 (5 : Fin 10)) := by
   intro x9
   simp only [List.any_cons, List.any_nil, Bool.or_false]
   ac_rfl
  by_contra hnone
  have hAllC : ∀ (x9 : Fin 10 → Bool), C.eval (List.ofFn x9 ++ [x9 (0 : Fin 10) || x9 (2 : Fin 10)]) = (x9 (0 : Fin 10) && x9 (1 : Fin 10) || x9 (1 : Fin 10) && x9 (2 : Fin 10) || x9 (2 : Fin 10) && x9 (3 : Fin 10) || x9 (3 : Fin 10) && x9 (4 : Fin 10) || x9 (4 : Fin 10) && x9 (0 : Fin 10) || x9 (0 : Fin 10) && x9 (5 : Fin 10) || x9 (1 : Fin 10) && x9 (6 : Fin 10) || x9 (2 : Fin 10) && x9 (7 : Fin 10) || x9 (3 : Fin 10) && x9 (8 : Fin 10) || x9 (4 : Fin 10) && x9 (9 : Fin 10) || x9 (5 : Fin 10) && x9 (7 : Fin 10) || x9 (7 : Fin 10) && x9 (9 : Fin 10) || x9 (9 : Fin 10) && x9 (6 : Fin 10) || x9 (6 : Fin 10) && x9 (8 : Fin 10) || x9 (8 : Fin 10) && x9 (5 : Fin 10)) := by
    intro x9
    by_contra hdiff
    exact hnone ⟨x9, hdiff⟩
  have hAllD : ∀ (x9 : Fin 10 → Bool), D.eval (List.ofFn x9 ++ [x9 (0 : Fin 10) || x9 (2 : Fin 10)]) = [((0 : Fin 10),(1 : Fin 10)),((1 : Fin 10),(2 : Fin 10)),((2 : Fin 10),(3 : Fin 10)),((3 : Fin 10),(4 : Fin 10)),((4 : Fin 10),(0 : Fin 10)),((0 : Fin 10),(5 : Fin 10)),((1 : Fin 10),(6 : Fin 10)),((2 : Fin 10),(7 : Fin 10)),((3 : Fin 10),(8 : Fin 10)),((4 : Fin 10),(9 : Fin 10)),((5 : Fin 10),(7 : Fin 10)),((7 : Fin 10),(9 : Fin 10)),((9 : Fin 10),(6 : Fin 10)),((6 : Fin 10),(8 : Fin 10)),((8 : Fin 10),(5 : Fin 10))].any (fun e => x9 e.1 && x9 e.2) := by
    intro x9
    rw [hDev x9, hAllC x9, ← (hfm x9)]
  by_cases hz : notCount D = 0
  · have hDMono : Monotone2 D := by
      intro g hg
      have hnot : g.op ≠ GateOp.not := by
        intro hne
        have hpos : 0 < notCount D := by
          change 0 < (D.gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)).length
          refine List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, ?_⟩)
          rw [hne]; rfl
        omega
      have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
        have hop := (hDfan g hg).1
        simpa using hop
      rcases hop' with h | h | h
      · exact ⟨by simp [h], (hDfan g hg).2⟩
      · exact ⟨by simp [h], (hDfan g hg).2⟩
      · exact (hnot h).elim
    obtain ⟨x, hx⟩ := h0 D hDMono hDreads hDsize hDo
    exact hx (hAllD x)
  · by_cases ho : notCount D = 1
    · obtain ⟨x, hx⟩ := h1 D hDfan hDreads hDsize hDo ho
      exact hx (hAllD x)
    · obtain ⟨x, hx⟩ := h2 D hDfan hDreads hDsize hDo (by omega)
      exact hx (hAllD x)
