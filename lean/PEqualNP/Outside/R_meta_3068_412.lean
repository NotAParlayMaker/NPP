import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The single inverter cancellation argument adapts the proof from pull request 5816.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3068_412
    (cofactor : ∀ (gs : List Gate) (j : Nat), gs.length ≤ 12 → FanInTwo ⟨gs,0⟩ →
      ∃ x : Fin 9 → Bool, x 6 = false ∧
        ((Circuit.mk gs 0).wires (List.ofFn x ++ [x 4 || x 6])).getD j false ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 2 && x 7) || (x 3 && x 8) ||
          (x 5 && x 7) || (x 8 && x 5)))
    (binary : ∀ C : Circuit, FanInTwo C →
      C.gates.countP (fun g => !(g.op.eval [false])) ≤ 12 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  let edge : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List Nat).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
  have edge_form (x : Fin 9 → Bool) :
      edge x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    simp only [edge, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  let bottom : Fin 9 → Bool := fun _ => false
  let top : Fin 9 → Bool := fun _ => true
  have edge_bottom : edge bottom = false := by decide
  have edge_top : edge top = true := by decide
  let pad (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let neg (g : Gate) := g.op.eval [false]
  let agrees (a b : List Bool) : Prop :=
    a.length = b.length ∧ ∀ i, a.getD i false ≤ b.getD i false
  have and_le : ∀ a b c d : Bool, a ≤ b → c ≤ d → (a && c) ≤ (b && d) := by decide
  have or_le : ∀ a b c d : Bool, a ≤ b → c ≤ d → (a || c) ≤ (b || d) := by decide
  have append_le (a b : List Bool) (ab : agrees a b) (c d : Bool) (cd : c ≤ d) :
      agrees (a ++ [c]) (b ++ [d]) := by
    refine ⟨by simp [ab.1], ?_⟩
    intro i
    by_cases hi : i < a.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by rwa [← ab.1])]
      exact ab.2 i
    · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by have := ab.1; omega), ab.1]
      by_cases he : i = b.length
      · simp [he, cd]
      · have hpos : 1 ≤ i - b.length := by have := ab.1; omega
        rw [List.getD_eq_default _ _ (by simpa using hpos),
            List.getD_eq_default _ _ (by simpa using hpos)]
  have pad_le (x y : Fin 9 → Bool) (xy : ∀ i, x i ≤ y i) : agrees (pad x) (pad y) := by
    refine append_le _ _ ⟨by simp, ?_⟩ _ _ (or_le _ _ _ _ (xy 4) (xy 6))
    intro i
    by_cases hi : i < 9
    · rw [List.getD_eq_getElem _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn, List.getElem_ofFn]
      exact xy ⟨i, hi⟩
    · rw [List.getD_eq_default _ _ (by simpa using hi),
          List.getD_eq_default _ _ (by simpa using hi)]
  have low (x : Fin 9 → Bool) : agrees (pad bottom) (pad x) :=
    pad_le bottom x (fun i => by cases x i <;> decide)
  have high (x : Fin 9 → Bool) : agrees (pad x) (pad top) :=
    pad_le x top (fun i => by cases x i <;> decide)
  have all_le (indices : List Nat) (a b : List Bool) (ab : agrees a b) :
      (indices.map fun i => a.getD i false).all id ≤
        (indices.map fun i => b.getD i false).all id := by
    induction indices with
    | nil => exact le_refl true
    | cons i is ih => exact and_le _ _ _ _ (ab.2 i) ih
  have any_le (indices : List Nat) (a b : List Bool) (ab : agrees a b) :
      (indices.map fun i => a.getD i false).any id ≤
        (indices.map fun i => b.getD i false).any id := by
    induction indices with
    | nil => exact le_refl false
    | cons i is ih => exact or_le _ _ _ _ (ab.2 i) ih
  have op_cases (g : Gate) (h : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp)) :
      g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have neg_op (g : Gate) (h : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp))
      (hn : neg g = true) : g.op = .not := by
    rcases op_cases g h with ha | ho | ht
    · change g.op.eval [false] = true at hn
      rw [ha] at hn
      exact Bool.noConfusion hn
    · change g.op.eval [false] = true at hn
      rw [ho] at hn
      exact Bool.noConfusion hn
    · exact ht
  have step_le (g : Gate) (h : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp))
      (hn : neg g = false) (a b : List Bool) (ab : agrees a b) :
      agrees (step a g) (step b g) := by
    apply append_le _ _ ab
    rcases op_cases g h with ha | ho | ht
    · rw [ha]
      exact all_le g.inputs a b ab
    · rw [ho]
      exact any_le g.inputs a b ab
    · change g.op.eval [false] = false at hn
      rw [ht] at hn
      exact Bool.noConfusion hn
  have run_le (gs : List Gate) (h : FanInTwo ⟨gs, 0⟩)
      (hn : ∀ g ∈ gs, neg g = false) (a b : List Bool) (ab : agrees a b) :
      agrees (gs.foldl step a) (gs.foldl step b) := by
    induction gs generalizing a b with
    | nil => exact ab
    | cons g gs ih =>
      exact ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
        (fun g' hg' => hn g' (List.mem_cons_of_mem _ hg'))
        _ _ (step_le g (h g (by simp)).1 (hn g (by simp)) a b ab)
  have run_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have pad_length (x : Fin 9 → Bool) : (pad x).length = 10 := by simp [pad]
  let first : Gate := ⟨.or, [4, 6]⟩
  have eval_first (x : Fin 9 → Bool) : step (List.ofFn x) first = pad x := by
    have read (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    change List.ofFn x ++
      [((List.ofFn x).getD 4 false || ((List.ofFn x).getD 6 false || false))] = pad x
    have h4 : (List.ofFn x).getD 4 false = x 4 := read 4
    have h6 : (List.ofFn x).getD 6 false = x 6 := read 6
    rw [h4, h6, Bool.or_false]
  have hfirst : first.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ first.inputs.length ≤ 2 := by
    change GateOp.or ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ [4, 6].length ≤ 2
    simp
  have no_few_inverters (gs : List Gate) (j : Nat) (hlen : gs.length ≤ 13)
      (hfan : FanInTwo ⟨gs, 0⟩) (hc : gs.countP neg < 2)
      (target : ∀ x : Fin 9 → Bool, (gs.foldl step (pad x)).getD j false = !edge x) : False := by
    by_cases hasNeg : ∃ g ∈ gs, neg g = true
    · obtain ⟨g, hg, hneg⟩ := hasNeg
      have hop := neg_op g (hfan g hg).1 hneg
      obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
      have counts : pre.countP neg + (post.countP neg + 1) < 2 := by
        simpa only [hsplit, List.countP_append, List.countP_cons_of_pos hneg] using hc
      have preNo : ∀ t ∈ pre, neg t = false := by
        have hz := List.countP_eq_zero.mp (show pre.countP neg = 0 by omega)
        intro t ht
        cases he : neg t
        · rfl
        · exact (hz t ht he).elim
      have postNo : ∀ t ∈ post, neg t = false := by
        have hz := List.countP_eq_zero.mp (show post.countP neg = 0 by omega)
        intro t ht
        cases he : neg t
        · rfl
        · exact (hz t ht he).elim
      have preFan : FanInTwo ⟨pre, 0⟩ := fun t ht => hfan t (by rw [hsplit]; simp [ht])
      have postFan : FanInTwo ⟨post, 0⟩ := fun t ht => hfan t (by rw [hsplit]; simp [ht])
      let before (x : Fin 9 → Bool) := pre.foldl step (pad x)
      let pin := g.inputs.headD (10 + pre.length)
      let H (x : Fin 9 → Bool) := (before x).getD pin false
      have gateVal (x : Fin 9 → Bool) : step (before x) g = before x ++ [!H x] := by
        change before x ++ [g.op.eval (g.inputs.map fun i => (before x).getD i false)] = _
        rw [hop]
        cases hi : g.inputs with
        | nil =>
          have hv : H x = false := by
            change (before x).getD (g.inputs.headD (10 + pre.length)) false = false
            rw [hi]
            apply List.getD_eq_default
            change (before x).length ≤ 10 + pre.length
            rw [run_length, pad_length]
          rw [hv]
          rfl
        | cons i is =>
          change before x ++ [!(before x).getD i false] =
            before x ++ [!((before x).getD (g.inputs.headD (10 + pre.length)) false)]
          rw [hi]
          rfl
      let tail (x : Fin 9 → Bool) (b : Bool) :=
        (post.foldl step (before x ++ [b])).getD j false
      have value (x : Fin 9 → Bool) : tail x (!H x) = !edge x := by
        have eq := target x
        rw [hsplit, List.foldl_append, List.foldl_cons] at eq
        change (post.foldl step (step (before x) g)).getD j false = !edge x at eq
        rwa [gateVal] at eq
      have tail_mono (x y : Fin 9 → Bool) (xy : agrees (pad x) (pad y)) (b : Bool) :
          tail x b ≤ tail y b := by
        have beforeLE := run_le pre preFan preNo _ _ xy
        exact (run_le post postFan postNo _ _
          (append_le _ _ beforeLE b b (le_refl _))).2 j
      have HbHt : H bottom ≤ H top := (run_le pre preFan preNo _ _ (low top)).2 pin
      have diff : H bottom ≠ H top := by
        intro same
        have h := tail_mono bottom top (low top) (!H bottom)
        rw [value bottom, same, value top, edge_bottom, edge_top] at h
        exact (by decide : ¬ ((!false) ≤ (!true))) h
      have endpoints : H bottom = false ∧ H top = true := by
        cases hb : H bottom <;> cases ht : H top
        · exact (diff (hb.trans ht.symm)).elim
        · exact ⟨rfl, rfl⟩
        · have h := HbHt
          rw [hb, ht] at h
          exact ((by decide : ¬ (true ≤ false)) h).elim
        · exact (diff (hb.trans ht.symm)).elim
      obtain ⟨loH, hiH⟩ := endpoints
      have evaluates (x : Fin 9 → Bool) : H x = edge x := by
        cases hx : H x with
        | false =>
          have h := tail_mono bottom x (low x) true
          have a := value bottom
          have b := value x
          rw [loH, edge_bottom] at a
          rw [hx] at b
          change tail bottom true = true at a
          change tail x true = !edge x at b
          rw [a, b] at h
          cases he : edge x
          · rfl
          · rw [he] at h
            exact ((by decide : ¬ (true ≤ !true)) h).elim
        | true =>
          have h := tail_mono x top (high x) false
          have a := value x
          have b := value top
          rw [hx] at a
          rw [hiH, edge_top] at b
          change tail x false = !edge x at a
          change tail top false = false at b
          rw [a, b] at h
          cases he : edge x
          · rw [he] at h
            exact ((by decide : ¬ ((!false) ≤ false)) h).elim
          · rfl
      have preBound : pre.length ≤ 12 := by
        rw [hsplit,List.length_append,List.length_cons] at hlen
        omega
      obtain ⟨x,hx,miss⟩ := cofactor pre pin preBound preFan
      apply miss
      exact (evaluates x).trans (by simp only [edge_form,hx,Bool.and_false,Bool.false_and,Bool.or_false])
    · have hn : ∀ g ∈ gs, neg g = false := by
        intro g hg
        cases he : neg g
        · rfl
        · exact (hasNeg ⟨g, hg, he⟩).elim
      have h := (run_le gs hfan hn _ _ (low top)).2 j
      rw [target bottom, target top, edge_bottom, edge_top] at h
      exact (by decide : ¬ ((!false) ≤ (!true))) h
  intro gs pins hlen hfan _ _
  by_contra! eq
  cases pins with
  | nil =>
    have h := not_not.mp (eq bottom)
    change true = _ at h
    rw [← edge_form, edge_bottom] at h
    exact Bool.noConfusion h
  | cons pin rest =>
    have target (x : Fin 9 → Bool) : (gs.foldl step (pad x)).getD pin.val false = !edge x := by
      have h := not_not.mp (eq x)
      change (!((gs.foldl step (pad x)).getD pin.val false)) = _ at h
      rw [← edge_form] at h
      rw [← h, Bool.not_not]
    by_cases many : 2 ≤ gs.countP neg
    · let out : Gate := ⟨.not, [pin.val]⟩
      let C : Circuit := ⟨(first :: gs) ++ [out],10 + gs.length⟩
      have fan : FanInTwo C := by
        intro g hg
        change g ∈ (first :: gs) ++ [out] at hg
        rcases List.mem_append.mp hg with hg | hg
        · rcases List.mem_cons.mp hg with rfl | hg
          · exact hfirst
          · exact hfan g hg
        · have e := List.mem_singleton.mp hg
          subst g
          change GateOp.not ∈ ({GateOp.and,.or,.not} : Set GateOp) ∧ [pin.val].length ≤ 2
          simp
      have parts (l : List Gate) : l.countP (fun g => !(neg g)) + l.countP neg = l.length := by
        induction l with
        | nil => rfl
        | cons g l ih =>
          simp only [List.countP_cons,List.length_cons]
          cases neg g <;> simp <;> omega
      have cost : C.gates.countP (fun g => !(g.op.eval [false])) ≤ 12 := by
        change ((first :: gs) ++ [out]).countP (fun g => !(neg g)) ≤ 12
        rw [List.countP_append,List.countP_cons]
        have head : neg first = false := rfl
        simp only [head,Bool.not_false,ite_true]
        have finish : [out].countP (fun g => !(neg g)) = 0 := rfl
        rw [finish]
        have budget := parts gs
        omega
      obtain ⟨x,miss⟩ := binary C fan cost
      apply miss
      have run : (gs.foldl step (pad x)).length = 10 + gs.length := by
        rw [run_length,pad_length]
      change (((first :: gs) ++ [out]).foldl step (List.ofFn x)).getD
        (10 + gs.length) false = _
      rw [List.foldl_append]
      simp only [List.foldl_cons,List.foldl_nil]
      rw [eval_first]
      change ((gs.foldl step (pad x)) ++ [!((gs.foldl step (pad x)).getD pin.val false)]).getD
        (10 + gs.length) false = _
      rw [← run]
      simp only [List.getD_append_right _ _ _ _ (by omega : (gs.foldl step (pad x)).length ≤
        (gs.foldl step (pad x)).length),Nat.sub_self,List.getD_cons_zero]
      rw [target x,Bool.not_not]
      exact edge_form x
    · exact no_few_inverters gs pin.val hlen hfan (by omega) target
