import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_3563_1
    (theta : ¬HasCircuitSize 7 (fun y : Fin 7 → Bool => y 0 && y 1 || y 1 && y 2 ||
      y 0 && y 4 || y 1 && y 5 || y 2 && y 6 || y 3 && y 5 || y 4 && y 6 || y 6 && y 3) 10)
    (few : ∀ k : Fin 9, (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      C.gates.countP (fun g => (g.inputs.take
        (if g.op.eval [false, true] = g.op.eval [true, false] then 2 else 1)).any
          fun i => i == 0 || i == 4 || i == 9) ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [false, x 0 || x 4 || x k]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : Fin (9 : ℕ)), x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (2 : Fin (9 : ℕ)) ∨ x2 = (3 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [Bool.false, x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) || x7 x2]) = x1 x7) → False := by
  intro f k hk C fan size hev
  let P : Gate → Bool := fun g => (g.inputs.take
    (if g.op.eval [false, true] = g.op.eval [true, false] then 2 else 1)).any
      fun i => i == 0 || i == 4 || i == 9
  by_cases hcnt : C.gates.countP P ≤ 2
  · exact few k hk C fan size hcnt hev
  have hcnt3 : 3 ≤ C.gates.countP P := by omega
  let θ : (Fin 7 → Bool) → Bool := fun y => y 0 && y 1 || y 1 && y 2 || y 0 && y 4 ||
    y 1 && y 5 || y 2 && y 6 || y 3 && y 5 || y 4 && y 6 || y 6 && y 3
  let val : (Bool ⊕ ℕ) → List Bool → Bool := fun s v =>
    Sum.elim (fun c => c) (fun j => v.getD j false) s
  let nw : List Gate → List Bool → List Bool := fun gs w => (Circuit.mk gs 0).wires w
  let OK : Gate → Prop := fun g =>
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  let Inv : List (Bool ⊕ ℕ) → List Gate → ((Fin 7 → Bool) → List Bool) → Prop :=
    fun σ ngs W =>
      (∀ y, (W y).length = σ.length) ∧
      (∀ y i, val (σ.getD i (Sum.inl false)) (nw ngs (List.ofFn y)) = (W y).getD i false) ∧
      (∀ i j, σ.getD i (Sum.inl false) = Sum.inr j → j < 7 + ngs.length) ∧
      (∀ g ∈ ngs, OK g) ∧
      (∀ i, (i = 0 ∨ i = 4 ∨ i = 9) → ∃ c, σ.getD i (Sum.inl false) = Sum.inl c) ∧
      10 ≤ σ.length
  have evAnd : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have evOr : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have evNot : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have wires_def : ∀ (D : Circuit) (x : List Bool), D.wires x = D.gates.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := fun _ _ => rfl
  have snoc_eq : ∀ (L : List (Bool ⊕ ℕ)) (S d : Bool ⊕ ℕ), (L ++ [S]).getD L.length d = S := by
    intro L S d; simp
  have nw_snoc : ∀ (gs : List Gate) (g : Gate) (w : List Bool),
      nw (gs ++ [g]) w = nw gs w ++ [g.op.eval (g.inputs.map fun i => (nw gs w).getD i false)] := by
    intro gs g w
    simp only [nw, wires_def, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have nw_len : ∀ (gs : List Gate) (w : List Bool), (nw gs w).length = w.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro w; simp [nw, wires_def]
    | append_singleton gs g ih =>
      intro w
      rw [nw_snoc, List.length_append, ih]
      simp only [List.length_singleton, List.length_append]
      omega
  -- a gate with a constant input is a constant or a copy of one of its inputs
  have simpStat : ∀ (op : GateOp) (st : List (Bool ⊕ ℕ)),
      (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) → st.length ≤ 2 →
      (op = GateOp.not → st.length ≤ 1) → (∃ c, Sum.inl c ∈ st) →
      ∃ s, (s ∈ st ∨ ∃ c, s = Sum.inl c) ∧
        ∀ v, val s v = op.eval (st.map fun t => val t v) := by
    intro op st hop hlen hnot hc
    rcases hop with rfl | rfl | rfl
    · rcases st with _ | ⟨a, _ | ⟨b, _ | ⟨e, l⟩⟩⟩
      · simp at hc
      · obtain ⟨c, hc⟩ := hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨Sum.inl c, Or.inr ⟨c, rfl⟩, fun v => by simp [val, evAnd, evOr, evNot]⟩
      · obtain ⟨c, hc⟩ := hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · cases c
          · exact ⟨Sum.inl false, Or.inr ⟨false, rfl⟩, fun v => by simp [val, evAnd, evOr, evNot]⟩
          · exact ⟨b, Or.inl (by simp), fun v => by simp [val, evAnd, evOr, evNot]⟩
        · cases c
          · exact ⟨Sum.inl false, Or.inr ⟨false, rfl⟩, fun v => by simp [val, evAnd, evOr, evNot]⟩
          · exact ⟨a, Or.inl (by simp), fun v => by simp [val, evAnd, evOr, evNot]⟩
      · simp at hlen
    · rcases st with _ | ⟨a, _ | ⟨b, _ | ⟨e, l⟩⟩⟩
      · simp at hc
      · obtain ⟨c, hc⟩ := hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨Sum.inl c, Or.inr ⟨c, rfl⟩, fun v => by simp [val, evAnd, evOr, evNot]⟩
      · obtain ⟨c, hc⟩ := hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · cases c
          · exact ⟨b, Or.inl (by simp), fun v => by simp [val, evAnd, evOr, evNot]⟩
          · exact ⟨Sum.inl true, Or.inr ⟨true, rfl⟩, fun v => by simp [val, evAnd, evOr, evNot]⟩
        · cases c
          · exact ⟨a, Or.inl (by simp), fun v => by simp [val, evAnd, evOr, evNot]⟩
          · exact ⟨Sum.inl true, Or.inr ⟨true, rfl⟩, fun v => by simp [val, evAnd, evOr, evNot]⟩
      · simp at hlen
    · rcases st with _ | ⟨a, _ | ⟨b, l⟩⟩
      · simp at hc
      · obtain ⟨c, hc⟩ := hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨Sum.inl (!c), Or.inr ⟨!c, rfl⟩, fun v => by simp [val, evAnd, evOr, evNot]⟩
      · simp at hnot
  -- one gate of the old circuit
  have step : ∀ (g : Gate) (σ : List (Bool ⊕ ℕ)) (ngs : List Gate)
      (W : (Fin 7 → Bool) → List Bool), OK g → Inv σ ngs W →
      ∃ σ' ngs', Inv σ' ngs'
          (fun y => W y ++ [g.op.eval (g.inputs.map fun i => (W y).getD i false)]) ∧
        ngs'.length + (if P g = true then 1 else 0) ≤ ngs.length + 1 := by
    intro g σ ngs W hg hinv
    obtain ⟨hlen, hval, hbnd, hok, hconst, h10⟩ := hinv
    obtain ⟨hop, hfan⟩ := hg
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      simpa using hop
    set n := (if g.op.eval [false, true] = g.op.eval [true, false] then 2 else 1) with hn
    set ins := g.inputs.take n with hins
    have hn2 : g.op = GateOp.and ∨ g.op = GateOp.or → n = 2 := by
      rintro (h | h) <;> simp [hn, h, evAnd, evOr, evNot]
    have hn1 : g.op = GateOp.not → n = 1 := by
      intro h; simp [hn, h, evAnd, evOr, evNot]
    have hevalIns : ∀ F : ℕ → Bool, g.op.eval (g.inputs.map F) = g.op.eval (ins.map F) := by
      intro F
      rcases hop' with h | h | h
      · rw [hins, hn2 (Or.inl h), List.take_of_length_le hfan]
      · rw [hins, hn2 (Or.inr h), List.take_of_length_le hfan]
      · rw [hins, hn1 h, h]
        rcases g.inputs with _ | ⟨a, l⟩ <;> simp [evAnd, evOr, evNot]
    have hinsLen : ins.length ≤ 2 := by
      rw [hins, List.length_take]; omega
    have hinsNot : g.op = GateOp.not → ins.length ≤ 1 := by
      intro h
      rw [hins, List.length_take, hn1 h]; omega
    set st := ins.map fun i => σ.getD i (Sum.inl false) with hst
    have hstLen : st.length = ins.length := by rw [hst, List.length_map]
    have gateVal : ∀ y, g.op.eval (g.inputs.map fun i => (W y).getD i false)
        = g.op.eval (st.map fun t => val t (nw ngs (List.ofFn y))) := by
      intro y
      rw [hevalIns, hst, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (hval y i).symm
    have nwlen : ∀ y : Fin 7 → Bool, (nw ngs (List.ofFn y)).length = 7 + ngs.length := by
      intro y; rw [nw_len]; simp
    have old_short : ∀ i, i < σ.length → (σ ++ [Sum.inr (7 + ngs.length)]).getD i (Sum.inl false)
        = σ.getD i (Sum.inl false) := by
      intro i hi; exact List.getD_append _ _ _ _ hi
    by_cases hc : ∃ c, Sum.inl c ∈ st
    · -- a constant input: the gate is dropped
      obtain ⟨s, hs, hsv⟩ := simpStat g.op st hop' (by omega) (fun h => by
        have := hinsNot h; omega) hc
      refine ⟨σ ++ [s], ngs, ⟨?_, ?_, ?_, hok, ?_, ?_⟩, ?_⟩
      · intro y; simp [hlen y]
      · intro y i
        rcases lt_trichotomy i σ.length with hi | hi | hi
        · rw [List.getD_append _ _ _ _ hi,
            List.getD_append _ _ _ _ (by rw [hlen y]; exact hi)]
          exact hval y i
        · subst hi
          rw [snoc_eq]
          have e : (W y ++ [g.op.eval (g.inputs.map fun i => (W y).getD i false)]).getD
              σ.length false = g.op.eval (g.inputs.map fun i => (W y).getD i false) := by
            rw [← hlen y]; simp
          rw [e, hsv, gateVal]
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp [hlen y]; omega)]
          rfl
      · intro i j hij
        rcases lt_trichotomy i σ.length with hi | hi | hi
        · rw [List.getD_append _ _ _ _ hi] at hij
          exact hbnd i j hij
        · subst hi
          rw [snoc_eq] at hij
          subst hij
          rcases hs with hs | ⟨c, hc'⟩
          · obtain ⟨i', _, hi'⟩ := List.mem_map.1 hs
            exact hbnd i' j hi'
          · cases hc'
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hij
          cases hij
      · intro i hi
        have hi' : i < σ.length := by rcases hi with rfl | rfl | rfl <;> omega
        rw [List.getD_append _ _ _ _ hi']
        exact hconst i hi
      · simp; omega
      · split_ifs <;> omega
    · -- every input is a wire: the gate is kept
      have hwire : ∀ t ∈ st, ∃ j, t = Sum.inr j := by
        intro t ht
        cases t with
        | inl c => exact absurd ⟨c, ht⟩ hc
        | inr j => exact ⟨j, rfl⟩
      let g' : Gate := ⟨g.op, st.map (Sum.elim (fun _ => 0) id)⟩
      refine ⟨σ ++ [Sum.inr (7 + ngs.length)], ngs ++ [g'], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro y; simp [hlen y]
      · intro y i
        rcases lt_trichotomy i σ.length with hi | hi | hi
        · rw [old_short i hi,
            List.getD_append _ _ _ _ (by rw [hlen y]; exact hi), ← hval y i]
          cases hsi : σ.getD i (Sum.inl false) with
          | inl c => rfl
          | inr j =>
            have hj := hbnd i j hsi
            change (nw (ngs ++ [g']) (List.ofFn y)).getD j false
              = (nw ngs (List.ofFn y)).getD j false
            rw [nw_snoc, List.getD_append _ _ _ _ (by rw [nwlen y]; exact hj)]
        · subst hi
          rw [snoc_eq]
          have e : (W y ++ [g.op.eval (g.inputs.map fun i => (W y).getD i false)]).getD
              σ.length false = g.op.eval (g.inputs.map fun i => (W y).getD i false) := by
            rw [← hlen y]; simp
          rw [e, gateVal]
          change (nw (ngs ++ [g']) (List.ofFn y)).getD (7 + ngs.length) false = _
          rw [nw_snoc, ← nwlen y]
          simp only [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
            List.getD_cons_zero]
          change g.op.eval ((st.map (Sum.elim (fun _ => 0) id)).map
            fun i => (nw ngs (List.ofFn y)).getD i false) = _
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro t ht
          obtain ⟨j, rfl⟩ := hwire t ht
          rfl
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp [hlen y]; omega)]
          rfl
      · intro i j hij
        rcases lt_trichotomy i σ.length with hi | hi | hi
        · rw [old_short i hi] at hij
          have := hbnd i j hij
          simp only [List.length_append, List.length_singleton]
          omega
        · subst hi
          rw [snoc_eq] at hij
          cases hij
          simp
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hij
          cases hij
      · intro g'' hg''
        rcases List.mem_append.1 hg'' with h | h
        · exact hok g'' h
        · rw [List.mem_singleton] at h
          subst h
          refine ⟨hop, ?_⟩
          change (st.map (Sum.elim (fun _ => 0) id)).length ≤ 2
          rw [List.length_map]; omega
      · intro i hi
        have hi' : i < σ.length := by rcases hi with rfl | rfl | rfl <;> omega
        rw [old_short i hi']
        exact hconst i hi
      · simp; omega
      · have hP : P g = false := by
          by_contra hP
          rw [Bool.not_eq_false] at hP
          obtain ⟨i, hi, hi'⟩ := List.any_eq_true.1 hP
          have hi049 : i = 0 ∨ i = 4 ∨ i = 9 := by
            simp only [Bool.or_eq_true, beq_iff_eq] at hi'
            rcases hi' with (h | h) | h <;> simp [h]
          obtain ⟨c, hc'⟩ := hconst i hi049
          exact hc ⟨c, hc' ▸ List.mem_map.2 ⟨i, hi, rfl⟩⟩
        rw [hP]
        simp
  -- all the gates
  have fold : ∀ (gs : List Gate) (σ : List (Bool ⊕ ℕ)) (ngs : List Gate)
      (W : (Fin 7 → Bool) → List Bool), (∀ g ∈ gs, OK g) → Inv σ ngs W →
      ∃ σ' ngs', Inv σ' ngs' (fun y => gs.foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W y)) ∧
        ngs'.length + gs.countP P ≤ ngs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro σ ngs W _ h; exact ⟨σ, ngs, h, by simp⟩
    | cons g gs ih =>
      intro σ ngs W hok h
      obtain ⟨σ1, ngs1, h1, c1⟩ := step g σ ngs W (hok g List.mem_cons_self) h
      obtain ⟨σ2, ngs2, h2, c2⟩ :=
        ih σ1 ngs1 _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) h1
      refine ⟨σ2, ngs2, h2, ?_⟩
      rw [List.countP_cons, List.length_cons]
      split_ifs at c1 ⊢ <;> omega
  -- the end: a circuit for the theta graph with at most 10 gates
  have finish : ∀ (σ0 : List (Bool ⊕ ℕ)) (W0 : (Fin 7 → Bool) → List Bool),
      Inv σ0 [] W0 → (∀ y, C.eval (W0 y) = θ y) → False := by
    intro σ0 W0 h0 hW
    obtain ⟨σ', ngs', h', hcount⟩ := fold C.gates σ0 [] W0 (fun g hg => fan g hg) h0
    obtain ⟨_, hval', _, hok', _, _⟩ := h'
    have hsz : ngs'.length ≤ 10 := by
      have : C.gates.length ≤ 13 := size
      simp only [List.length_nil, zero_add] at hcount
      omega
    have hout : ∀ y, val (σ'.getD C.output (Sum.inl false)) (nw ngs' (List.ofFn y)) = θ y := by
      intro y; rw [hval' y C.output]; exact hW y
    cases hso : σ'.getD C.output (Sum.inl false) with
    | inl c =>
      have h1 := hout (fun _ => false)
      have h2 := hout (fun i => decide (i = 0 ∨ i = 1))
      rw [hso] at h1 h2
      simp [val, θ] at h1 h2
      rw [h1] at h2
      exact Bool.false_ne_true h2
    | inr j =>
      apply theta
      refine ⟨⟨ngs', j⟩, fun g hg => hok' g hg, hsz, ?_⟩
      intro y
      have := hout y
      rw [hso] at this
      exact this
  -- the start: fix x0 = x4 = 0; the wire of the OR becomes a copy of x_k
  have ofFnGet : ∀ (y : Fin 7 → Bool) (j : Fin 7), (List.ofFn y).getD j.val false = y j := by
    intro y j
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  obtain ⟨t, ht⟩ : ∃ t : Fin 7, ∀ y : Fin 7 → Bool,
      ((![false, y 0, y 1, y 2, false, y 3, y 4, y 5, y 6] : Fin 9 → Bool) 0 ||
        (![false, y 0, y 1, y 2, false, y 3, y 4, y 5, y 6] : Fin 9 → Bool) 4 ||
        (![false, y 0, y 1, y 2, false, y 3, y 4, y 5, y 6] : Fin 9 → Bool) k) = y t := by
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨0, fun y => by simp⟩
    · exact ⟨1, fun y => by simp⟩
    · exact ⟨2, fun y => by simp⟩
    · exact ⟨4, fun y => by simp⟩
  apply finish
    [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl false, Sum.inr 3, Sum.inr 4,
      Sum.inr 5, Sum.inr 6, Sum.inl false, Sum.inr t.val]
    (fun y => [false, y 0, y 1, y 2, false, y 3, y 4, y 5, y 6, false, y t])
  · refine ⟨fun y => rfl, ?_, ?_, fun g hg => by simp at hg, ?_, by simp⟩
    · intro y i
      rcases lt_or_ge i 11 with hi | hi
      · interval_cases i
        all_goals first
          | rfl
          | exact ofFnGet y t
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
        rfl
    · intro i j hij
      rcases lt_or_ge i 11 with hi | hi
      · interval_cases i <;> simp at hij <;> omega
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hij
        cases hij
    · intro i hi
      rcases hi with rfl | rfl | rfl <;> exact ⟨false, rfl⟩
  · intro y
    have e := hev ![false, y 0, y 1, y 2, false, y 3, y 4, y 5, y 6]
    rw [ht y] at e
    have hl : List.ofFn (![false, y 0, y 1, y 2, false, y 3, y 4, y 5, y 6] : Fin 9 → Bool) ++
        [false, y t] = [false, y 0, y 1, y 2, false, y 3, y 4, y 5, y 6, false, y t] := by
      simp [List.ofFn_succ]
    rw [hl] at e
    rw [e]
    simp only [f, θ]
    simp
