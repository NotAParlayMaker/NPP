import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3655

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

def CC : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 38] }], output := 46 }

def t0 (x : Fin 14 → Bool) : Bool := x 0 && (x 7 || x 11 || x 13)
def t1 (x : Fin 14 → Bool) : Bool := x 1 && (x 7 || x 8 || x 12)
def t2 (x : Fin 14 → Bool) : Bool := x 2 && (x 8 || x 9 || x 13)
def t3 (x : Fin 14 → Bool) : Bool := x 3 && (x 7 || x 9 || x 10)
def t4 (x : Fin 14 → Bool) : Bool := x 4 && (x 8 || x 10 || x 11)
def t5 (x : Fin 14 → Bool) : Bool := x 5 && (x 9 || x 11 || x 12)
def t6 (x : Fin 14 → Bool) : Bool := x 6 && (x 10 || x 12 || x 13)

def f (x : Fin 14 → Bool) : Bool :=
  t0 x || (t1 x || (t2 x || (t3 x || (t4 x || (t5 x || t6 x)))))

def Inc (x : Fin 14 → Bool) : Prop := ∃ p l : Fin 7,
  (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true

abbrev GG : SimpleGraph (Fin 14) := SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7,
  (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧
    ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)

theorem f_iff (x : Fin 14 → Bool) : f x = true ↔ t0 x = true ∨ t1 x = true ∨ t2 x = true ∨
    t3 x = true ∨ t4 x = true ∨ t5 x = true ∨ t6 x = true := by
  simp only [f, Bool.or_eq_true]

theorem t0_iff (x : Fin 14 → Bool) : t0 x = true ↔
    x 0 = true ∧ (x 7 = true ∨ x 11 = true ∨ x 13 = true) := by
  simp only [t0, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem t1_iff (x : Fin 14 → Bool) : t1 x = true ↔
    x 1 = true ∧ (x 7 = true ∨ x 8 = true ∨ x 12 = true) := by
  simp only [t1, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem t2_iff (x : Fin 14 → Bool) : t2 x = true ↔
    x 2 = true ∧ (x 8 = true ∨ x 9 = true ∨ x 13 = true) := by
  simp only [t2, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem t3_iff (x : Fin 14 → Bool) : t3 x = true ↔
    x 3 = true ∧ (x 7 = true ∨ x 9 = true ∨ x 10 = true) := by
  simp only [t3, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem t4_iff (x : Fin 14 → Bool) : t4 x = true ↔
    x 4 = true ∧ (x 8 = true ∨ x 10 = true ∨ x 11 = true) := by
  simp only [t4, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem t5_iff (x : Fin 14 → Bool) : t5 x = true ↔
    x 5 = true ∧ (x 9 = true ∨ x 11 = true ∨ x 12 = true) := by
  simp only [t5, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem t6_iff (x : Fin 14 → Bool) : t6 x = true ↔
    x 6 = true ∧ (x 10 = true ∨ x 12 = true ∨ x 13 = true) := by
  simp only [t6, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem Inc_iff (x : Fin 14 → Bool) : Inc x ↔ f x = true := by
  constructor
  · rintro ⟨p, l, h, hp, hl⟩
    rw [f_iff, t0_iff, t1_iff, t2_iff, t3_iff, t4_iff, t5_iff, t6_iff]
    fin_cases p <;> fin_cases l <;> first
      | (exfalso; revert h; decide)
      | exact Or.inl ⟨hp, Or.inl hl⟩
      | exact Or.inl ⟨hp, Or.inr (Or.inl hl)⟩
      | exact Or.inl ⟨hp, Or.inr (Or.inr hl)⟩
      | exact Or.inr (Or.inl ⟨hp, Or.inl hl⟩)
      | exact Or.inr (Or.inl ⟨hp, Or.inr (Or.inl hl)⟩)
      | exact Or.inr (Or.inl ⟨hp, Or.inr (Or.inr hl)⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hp, Or.inl hl⟩))
      | exact Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inl hl)⟩))
      | exact Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inr hl)⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inl hl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inl hl)⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inr hl)⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inl hl⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inl hl)⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inr hl)⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inl hl⟩)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inl hl)⟩)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, Or.inr (Or.inr hl)⟩)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hp, Or.inl hl⟩))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hp, Or.inr (Or.inl hl)⟩))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hp, Or.inr (Or.inr hl)⟩))))))
  · rw [f_iff, t0_iff, t1_iff, t2_iff, t3_iff, t4_iff, t5_iff, t6_iff]
    rintro (⟨hp, hl | hl | hl⟩ | ⟨hp, hl | hl | hl⟩ | ⟨hp, hl | hl | hl⟩ | ⟨hp, hl | hl | hl⟩ | ⟨hp, hl | hl | hl⟩ | ⟨hp, hl | hl | hl⟩ | ⟨hp, hl | hl | hl⟩)
    · exact ⟨0, 0, by decide, hp, hl⟩
    · exact ⟨0, 4, by decide, hp, hl⟩
    · exact ⟨0, 6, by decide, hp, hl⟩
    · exact ⟨1, 0, by decide, hp, hl⟩
    · exact ⟨1, 1, by decide, hp, hl⟩
    · exact ⟨1, 5, by decide, hp, hl⟩
    · exact ⟨2, 1, by decide, hp, hl⟩
    · exact ⟨2, 2, by decide, hp, hl⟩
    · exact ⟨2, 6, by decide, hp, hl⟩
    · exact ⟨3, 0, by decide, hp, hl⟩
    · exact ⟨3, 2, by decide, hp, hl⟩
    · exact ⟨3, 3, by decide, hp, hl⟩
    · exact ⟨4, 1, by decide, hp, hl⟩
    · exact ⟨4, 3, by decide, hp, hl⟩
    · exact ⟨4, 4, by decide, hp, hl⟩
    · exact ⟨5, 2, by decide, hp, hl⟩
    · exact ⟨5, 4, by decide, hp, hl⟩
    · exact ⟨5, 5, by decide, hp, hl⟩
    · exact ⟨6, 3, by decide, hp, hl⟩
    · exact ⟨6, 5, by decide, hp, hl⟩
    · exact ⟨6, 6, by decide, hp, hl⟩

theorem gf (d : DecidableRel GG.Adj) (x : Fin 14 → Bool) :
    @graphFun 14 GG d ∅ x = true ↔ f x = true := by
  rw [← Inc_iff]
  unfold graphFun
  rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro (⟨a, ha, _⟩ | ⟨u, v, hadj, hu, hv⟩)
    · exact absurd ha (Finset.notMem_empty a)
    · rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with ⟨p, l, h, rfl, rfl⟩ | ⟨p, l, h, rfl, rfl⟩
      · exact ⟨p, l, h, hu, hv⟩
      · exact ⟨p, l, h, hv, hu⟩
  · rintro ⟨p, l, h, hp, hl⟩
    refine Or.inr ⟨_, _, ?_, hp, hl⟩
    rw [SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨p, l, h, rfl, rfl⟩⟩
    intro e
    have := congrArg Fin.val e
    rw [Fin.val_castAdd, Fin.val_natAdd] at this
    omega

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2


theorem wor (x : Fin 14 → Bool) (r a b : ℕ) (hr : r < CC.gates.length)
    (hg : gateAt CC r = ⟨GateOp.or, [a, b]⟩) (ha : a < 14 + r) (hb : b < 14 + r) :
    wval CC x (14 + r) = true ↔ wval CC x a = true ∨ wval CC x b = true := by
  refine (val_or (C := CC) (x := List.ofFn x) (n := 14) List.length_ofFn hr (by rw [hg])).trans ?_
  rw [hg]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, ha, hb,
    true_and]
  exact Iff.rfl

theorem wand (x : Fin 14 → Bool) (r a b : ℕ) (hr : r < CC.gates.length)
    (hg : gateAt CC r = ⟨GateOp.and, [a, b]⟩) (ha : a < 14 + r) (hb : b < 14 + r) :
    wval CC x (14 + r) = true ↔ wval CC x a = true ∧ wval CC x b = true := by
  refine (val_and (C := CC) (x := List.ofFn x) (n := 14) List.length_ofFn hr (by rw [hg])).trans ?_
  rw [hg]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ha, hb,
    true_and]
  exact Iff.rfl

theorem wi (x : Fin 14 → Bool) (i : Fin 14) : wval CC x i.val = x i := by
  refine (val_input (C := CC) (x := List.ofFn x) (n := 14) List.length_ofFn i.isLt).trans ?_
  fin_cases i <;> rfl

theorem w0 (x : Fin 14 → Bool) : wval CC x 0 = x 0 := wi x 0
theorem w1 (x : Fin 14 → Bool) : wval CC x 1 = x 1 := wi x 1
theorem w2 (x : Fin 14 → Bool) : wval CC x 2 = x 2 := wi x 2
theorem w3 (x : Fin 14 → Bool) : wval CC x 3 = x 3 := wi x 3
theorem w4 (x : Fin 14 → Bool) : wval CC x 4 = x 4 := wi x 4
theorem w5 (x : Fin 14 → Bool) : wval CC x 5 = x 5 := wi x 5
theorem w6 (x : Fin 14 → Bool) : wval CC x 6 = x 6 := wi x 6
theorem w7 (x : Fin 14 → Bool) : wval CC x 7 = x 7 := wi x 7
theorem w8 (x : Fin 14 → Bool) : wval CC x 8 = x 8 := wi x 8
theorem w9 (x : Fin 14 → Bool) : wval CC x 9 = x 9 := wi x 9
theorem w10 (x : Fin 14 → Bool) : wval CC x 10 = x 10 := wi x 10
theorem w11 (x : Fin 14 → Bool) : wval CC x 11 = x 11 := wi x 11
theorem w12 (x : Fin 14 → Bool) : wval CC x 12 = x 12 := wi x 12
theorem w13 (x : Fin 14 → Bool) : wval CC x 13 = x 13 := wi x 13
theorem w14 (x : Fin 14 → Bool) :
    wval CC x 14 = true ↔ wval CC x 7 = true ∨ wval CC x 8 = true :=
  wor x 0 7 8 (by decide) rfl (by decide) (by decide)
theorem w15 (x : Fin 14 → Bool) :
    wval CC x 15 = true ↔ wval CC x 14 = true ∨ wval CC x 12 = true :=
  wor x 1 14 12 (by decide) rfl (by decide) (by decide)
theorem w16 (x : Fin 14 → Bool) :
    wval CC x 16 = true ↔ wval CC x 1 = true ∧ wval CC x 15 = true :=
  wand x 2 1 15 (by decide) rfl (by decide) (by decide)
theorem w17 (x : Fin 14 → Bool) :
    wval CC x 17 = true ↔ wval CC x 8 = true ∨ wval CC x 9 = true :=
  wor x 3 8 9 (by decide) rfl (by decide) (by decide)
theorem w18 (x : Fin 14 → Bool) :
    wval CC x 18 = true ↔ wval CC x 17 = true ∨ wval CC x 13 = true :=
  wor x 4 17 13 (by decide) rfl (by decide) (by decide)
theorem w19 (x : Fin 14 → Bool) :
    wval CC x 19 = true ↔ wval CC x 2 = true ∧ wval CC x 18 = true :=
  wand x 5 2 18 (by decide) rfl (by decide) (by decide)
theorem w20 (x : Fin 14 → Bool) :
    wval CC x 20 = true ↔ wval CC x 7 = true ∨ wval CC x 9 = true :=
  wor x 6 7 9 (by decide) rfl (by decide) (by decide)
theorem w21 (x : Fin 14 → Bool) :
    wval CC x 21 = true ↔ wval CC x 20 = true ∨ wval CC x 10 = true :=
  wor x 7 20 10 (by decide) rfl (by decide) (by decide)
theorem w22 (x : Fin 14 → Bool) :
    wval CC x 22 = true ↔ wval CC x 3 = true ∧ wval CC x 21 = true :=
  wand x 8 3 21 (by decide) rfl (by decide) (by decide)
theorem w23 (x : Fin 14 → Bool) :
    wval CC x 23 = true ↔ wval CC x 8 = true ∨ wval CC x 10 = true :=
  wor x 9 8 10 (by decide) rfl (by decide) (by decide)
theorem w24 (x : Fin 14 → Bool) :
    wval CC x 24 = true ↔ wval CC x 23 = true ∨ wval CC x 11 = true :=
  wor x 10 23 11 (by decide) rfl (by decide) (by decide)
theorem w25 (x : Fin 14 → Bool) :
    wval CC x 25 = true ↔ wval CC x 4 = true ∧ wval CC x 24 = true :=
  wand x 11 4 24 (by decide) rfl (by decide) (by decide)
theorem w26 (x : Fin 14 → Bool) :
    wval CC x 26 = true ↔ wval CC x 9 = true ∨ wval CC x 11 = true :=
  wor x 12 9 11 (by decide) rfl (by decide) (by decide)
theorem w27 (x : Fin 14 → Bool) :
    wval CC x 27 = true ↔ wval CC x 26 = true ∨ wval CC x 12 = true :=
  wor x 13 26 12 (by decide) rfl (by decide) (by decide)
theorem w28 (x : Fin 14 → Bool) :
    wval CC x 28 = true ↔ wval CC x 5 = true ∧ wval CC x 27 = true :=
  wand x 14 5 27 (by decide) rfl (by decide) (by decide)
theorem w29 (x : Fin 14 → Bool) :
    wval CC x 29 = true ↔ wval CC x 10 = true ∨ wval CC x 12 = true :=
  wor x 15 10 12 (by decide) rfl (by decide) (by decide)
theorem w30 (x : Fin 14 → Bool) :
    wval CC x 30 = true ↔ wval CC x 29 = true ∨ wval CC x 13 = true :=
  wor x 16 29 13 (by decide) rfl (by decide) (by decide)
theorem w31 (x : Fin 14 → Bool) :
    wval CC x 31 = true ↔ wval CC x 6 = true ∧ wval CC x 30 = true :=
  wand x 17 6 30 (by decide) rfl (by decide) (by decide)
theorem w32 (x : Fin 14 → Bool) :
    wval CC x 32 = true ↔ wval CC x 0 = true ∧ wval CC x 7 = true :=
  wand x 18 0 7 (by decide) rfl (by decide) (by decide)
theorem w33 (x : Fin 14 → Bool) :
    wval CC x 33 = true ↔ wval CC x 0 = true ∧ wval CC x 13 = true :=
  wand x 19 0 13 (by decide) rfl (by decide) (by decide)
theorem w34 (x : Fin 14 → Bool) :
    wval CC x 34 = true ↔ wval CC x 7 = true ∨ wval CC x 11 = true :=
  wor x 20 7 11 (by decide) rfl (by decide) (by decide)
theorem w35 (x : Fin 14 → Bool) :
    wval CC x 35 = true ↔ wval CC x 0 = true ∧ wval CC x 34 = true :=
  wand x 21 0 34 (by decide) rfl (by decide) (by decide)
theorem w36 (x : Fin 14 → Bool) :
    wval CC x 36 = true ↔ wval CC x 11 = true ∨ wval CC x 13 = true :=
  wor x 22 11 13 (by decide) rfl (by decide) (by decide)
theorem w37 (x : Fin 14 → Bool) :
    wval CC x 37 = true ↔ wval CC x 0 = true ∧ wval CC x 36 = true :=
  wand x 23 0 36 (by decide) rfl (by decide) (by decide)
theorem w38 (x : Fin 14 → Bool) :
    wval CC x 38 = true ↔ wval CC x 35 = true ∧ wval CC x 37 = true :=
  wand x 24 35 37 (by decide) rfl (by decide) (by decide)
theorem w39 (x : Fin 14 → Bool) :
    wval CC x 39 = true ↔ wval CC x 16 = true ∨ wval CC x 19 = true :=
  wor x 25 16 19 (by decide) rfl (by decide) (by decide)
theorem w40 (x : Fin 14 → Bool) :
    wval CC x 40 = true ↔ wval CC x 39 = true ∨ wval CC x 22 = true :=
  wor x 26 39 22 (by decide) rfl (by decide) (by decide)
theorem w41 (x : Fin 14 → Bool) :
    wval CC x 41 = true ↔ wval CC x 40 = true ∨ wval CC x 25 = true :=
  wor x 27 40 25 (by decide) rfl (by decide) (by decide)
theorem w42 (x : Fin 14 → Bool) :
    wval CC x 42 = true ↔ wval CC x 41 = true ∨ wval CC x 28 = true :=
  wor x 28 41 28 (by decide) rfl (by decide) (by decide)
theorem w43 (x : Fin 14 → Bool) :
    wval CC x 43 = true ↔ wval CC x 42 = true ∨ wval CC x 31 = true :=
  wor x 29 42 31 (by decide) rfl (by decide) (by decide)
theorem w44 (x : Fin 14 → Bool) :
    wval CC x 44 = true ↔ wval CC x 43 = true ∨ wval CC x 32 = true :=
  wor x 30 43 32 (by decide) rfl (by decide) (by decide)
theorem w45 (x : Fin 14 → Bool) :
    wval CC x 45 = true ↔ wval CC x 44 = true ∨ wval CC x 33 = true :=
  wor x 31 44 33 (by decide) rfl (by decide) (by decide)
theorem w46 (x : Fin 14 → Bool) :
    wval CC x 46 = true ↔ wval CC x 45 = true ∨ wval CC x 38 = true :=
  wor x 32 45 38 (by decide) rfl (by decide) (by decide)

theorem e16 (x : Fin 14 → Bool) : wval CC x 16 = true ↔ t1 x = true := by
  simp only [w16, w15, w14, w1, w7, w8, w12, t1_iff]
  tauto

theorem e19 (x : Fin 14 → Bool) : wval CC x 19 = true ↔ t2 x = true := by
  simp only [w19, w18, w17, w2, w8, w9, w13, t2_iff]
  tauto

theorem e22 (x : Fin 14 → Bool) : wval CC x 22 = true ↔ t3 x = true := by
  simp only [w22, w21, w20, w3, w7, w9, w10, t3_iff]
  tauto

theorem e25 (x : Fin 14 → Bool) : wval CC x 25 = true ↔ t4 x = true := by
  simp only [w25, w24, w23, w4, w8, w10, w11, t4_iff]
  tauto

theorem e28 (x : Fin 14 → Bool) : wval CC x 28 = true ↔ t5 x = true := by
  simp only [w28, w27, w26, w5, w9, w11, w12, t5_iff]
  tauto

theorem e31 (x : Fin 14 → Bool) : wval CC x 31 = true ↔ t6 x = true := by
  simp only [w31, w30, w29, w6, w10, w12, w13, t6_iff]
  tauto

theorem b32 (x : Fin 14 → Bool) : wval CC x 32 = true → t0 x = true := by
  simp only [w32, w0, w7, t0_iff]
  tauto

theorem b33 (x : Fin 14 → Bool) : wval CC x 33 = true → t0 x = true := by
  simp only [w33, w0, w13, t0_iff]
  tauto

theorem b35 (x : Fin 14 → Bool) : wval CC x 35 = true → t0 x = true := by
  simp only [w35, w34, w0, w7, w11, t0_iff]
  tauto

theorem b37 (x : Fin 14 → Bool) : wval CC x 37 = true → t0 x = true := by
  simp only [w37, w36, w0, w11, w13, t0_iff]
  tauto

theorem b38 (x : Fin 14 → Bool) : wval CC x 38 = true → t0 x = true := by
  simp only [w38, w37, w36, w35, w34, w0, w7, w11, w13, t0_iff]
  tauto

theorem e0 (x : Fin 14 → Bool) (h : t0 x = true) :
    wval CC x 32 = true ∨ wval CC x 33 = true ∨ wval CC x 38 = true := by
  rw [t0_iff] at h
  simp only [w38, w37, w36, w35, w34, w33, w32, w0, w7, w11, w13]
  tauto

theorem s0 (x : Fin 14 → Bool) (h : t0 x = true) : f x = true := by
  rw [f_iff]; exact Or.inl h


theorem g16 (x : Fin 14 → Bool) (h : wval CC x 16 = true) : f x = true :=
  (f_iff x).2 (Or.inr (Or.inl ((e16 x).1 h)))

theorem g19 (x : Fin 14 → Bool) (h : wval CC x 19 = true) : f x = true :=
  (f_iff x).2 (Or.inr (Or.inr (Or.inl ((e19 x).1 h))))

theorem g22 (x : Fin 14 → Bool) (h : wval CC x 22 = true) : f x = true :=
  (f_iff x).2 (Or.inr (Or.inr (Or.inr (Or.inl ((e22 x).1 h)))))

theorem g25 (x : Fin 14 → Bool) (h : wval CC x 25 = true) : f x = true :=
  (f_iff x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((e25 x).1 h))))))

theorem g28 (x : Fin 14 → Bool) (h : wval CC x 28 = true) : f x = true :=
  (f_iff x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((e28 x).1 h)))))))

theorem g31 (x : Fin 14 → Bool) (h : wval CC x 31 = true) : f x = true :=
  (f_iff x).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((e31 x).1 h)))))))

theorem g32 (x : Fin 14 → Bool) (h : wval CC x 32 = true) : f x = true :=
  s0 x (b32 x h)

theorem g33 (x : Fin 14 → Bool) (h : wval CC x 33 = true) : f x = true :=
  s0 x (b33 x h)

theorem g38 (x : Fin 14 → Bool) (h : wval CC x 38 = true) : f x = true :=
  s0 x (b38 x h)

theorem g39 (x : Fin 14 → Bool) (h : wval CC x 39 = true) : f x = true :=
  ((w39 x).1 h).elim (g16 x) (g19 x)

theorem g40 (x : Fin 14 → Bool) (h : wval CC x 40 = true) : f x = true :=
  ((w40 x).1 h).elim (g39 x) (g22 x)

theorem g41 (x : Fin 14 → Bool) (h : wval CC x 41 = true) : f x = true :=
  ((w41 x).1 h).elim (g40 x) (g25 x)

theorem g42 (x : Fin 14 → Bool) (h : wval CC x 42 = true) : f x = true :=
  ((w42 x).1 h).elim (g41 x) (g28 x)

theorem g43 (x : Fin 14 → Bool) (h : wval CC x 43 = true) : f x = true :=
  ((w43 x).1 h).elim (g42 x) (g31 x)

theorem g44 (x : Fin 14 → Bool) (h : wval CC x 44 = true) : f x = true :=
  ((w44 x).1 h).elim (g43 x) (g32 x)

theorem g45 (x : Fin 14 → Bool) (h : wval CC x 45 = true) : f x = true :=
  ((w45 x).1 h).elim (g44 x) (g33 x)

theorem g46 (x : Fin 14 → Bool) (h : wval CC x 46 = true) : f x = true :=
  ((w46 x).1 h).elim (g45 x) (g38 x)

theorem out (x : Fin 14 → Bool) : wval CC x 46 = true ↔ f x = true := by
  refine ⟨g46 x, ?_⟩
  intro h
  rw [f_iff] at h
  rcases h with h | h | h | h | h | h | h
  · rcases e0 x h with h | h | h
    · exact ((w46 x).2 (Or.inl ((w45 x).2 (Or.inl ((w44 x).2 (Or.inr h))))))
    · exact ((w46 x).2 (Or.inl ((w45 x).2 (Or.inr h))))
    · exact ((w46 x).2 (Or.inr h))
  · exact ((w46 x).2 (Or.inl ((w45 x).2 (Or.inl ((w44 x).2 (Or.inl ((w43 x).2 (Or.inl ((w42 x).2 (Or.inl ((w41 x).2 (Or.inl ((w40 x).2 (Or.inl ((w39 x).2 (Or.inl ((e16 x).2 h)))))))))))))))))
  · exact ((w46 x).2 (Or.inl ((w45 x).2 (Or.inl ((w44 x).2 (Or.inl ((w43 x).2 (Or.inl ((w42 x).2 (Or.inl ((w41 x).2 (Or.inl ((w40 x).2 (Or.inl ((w39 x).2 (Or.inr ((e19 x).2 h)))))))))))))))))
  · exact ((w46 x).2 (Or.inl ((w45 x).2 (Or.inl ((w44 x).2 (Or.inl ((w43 x).2 (Or.inl ((w42 x).2 (Or.inl ((w41 x).2 (Or.inl ((w40 x).2 (Or.inr ((e22 x).2 h)))))))))))))))
  · exact ((w46 x).2 (Or.inl ((w45 x).2 (Or.inl ((w44 x).2 (Or.inl ((w43 x).2 (Or.inl ((w42 x).2 (Or.inl ((w41 x).2 (Or.inr ((e25 x).2 h)))))))))))))
  · exact ((w46 x).2 (Or.inl ((w45 x).2 (Or.inl ((w44 x).2 (Or.inl ((w43 x).2 (Or.inl ((w42 x).2 (Or.inr ((e28 x).2 h)))))))))))
  · exact ((w46 x).2 (Or.inl ((w45 x).2 (Or.inl ((w44 x).2 (Or.inl ((w43 x).2 (Or.inr ((e31 x).2 h)))))))))

theorem nl (d : DecidableRel GG.Adj) (w : ℕ) (k : Fin 14)
    (h : wval CC (fun i => decide (i = k)) w = true)
    (hk : f (fun i => decide (i = k)) = false) : ¬ @IsImpWire 14 GG d CC w := by
  intro hw
  have := (gf d _).1 (hw.1 _ h)
  rw [hk] at this
  exact Bool.false_ne_true this

theorem lift (d : DecidableRel GG.Adj) : @IsLiftFixedPoint 14 GG d CC := by
  rintro ⟨h, hlt, b, -, hor, hnb, himp⟩
  have hlt' : h < 33 := hlt
  interval_cases h
  · fin_cases b
    · exact nl d 7 7 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 8 8 (by decide +kernel) (by decide +kernel) himp
  · fin_cases b
    · exact nl d 14 8 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 12 12 (by decide +kernel) (by decide +kernel) himp
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · fin_cases b
    · exact nl d 8 8 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 9 9 (by decide +kernel) (by decide +kernel) himp
  · fin_cases b
    · exact nl d 17 9 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 13 13 (by decide +kernel) (by decide +kernel) himp
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · fin_cases b
    · exact nl d 7 7 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 9 9 (by decide +kernel) (by decide +kernel) himp
  · fin_cases b
    · exact nl d 20 9 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 10 10 (by decide +kernel) (by decide +kernel) himp
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · fin_cases b
    · exact nl d 8 8 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 10 10 (by decide +kernel) (by decide +kernel) himp
  · fin_cases b
    · exact nl d 23 10 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 11 11 (by decide +kernel) (by decide +kernel) himp
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · fin_cases b
    · exact nl d 9 9 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 11 11 (by decide +kernel) (by decide +kernel) himp
  · fin_cases b
    · exact nl d 26 11 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 12 12 (by decide +kernel) (by decide +kernel) himp
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · fin_cases b
    · exact nl d 10 10 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 12 12 (by decide +kernel) (by decide +kernel) himp
  · fin_cases b
    · exact nl d 29 12 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 13 13 (by decide +kernel) (by decide +kernel) himp
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · fin_cases b
    · exact nl d 7 7 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 11 11 (by decide +kernel) (by decide +kernel) himp
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · fin_cases b
    · exact nl d 11 11 (by decide +kernel) (by decide +kernel) himp
    · exact nl d 13 13 (by decide +kernel) (by decide +kernel) himp
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · exact absurd hor (by intro e; exact GateOp.noConfusion e)
  · exact absurd (fun x hx => (gf d x).2 (g39 x hx)) hnb
  · exact absurd (fun x hx => (gf d x).2 (g40 x hx)) hnb
  · exact absurd (fun x hx => (gf d x).2 (g41 x hx)) hnb
  · exact absurd (fun x hx => (gf d x).2 (g42 x hx)) hnb
  · exact absurd (fun x hx => (gf d x).2 (g43 x hx)) hnb
  · exact absurd (fun x hx => (gf d x).2 (g44 x hx)) hnb
  · exact absurd (fun x hx => (gf d x).2 (g45 x hx)) hnb
  · exact absurd (fun x hx => (gf d x).2 (g46 x hx)) hnb

end PEqualNP.Outside.L_meta_3655

open PEqualNP.Outside.L_meta_3655 in
theorem PEqualNP.Outside.L_meta_3655 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 38] }], output := 46 } → (∀ z : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C z = decide (∃ p3 l3 : Fin 7, (p3.val = l3.val ∨ p3.val = (l3.val + 1) % 7 ∨ p3.val = (l3.val + 3) % 7) ∧ z (Fin.castAdd 7 p3) = true ∧ z (Fin.natAdd 7 l3) = true)) ∧ (PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) C 21 ∧ PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ub vb : Fin 14 => ∃ pb lb : Fin 7, (pb.val = lb.val ∨ pb.val = (lb.val + 1) % 7 ∨ pb.val = (lb.val + 3) % 7) ∧ ub = Fin.castAdd 7 pb ∧ vb = Fin.natAdd 7 lb)) C 23 ∧ PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun uc vc : Fin 14 => ∃ pc lc : Fin 7, (pc.val = lc.val ∨ pc.val = (lc.val + 1) % 7 ∨ pc.val = (lc.val + 3) % 7) ∧ uc = Fin.castAdd 7 pc ∧ vc = Fin.natAdd 7 lc)) C 24) ∧ PEqualNP.Core.IsLiftFixedPoint (SimpleGraph.fromRel (fun ud vd : Fin 14 => ∃ pd ld : Fin 7, (pd.val = ld.val ∨ pd.val = (ld.val + 1) % 7 ∨ pd.val = (ld.val + 3) % 7) ∧ ud = Fin.castAdd 7 pd ∧ vd = Fin.natAdd 7 ld)) C ∧ PEqualNP.ReadK.doubleReread C 14 (fun w => decide (7 ≤ w)) ((List.finRange 7).flatMap (fun p5 => ((List.finRange 7).filter (fun l5 => decide (p5.val = l5.val ∨ p5.val = (l5.val + 1) % 7 ∨ p5.val = (l5.val + 3) % 7))).map (fun l6 => (p5.val, 7 + l6.val)))) = [(0, 11)] := by
  intro C hC
  have e : C = CC := hC
  subst e
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro z
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact (out z).trans (Inc_iff z).symm
  · exact fun x hx => (gf _ x).2 (s0 x (b35 x hx))
  · exact fun x hx => (gf _ x).2 (s0 x (b37 x hx))
  · exact fun x hx => (gf _ x).2 (s0 x (b38 x hx))
  · exact lift _
  · decide +kernel
