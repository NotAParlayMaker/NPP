import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3418

/-- Wire values on the 24 test rows, one bit per row. -/
abbrev BV := BitVec 24

/-- The columns of the nine inputs and of the first gate `OR(x_0, x_3)`. -/
def A : List BV :=
  [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661]

/-- Thirteen ORs of two input columns, none of them an input column, `0` or `4095`. -/
def P : List BV :=
  [14053491, 7684279, 16605241, 5634609, 6145137, 14566065, 16010545, 11759815, 8827215,
    11219035, 8632931, 9434179, 13513411]

/-- A new value is all ones or the AND or OR of two values of `pre`. -/
def G (pre : List BV) (v : BV) : Prop :=
  v = 16777215 ∨ ∃ a b, a ∈ pre ∧ b ∈ pre ∧ (v = a &&& b ∨ v = a ||| b)

/-- A gate column: all ones, or the AND or OR of two earlier columns or the zero column. -/
def Ok (pre : List BV) (v : BV) : Prop :=
  v = 16777215 ∨ ∃ a b, a ∈ (0 : BV) :: pre ∧ b ∈ (0 : BV) :: pre ∧ (v = a &&& b ∨ v = a ||| b)

/-- Every entry from position 10 on is a `G`-step over the entries before it. -/
def GoodPre (l : List BV) : Prop :=
  ∀ i, 10 ≤ i → i < l.length → G (l.take i) (l.getD i 0)

/-- The conclusion of the step, for one list. -/
def Spec (x8 : List BV) : Prop :=
  x8.length = 24 ∧ x8.take 10 = A ∧ x8.getD 23 0 = 4095 ∧ ((0 : BV) :: x8).Nodup ∧
    ∀ x9 : ℕ, 0 < x9 → x9 < 15 →
      (x8.getD (9 + x9) 0 = 16777215 ∨ ∃ x13 x14 : BV, x13 ∈ x8.take (9 + x9) ∧
        x14 ∈ x8.take (9 + x9) ∧
        (x8.getD (9 + x9) 0 = x13 &&& x14 ∨ x8.getD (9 + x9) 0 = x13 ||| x14))

theorem G_mono {pre pre' : List BV} {v : BV} (h : G pre v) (hs : pre ⊆ pre') : G pre' v := by
  rcases h with h | ⟨a, b, ha, hb, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, b, hs ha, hs hb, h⟩

theorem getD_append_left' (l m : List BV) (i : ℕ) (hi : i < l.length) :
    (l ++ m).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_single (l : List BV) (v : BV) : (l ++ [v]).getD l.length 0 = v := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl l.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem GoodPre_append {l : List BV} {v : BV} (h : GoodPre l) (hv : G l v) :
    GoodPre (l ++ [v]) := by
  intro i hi hlt
  rw [List.length_append, List.length_singleton] at hlt
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
  · rw [List.take_append_of_le_length hlt.le, getD_append_left' _ _ _ hlt]
    exact h i hi hlt
  · subst heq
    rw [List.take_left' rfl, getD_append_single]
    exact hv

theorem GoodPre_appendList (ps : List BV) : ∀ (l : List BV), GoodPre l → 10 ≤ l.length →
    (∀ p ∈ ps, G (l.take 10) p) → GoodPre (l ++ ps) := by
  induction ps with
  | nil => intro l h _ _; simpa using h
  | cons p ps ih =>
    intro l h hl hps
    have h1 : GoodPre (l ++ [p]) :=
      GoodPre_append h (G_mono (hps p (List.mem_cons_self ..)) (List.take_subset _ _))
    have h2 : (l ++ [p]).take 10 = l.take 10 := List.take_append_of_le_length hl
    have := ih (l ++ [p]) h1 (by simp; omega) (fun q hq => by
      rw [h2]; exact hps q (List.mem_cons_of_mem _ hq))
    simpa using this

theorem P_G : ∀ p ∈ P, ∃ a ∈ A, ∃ b ∈ A, p = a ||| b := by
  intro p hp
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨5521457, by simp [A], 8532035, by simp [A], by decide⟩
  · exact ⟨5521457, by simp [A], 3227782, by simp [A], by decide⟩
  · exact ⟨5521457, by simp [A], 11083800, by simp [A], by decide⟩
  · exact ⟨5521457, by simp [A], 113184, by simp [A], by decide⟩
  · exact ⟨5521457, by simp [A], 902208, by simp [A], by decide⟩
  · exact ⟨5521457, by simp [A], 13501056, by simp [A], by decide⟩
  · exact ⟨5521457, by simp [A], 15731968, by simp [A], by decide⟩
  · exact ⟨8532035, by simp [A], 3227782, by simp [A], by decide⟩
  · exact ⟨8532035, by simp [A], 430348, by simp [A], by decide⟩
  · exact ⟨8532035, by simp [A], 11083800, by simp [A], by decide⟩
  · exact ⟨8532035, by simp [A], 113184, by simp [A], by decide⟩
  · exact ⟨8532035, by simp [A], 902208, by simp [A], by decide⟩
  · exact ⟨8532035, by simp [A], 13501056, by simp [A], by decide⟩

theorem P_nodup : P.Nodup := by simp [P]

theorem P_disj : ∀ p ∈ P, p ∉ A ∧ p ≠ 0 ∧ p ≠ 4095 := by simp [P, A]

theorem P_length : P.length = 13 := rfl

/-- Close: pad `acc` with fresh ORs of inputs, then append `4095`. -/
theorem close (acc : List BV) (hA : acc.take 10 = A) (h10 : 10 ≤ acc.length)
    (hgood : GoodPre acc) (hnd : ((0 : BV) :: acc).Nodup) (h4 : (4095 : BV) ∉ acc)
    (hlen : acc.length ≤ 23)
    (hab : ∃ a b, a ∈ acc ∧ b ∈ acc ∧ ((4095 : BV) = a &&& b ∨ (4095 : BV) = a ||| b)) :
    ∃ x8, Spec x8 := by
  classical
  set k := 23 - acc.length with hk
  set Q := P.filter (fun p => p ∉ acc) with hQ
  set pads := Q.take k with hpads
  -- counting: at most `acc.length - 10` pool values lie in `acc`
  have hin : (P.filter (fun p => p ∈ acc)).length ≤ acc.length - 10 := by
    have hsub : P.filter (fun p => p ∈ acc) ⊆ acc.drop 10 := by
      intro p hp
      rw [List.mem_filter] at hp
      have hpA : p ∉ A := (P_disj p hp.1).1
      have hpacc : p ∈ acc := by simpa using hp.2
      rw [← List.take_append_drop 10 acc, hA] at hpacc
      rcases List.mem_append.mp hpacc with h | h
      · exact absurd h hpA
      · exact h
    have := ((P_nodup.filter _).subperm hsub).length_le
    simpa using this
  have hsplit := List.length_eq_length_filter_add (fun p => decide (p ∈ acc)) (l := P)
  have hQlen : k ≤ Q.length := by
    have e : Q = P.filter (fun p => !decide (p ∈ acc)) := by
      rw [hQ]; apply List.filter_congr; intro p _; simp
    rw [e]; rw [P_length] at hsplit
    have : (P.filter (fun p => decide (p ∈ acc))).length ≤ acc.length - 10 := by simpa using hin
    omega
  have hpadlen : pads.length = k := by rw [hpads, List.length_take]; omega
  have hpadP : ∀ p ∈ pads, p ∈ P ∧ p ∉ acc := by
    intro p hp
    have := List.mem_of_mem_take hp
    rw [hQ, List.mem_filter] at this
    exact ⟨this.1, by simpa using this.2⟩
  have hpadnd : pads.Nodup := (P_nodup.filter _).sublist (List.take_sublist _ _)
  refine ⟨acc ++ pads ++ [4095], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · rw [List.append_assoc, List.take_append_of_le_length h10, hA]
  · have : (acc ++ pads).length = 23 := by simp only [List.length_append]; omega
    rw [← this, getD_append_single]
  · rw [List.nodup_cons] at hnd ⊢
    refine ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      refine ⟨⟨hnd.1, fun h => (P_disj 0 (hpadP 0 h).1).2.1 rfl⟩, by decide +kernel⟩
    · rw [List.nodup_append]
      refine ⟨?_, List.nodup_singleton _, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd.2, hpadnd, ?_⟩
        intro a ha b hb hab'
        subst hab'
        exact (hpadP a hb).2 ha
      · intro a ha b hb hab'
        rw [List.mem_singleton] at hb
        subst hb; subst hab'
        rcases List.mem_append.mp ha with h | h
        · exact h4 h
        · exact (P_disj _ (hpadP _ h).1).2.2 rfl
  · have g1 : GoodPre (acc ++ pads) := by
      refine GoodPre_appendList pads acc hgood h10 ?_
      intro p hp
      obtain ⟨a, ha, b, hb, e⟩ := P_G p (hpadP p hp).1
      rw [hA]
      exact Or.inr ⟨a, b, ha, hb, Or.inr e⟩
    have g2 : GoodPre (acc ++ pads ++ [4095]) := by
      refine GoodPre_append g1 ?_
      obtain ⟨a, b, ha, hb, e⟩ := hab
      exact Or.inr ⟨a, b, List.mem_append_left _ ha, List.mem_append_left _ hb, e⟩
    intro x9 h0 h15
    have hl : (acc ++ pads ++ [(4095 : BV)]).length = 24 := by
      simp only [List.length_append, List.length_singleton]; omega
    exact g2 (9 + x9) (by omega) (by omega)

theorem ok_of_zero_or (pre acc : List BV) (hpre : ∀ x ∈ pre, x = 0 ∨ x ∈ acc) (v : BV)
    (hv : Ok pre v) (hv0 : v ≠ 0) (hvacc : v ∉ acc) : G acc v := by
  rcases hv with h | ⟨a, b, ha, hb, h⟩
  · exact Or.inl h
  · have ha' : a = 0 ∨ a ∈ acc := by
      rcases List.mem_cons.mp ha with h | h
      · exact Or.inl h
      · exact hpre a h
    have hb' : b = 0 ∨ b ∈ acc := by
      rcases List.mem_cons.mp hb with h | h
      · exact Or.inl h
      · exact hpre b h
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · subst ha' hb'; rcases h with h | h <;> simp at h <;> exact absurd h hv0
    · subst ha'; rcases h with h | h <;> simp at h
      · exact absurd h hv0
      · exact absurd (h ▸ hb') hvacc
    · subst hb'; rcases h with h | h <;> simp at h
      · exact absurd h hv0
      · exact absurd (h ▸ ha') hvacc
    · exact Or.inr ⟨a, b, ha', hb', h⟩

theorem greedy (rest : List BV) : ∀ (pre acc : List BV),
    acc.take 10 = A → 10 ≤ acc.length → GoodPre acc → ((0 : BV) :: acc).Nodup →
    (4095 : BV) ∉ acc → (∀ x ∈ pre, x = 0 ∨ x ∈ acc) → acc.length + rest.length ≤ 24 →
    (∀ i < rest.length, Ok (pre ++ rest.take i) (rest.getD i 0)) → (4095 : BV) ∈ rest →
    ∃ x8, Spec x8 := by
  induction rest with
  | nil => intro _ _ _ _ _ _ _ _ _ _ h; simp at h
  | cons v rest ih =>
    intro pre acc hA h10 hgood hnd h4 hpre hlen hvalid hmem
    have hv : Ok pre v := by simpa using hvalid 0 (by simp)
    have hshift : ∀ i < rest.length, Ok ((pre ++ [v]) ++ rest.take i) (rest.getD i 0) := by
      intro i hi
      have := hvalid (i + 1) (by simp; omega)
      simpa [List.take_succ_cons] using this
    simp only [List.length_cons] at hlen
    by_cases hv4 : v = 4095
    · subst hv4
      refine close acc hA h10 hgood hnd h4 (by omega) ?_
      have hg := ok_of_zero_or pre acc hpre 4095 hv (by decide +kernel) h4
      rcases hg with h | h
      · exact absurd h (by decide +kernel)
      · exact h
    · have hmem' : (4095 : BV) ∈ rest := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hv4
        · exact h
      by_cases hold : v = 0 ∨ v ∈ acc
      · refine ih (pre ++ [v]) acc hA h10 hgood hnd h4 ?_ (by omega) hshift hmem'
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hpre x h
        · rw [List.mem_singleton] at h; subst h; exact hold
      · rw [not_or] at hold
        have hg := ok_of_zero_or pre acc hpre v hv hold.1 hold.2
        refine ih (pre ++ [v]) (acc ++ [v]) ?_ (by simp; omega) (GoodPre_append hgood hg) ?_
          ?_ ?_ (by simp; omega) hshift hmem'
        · rw [List.take_append_of_le_length h10, hA]
        · rw [List.nodup_cons] at hnd ⊢
          refine ⟨?_, ?_⟩
          · simp only [List.mem_append, List.mem_singleton, not_or]
            exact ⟨hnd.1, fun h => hold.1 h.symm⟩
          · refine List.nodup_append.mpr ⟨hnd.2, List.nodup_singleton v, ?_⟩
            intro a ha b hb e
            rw [List.mem_singleton] at hb
            subst hb e
            exact hold.2 ha
        · simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨h4, fun h => hv4 h.symm⟩
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · rcases hpre x h with h' | h'
            · exact Or.inl h'
            · exact Or.inr (List.mem_append_left _ h')
          · rw [List.mem_singleton] at h; subst h
            exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))

/-! From the circuit to its columns. -/

/-- One evaluation step of `Circuit.wires`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega

theorem past (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem gate_step (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rcases j with _ | j
    · rw [List.foldl_cons, keep _ _ _ (by simp [step])]
      simp [step, List.getD_eq_getElem?_getD]
    · rw [List.foldl_cons]
      have hl : (step w g).length = w.length + 1 := by simp [step]
      have := ih (step w g) j (by simpa using hj)
      rw [hl, show w.length + 1 + j = w.length + (j + 1) by omega] at this
      rw [this]
      simp [List.take_succ_cons, List.foldl_cons]

/-- Row `r`: vertex `i` is present when bit `r` of input column `i` is set. -/
def row (r : ℕ) : Fin 9 → Bool := fun i => (A.getD i.val 0).getLsbD r

/-- The value of wire `w` on row `r`. -/
def val (C : Circuit) (w r : ℕ) : Bool := (C.wires (List.ofFn (row r))).getD w false

/-- The column of wire `w`. -/
def col (C : Circuit) (w : ℕ) : BV :=
  (BitVec.ofBoolListLE ((List.range 24).map (fun r => val C w r))).setWidth 24

theorem getLsbD_col (C : Circuit) (w r : ℕ) (hr : r < 24) :
    (col C w).getLsbD r = val C w r := by
  rw [col, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  simp [hr, List.getD_eq_getElem?_getD, List.getElem?_range hr]

theorem col_ext {C : Circuit} {w : ℕ} {y : BV} (h : ∀ r < 24, val C w r = y.getLsbD r) :
    col C w = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [getLsbD_col C w r hr, h r hr]

theorem f_rows : ∀ r < 24,
    ([(1 : ℕ), 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77].any fun (x8 : ℕ) =>
      row r (Fin.ofNat 9 (x8 / 9)) && row r (Fin.ofNat 9 (x8 % 9))) =
      (4095 : BV).getLsbD r := by decide +kernel

theorem A_or : A.getD 9 0 = A.getD 0 0 ||| A.getD 3 0 := by decide +kernel

end PEqualNP.Outside.L_meta_3418

open PEqualNP.Outside.L_meta_3418 in
theorem PEqualNP.Outside.L_meta_3418 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.gates.length = (15 : ℕ) →     x1.output = (23 : ℕ) →       x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →         PEqualNP.MetaComplexity.Monotone2 x1 →           (∀ (x6 : ℕ) (x7 : x6 < x1.gates.length), ∀ x8 ∈ x1.gates[x6].inputs, x8 < (9 : ℕ) + x6 ∨ x8 = (24 : ℕ)) →             (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (9 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (9 : ℕ)))) →               ∃ (x8 : List (BitVec (24 : ℕ))),                 x8.length = (24 : ℕ) ∧                   List.take (10 : ℕ) x8 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧                     x8.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧                       ((0 : BitVec (24 : ℕ)) :: x8).Nodup ∧                         ∀ (x9 : ℕ),                           (0 : ℕ) < x9 →                             x9 < (15 : ℕ) →                               have x12 : BitVec (24 : ℕ) := x8.getD ((9 : ℕ) + x9) (0 : BitVec (24 : ℕ));                               x12 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x13 : BitVec (24 : ℕ)) (x14 : BitVec (24 : ℕ)), x13 ∈ List.take ((9 : ℕ) + x9) x8 ∧ x14 ∈ List.take ((9 : ℕ) + x9) x8 ∧ (x12 = x13 &&& x14 ∨ x12 = x13 ||| x14) := by
  intro C hlen hout hg0 hmono hin hfun
  classical
  -- wires on a row have length 24
  have wlen : ∀ r, (C.wires (List.ofFn (row r))).length = 24 := by
    intro r; rw [wires_eq, foldl_length, hlen]; simp
  -- value of gate `j` from the values of its inputs
  have gval : ∀ j (hj : j < 15) r, val C (9 + j) r =
      (C.gates[j]'(by omega)).op.eval
        ((C.gates[j]'(by omega)).inputs.map fun i => val C i r) := by
    intro j hj r
    have hjl : j < C.gates.length := by omega
    have e := gate_step C.gates (List.ofFn (row r)) j hjl
    rw [List.length_ofFn] at e
    unfold val
    rw [wires_eq, e]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hmid : ((C.gates.take j).foldl step (List.ofFn (row r))).length = 9 + j := by
      rw [foldl_length, List.length_ofFn, List.length_take]; omega
    rcases hin j hjl i hi with h | h
    · have hsplit : C.gates.foldl step (List.ofFn (row r)) =
          (C.gates.drop j).foldl step ((C.gates.take j).foldl step (List.ofFn (row r))) := by
        rw [← List.foldl_append, List.take_append_drop]
      rw [hsplit]
      exact (keep (C.gates.drop j) _ i (by omega)).symm
    · subst h
      rw [past _ _ (by omega)]
      have := wlen r
      rw [wires_eq] at this
      rw [past _ _ (by omega)]
  -- columns of the inputs and of gate 0
  have cin : ∀ i < 9, col C i = A.getD i 0 := by
    intro i hi
    apply col_ext
    intro r hr
    unfold val
    rw [wires_eq, keep _ _ _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hi, row]
  have g0 : C.gates[0]'(by omega) = ⟨GateOp.or, [0, 3]⟩ := by
    have := hg0; rw [List.getElem?_eq_getElem (by omega)] at this; exact Option.some.inj this
  have c9 : col C 9 = A.getD 9 0 := by
    rw [A_or, ← cin 0 (by omega), ← cin 3 (by omega)]
    apply col_ext
    intro r hr
    rw [BitVec.getLsbD_or, getLsbD_col _ _ _ hr, getLsbD_col _ _ _ hr]
    have := gval 0 (by omega) r
    rw [g0] at this
    simpa [GateOp.eval] using this
  -- the output column
  have c23 : col C 23 = 4095 := by
    apply col_ext
    intro r hr
    have e : val C 23 r = circuitFun 9 C (row r) := by
      simp only [val, circuitFun, Circuit.eval, hout]
    rw [e, hfun]
    exact f_rows r hr
  -- the column of wire 24 is zero
  have c24 : col C 24 = 0 := by
    apply col_ext
    intro r hr
    simp only [val]
    rw [past _ _ (by rw [wlen r])]
    simp
  -- columns list
  set cols := (List.range 24).map (col C) with hcols
  have colsget : ∀ k < 24, cols.getD k 0 = col C k := by
    intro k hk
    simp [hcols, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  have colstake : ∀ m ≤ 24, cols.take m = (List.range m).map (col C) := by
    intro m hm
    rw [hcols, ← List.map_take, List.take_range, Nat.min_eq_left hm]
  have hA : cols.take 10 = A := by
    rw [colstake 10 (by omega)]
    have : (List.range 10).map (col C) = (List.range 10).map (fun i => A.getD i 0) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rcases Nat.lt_or_ge i 9 with h | h
      · exact cin i h
      · rw [show i = 9 by omega]; exact c9
    rw [this]; decide +kernel
  -- each gate column is `Ok` over the earlier columns
  have hok : ∀ j (hj : j < 15), Ok (cols.take (9 + j)) (col C (9 + j)) := by
    intro j hj
    have hjl : j < C.gates.length := by omega
    have hm := hmono _ (List.getElem_mem hjl)
    obtain ⟨hop, hlen2⟩ := hm
    have hval := gval j hj
    have hpre : ∀ i ∈ (C.gates[j]'hjl).inputs, col C i ∈ (0 : BV) :: cols.take (9 + j) := by
      intro i hi
      rcases hin j hjl i hi with h | h
      · apply List.mem_cons_of_mem
        rw [colstake _ (by omega)]
        exact List.mem_map_of_mem (List.mem_range.mpr h)
      · subst h; rw [c24]; exact List.mem_cons_self ..
    generalize hgj : C.gates[j]'hjl = g at hop hlen2 hval hpre
    obtain ⟨op, ins⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    match ins, hlen2, hpre, hval with
    | [], _, _, hval =>
      rcases hop with rfl | rfl
      · left
        apply col_ext; intro r hr
        rw [hval]
        have : (16777215 : BV).getLsbD r = true := by
          have e : (16777215 : BV) = BitVec.allOnes 24 := by decide +kernel
          rw [e, BitVec.getLsbD_allOnes]; simp [hr]
        rw [this]; simp [GateOp.eval]
      · right
        refine ⟨0, 0, List.mem_cons_self .., List.mem_cons_self .., Or.inl ?_⟩
        apply col_ext; intro r hr
        rw [hval]; simp [GateOp.eval]
    | [a], _, hpre, hval =>
      right
      refine ⟨col C a, 0, hpre a (List.mem_singleton_self _), List.mem_cons_self .., Or.inr ?_⟩
      apply col_ext; intro r hr
      rw [hval, BitVec.getLsbD_or, getLsbD_col _ _ _ hr]
      rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | [a, b], _, hpre, hval =>
      right
      refine ⟨col C a, col C b, hpre a (by simp), hpre b (by simp), ?_⟩
      rcases hop with rfl | rfl
      · left
        apply col_ext; intro r hr
        rw [hval, BitVec.getLsbD_and, getLsbD_col _ _ _ hr, getLsbD_col _ _ _ hr]
        simp [GateOp.eval]
      · right
        apply col_ext; intro r hr
        rw [hval, BitVec.getLsbD_or, getLsbD_col _ _ _ hr, getLsbD_col _ _ _ hr]
        simp [GateOp.eval]
    | _ :: _ :: _ :: _, h, _, _ => simp at h
  -- run the greedy pass
  have hcolslen : cols.length = 24 := by simp [hcols]
  obtain ⟨x8, hl, ht, h23, hnd, hgood⟩ :=
    greedy (cols.drop 10) A A (by simp [A]) (by simp [A])
      (fun i h1 h2 => by simp [A] at h2; omega) (by simp [A]) (by simp [A])
      (fun x hx => Or.inr hx) (by simp [hcolslen, A])
      (by
        intro i hi
        have hi' : i < 14 := by simpa [hcolslen] using hi
        have e1 : A ++ (cols.drop 10).take i = cols.take (9 + (i + 1)) := by
          rw [← hA, ← List.take_add]; congr 1; omega
        have e2 : (cols.drop 10).getD i 0 = col C (9 + (i + 1)) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
            colsget _ (by omega)]
          congr 1; omega
        rw [e1, e2]
        exact hok (i + 1) (by omega))
      (by
        have : (cols.drop 10)[13]? = some 4095 := by
          rw [List.getElem?_drop, ← c23]
          simp [hcols, List.getElem?_map, List.getElem?_range]
        exact List.mem_of_getElem? this)
  exact ⟨x8, hl, ht, h23, hnd, fun x9 h0 h15 => hgood x9 h0 h15⟩
