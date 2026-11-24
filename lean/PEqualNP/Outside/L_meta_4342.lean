import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4342

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def evalGates (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl wireStep x

lemma evalGates_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    evalGates (gs₁ ++ gs₂) x = evalGates gs₂ (evalGates gs₁ x) :=
  List.foldl_append

lemma evalGates_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    evalGates (gs ++ [g]) x = wireStep (evalGates gs x) g := by
  rw [evalGates_append]
  rfl

lemma evalGates_length (gs : List Gate) (x : List Bool) :
    (evalGates gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evalGates]
  | cons g gs ih =>
    change (evalGates gs (wireStep x g)).length = x.length + (gs.length + 1)
    rw [ih]
    simp [wireStep]
    omega

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_singleton_self {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_of_le {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

def repVal (outWires : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr k => outWires.getD k false

def repBound (bound : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < bound

lemma repBound_mono {b₁ b₂ : ℕ} {r : Bool ⊕ ℕ} (h : b₁ ≤ b₂) (hr : repBound b₁ r) :
    repBound b₂ r := by
  cases r with
  | inl _ => trivial
  | inr k => exact Nat.lt_of_lt_of_le hr h

lemma repVal_append (w₁ w₂ : List Bool) (r : Bool ⊕ ℕ) (hr : repBound w₁.length r) :
    repVal (w₁ ++ w₂) r = repVal w₁ r := by
  cases r with
  | inl _ => rfl
  | inr k => exact getD_append_left w₁ w₂ k false hr

def combineAnd (n : ℕ) (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ) : (Bool ⊕ ℕ) × List Gate :=
  match r1, r2 with
  | Sum.inl false, _ => (Sum.inl false, outGates)
  | _, Sum.inl false => (Sum.inl false, outGates)
  | Sum.inl true, r => (r, outGates)
  | r, Sum.inl true => (r, outGates)
  | Sum.inr k1, Sum.inr k2 =>
      (Sum.inr (n + outGates.length), outGates ++ [⟨GateOp.and, [k1, k2]⟩])

def combineOr (n : ℕ) (outGates : List Gate) (r1 r2 : Bool ⊕ ℕ) : (Bool ⊕ ℕ) × List Gate :=
  match r1, r2 with
  | Sum.inl true, _ => (Sum.inl true, outGates)
  | _, Sum.inl true => (Sum.inl true, outGates)
  | Sum.inl false, r => (r, outGates)
  | r, Sum.inl false => (r, outGates)
  | Sum.inr k1, Sum.inr k2 =>
      (Sum.inr (n + outGates.length), outGates ++ [⟨GateOp.or, [k1, k2]⟩])

def stepGate (n : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
  let getR := fun i => st.1.getD i (Sum.inl false)
  let res : (Bool ⊕ ℕ) × List Gate :=
    match g.op, g.inputs with
    | GateOp.and, [] => (Sum.inl true, st.2)
    | GateOp.and, [i] => (getR i, st.2)
    | GateOp.and, [i, j] => combineAnd n st.2 (getR i) (getR j)
    | GateOp.or, [] => (Sum.inl false, st.2)
    | GateOp.or, [i] => (getR i, st.2)
    | GateOp.or, [i, j] => combineOr n st.2 (getR i) (getR j)
    | _, _ => (Sum.inl false, st.2)
  (st.1 ++ [res.1], res.2)

def initState (n : ℕ) : List (Bool ⊕ ℕ) × List Gate :=
  (List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)), [])

def Inv (n : ℕ) (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  st.1.length = n + gs.length ∧
  st.2.length ≤ gs.length ∧
  IsAO2 n ⟨st.2, 0⟩ ∧
  (∀ w : ℕ, repBound (n + st.2.length) (st.1.getD w (Sum.inl false))) ∧
  (∀ (x : Fin n → Bool) (w : ℕ),
    (evalGates gs (List.ofFn x)).getD w false =
      repVal (evalGates st.2 (List.ofFn x)) (st.1.getD w (Sum.inl false)))

lemma isAO2_change_output (n : ℕ) (gs : List Gate) (o₁ o₂ : ℕ) (h : IsAO2 n ⟨gs, o₁⟩) :
    IsAO2 n ⟨gs, o₂⟩ := h

lemma isAO2_append_singleton (n : ℕ) (gs : List Gate) (op : GateOp) (k1 k2 : ℕ)
    (h : IsAO2 n ⟨gs, 0⟩) (hop : op = GateOp.and ∨ op = GateOp.or)
    (hk1 : k1 < n + gs.length) (hk2 : k2 < n + gs.length) :
    IsAO2 n ⟨gs ++ [⟨op, [k1, k2]⟩], 0⟩ := by
  rcases h with ⟨hao, hrb, hlen⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hao g hg
    · exact hop
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hga : gateAt ⟨gs ++ [⟨op, [k1, k2]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        simp only [gateAt]
        exact getD_append_left gs [⟨op, [k1, k2]⟩] j ⟨GateOp.or, []⟩ hlt
      rw [hga] at hi
      exact hrb j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hga : gateAt ⟨gs ++ [⟨op, [k1, k2]⟩], 0⟩ gs.length = ⟨op, [k1, k2]⟩ := by
        simp only [gateAt]
        exact getD_append_singleton_self gs ⟨op, [k1, k2]⟩ ⟨GateOp.or, []⟩
      rw [hga] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hk1
      · exact hk2
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hlen g hg
    · rfl

lemma combineAnd_spec (n : ℕ) (gs : List Gate) (r1 r2 : Bool ⊕ ℕ)
    (hao : IsAO2 n ⟨gs, 0⟩)
    (hr1 : repBound (n + gs.length) r1) (hr2 : repBound (n + gs.length) r2) :
    let res := combineAnd n gs r1 r2
    res.2.length ≤ gs.length + 1 ∧
    IsAO2 n ⟨res.2, 0⟩ ∧
    repBound (n + res.2.length) res.1 ∧
    (∀ (x : Fin n → Bool),
      (∃ extra : List Gate, res.2 = gs ++ extra) ∧
      repVal (evalGates res.2 (List.ofFn x)) res.1 =
        (repVal (evalGates gs (List.ofFn x)) r1 && repVal (evalGates gs (List.ofFn x)) r2)) := by
  cases r1 with
  | inl b1 =>
    cases b1 with
    | false =>
      refine ⟨Nat.le_succ _, hao, trivial,
        fun _ => ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩⟩
    | true =>
      cases r2 with
      | inl b2 =>
        cases b2 with
        | false =>
          refine ⟨Nat.le_succ _, hao, trivial,
            fun _ => ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩⟩
        | true =>
          refine ⟨Nat.le_succ _, hao, trivial,
            fun _ => ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩⟩
      | inr k2 =>
        refine ⟨Nat.le_succ _, hao, hr2,
          fun _ => ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩⟩
  | inr k1 =>
    cases r2 with
    | inl b2 =>
      cases b2 with
      | false =>
        refine ⟨Nat.le_succ _, hao, trivial,
          fun _ => ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩⟩
      | true =>
        refine ⟨Nat.le_succ _, hao, hr1,
          fun _ => ⟨⟨[], by simp [combineAnd]⟩, by simp [combineAnd, repVal]⟩⟩
    | inr k2 =>
      simp only [combineAnd]
      refine ⟨by simp, isAO2_append_singleton n gs GateOp.and k1 k2 hao (Or.inl rfl) hr1 hr2,
        by simp [repBound], fun x => ⟨⟨[⟨GateOp.and, [k1, k2]⟩], rfl⟩, ?_⟩⟩
      rw [evalGates_append_singleton]
      simp only [wireStep, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, repVal]
      have hlen : (evalGates gs (List.ofFn x)).length = n + gs.length := by
        rw [evalGates_length, List.length_ofFn]
      rw [← hlen]
      exact getD_append_singleton_self _ _ false

lemma combineOr_spec (n : ℕ) (gs : List Gate) (r1 r2 : Bool ⊕ ℕ)
    (hao : IsAO2 n ⟨gs, 0⟩)
    (hr1 : repBound (n + gs.length) r1) (hr2 : repBound (n + gs.length) r2) :
    let res := combineOr n gs r1 r2
    res.2.length ≤ gs.length + 1 ∧
    IsAO2 n ⟨res.2, 0⟩ ∧
    repBound (n + res.2.length) res.1 ∧
    (∀ (x : Fin n → Bool),
      (∃ extra : List Gate, res.2 = gs ++ extra) ∧
      repVal (evalGates res.2 (List.ofFn x)) res.1 =
        (repVal (evalGates gs (List.ofFn x)) r1 || repVal (evalGates gs (List.ofFn x)) r2)) := by
  cases r1 with
  | inl b1 =>
    cases b1 with
    | true =>
      refine ⟨Nat.le_succ _, hao, trivial,
        fun _ => ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩⟩
    | false =>
      cases r2 with
      | inl b2 =>
        cases b2 with
        | true =>
          refine ⟨Nat.le_succ _, hao, trivial,
            fun _ => ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩⟩
        | false =>
          refine ⟨Nat.le_succ _, hao, trivial,
            fun _ => ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩⟩
      | inr k2 =>
        refine ⟨Nat.le_succ _, hao, hr2,
          fun _ => ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩⟩
  | inr k1 =>
    cases r2 with
    | inl b2 =>
      cases b2 with
      | true =>
        refine ⟨Nat.le_succ _, hao, trivial,
          fun _ => ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩⟩
      | false =>
        refine ⟨Nat.le_succ _, hao, hr1,
          fun _ => ⟨⟨[], by simp [combineOr]⟩, by simp [combineOr, repVal]⟩⟩
    | inr k2 =>
      simp only [combineOr]
      refine ⟨by simp, isAO2_append_singleton n gs GateOp.or k1 k2 hao (Or.inr rfl) hr1 hr2,
        by simp [repBound], fun x => ⟨⟨[⟨GateOp.or, [k1, k2]⟩], rfl⟩, ?_⟩⟩
      rw [evalGates_append_singleton]
      simp only [wireStep, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false, repVal]
      have hlen : (evalGates gs (List.ofFn x)).length = n + gs.length := by
        rw [evalGates_length, List.length_ofFn]
      rw [← hlen]
      exact getD_append_singleton_self _ _ false

lemma evalGates_append_prefix (gs extra : List Gate) (x : List Bool) :
    ∃ suffix : List Bool, evalGates (gs ++ extra) x = evalGates gs x ++ suffix := by
  rw [evalGates_append]
  have h1 : ∀ (l : List Gate) (w : List Bool), ∃ s : List Bool, evalGates l w = w ++ s := by
    intro l
    induction l with
    | nil => intro w; exact ⟨[], by simp [evalGates]⟩
    | cons g' l' ih' =>
      intro w
      rcases ih' (wireStep w g') with ⟨s, hs⟩
      exact ⟨[g'.op.eval (g'.inputs.map fun i => w.getD i false)] ++ s, by
        simpa [evalGates, wireStep, List.append_assoc] using hs⟩
  exact h1 extra (evalGates gs x)

lemma inv_step_aux (n : ℕ) (pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (res : (Bool ⊕ ℕ) × List Gate)
    (hinv : Inv n pre st)
    (hlen : res.2.length ≤ st.2.length + 1)
    (hao : IsAO2 n ⟨res.2, 0⟩)
    (hbd : repBound (n + res.2.length) res.1)
    (hext : ∃ extra : List Gate, res.2 = st.2 ++ extra)
    (hval : ∀ x : Fin n → Bool,
      repVal (evalGates res.2 (List.ofFn x)) res.1 =
        g.op.eval (g.inputs.map fun i => (evalGates pre (List.ofFn x)).getD i false)) :
    Inv n (pre ++ [g]) (st.1 ++ [res.1], res.2) := by
  rcases hinv with ⟨h1, h2, _, h4, h5⟩
  rcases hext with ⟨extra, hextra⟩
  have hle_out : st.2.length ≤ res.2.length := by rw [hextra]; simp
  refine ⟨?_, ?_, hao, ?_, ?_⟩
  · simp [h1]; omega
  · simp; omega
  · intro w
    dsimp only
    by_cases hw : w < st.1.length
    · rw [getD_append_left st.1 [res.1] w (Sum.inl false) hw]
      exact repBound_mono (by omega) (h4 w)
    · by_cases hweq : w = st.1.length
      · subst hweq
        rw [getD_append_singleton_self]
        exact hbd
      · have hgt : (st.1 ++ [res.1]).length ≤ w := by simp; omega
        rw [getD_of_le _ _ _ hgt]
        trivial
  · intro x w
    dsimp only
    rw [evalGates_append_singleton]
    simp only [wireStep]
    have hprelen : (evalGates pre (List.ofFn x)).length = st.1.length := by
      rw [evalGates_length, List.length_ofFn, h1]
    by_cases hw : w < st.1.length
    · rw [getD_append_left _ _ w false (by omega)]
      rw [getD_append_left st.1 [res.1] w (Sum.inl false) hw]
      rw [h5 x w, hextra]
      rcases evalGates_append_prefix st.2 extra (List.ofFn x) with ⟨suf, hsuf⟩
      rw [hsuf]
      have houtlen : (evalGates st.2 (List.ofFn x)).length = n + st.2.length := by
        rw [evalGates_length, List.length_ofFn]
      rw [repVal_append _ suf _ (by rw [houtlen]; exact h4 w)]
    · by_cases hweq : w = st.1.length
      · subst hweq
        rw [getD_append_singleton_self]
        rw [← hprelen]
        rw [getD_append_singleton_self]
        exact (hval x).symm
      · have hgt1 : (evalGates pre (List.ofFn x) ++
            [g.op.eval (g.inputs.map fun i => (evalGates pre (List.ofFn x)).getD i false)]).length ≤ w := by
          simp [hprelen]; omega
        have hgt2 : (st.1 ++ [res.1]).length ≤ w := by simp; omega
        rw [getD_of_le _ _ _ hgt1, getD_of_le _ _ _ hgt2]
        rfl

lemma inv_step (n : ℕ) (pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hinv : Inv n pre st) :
    Inv n (pre ++ [g]) (stepGate n st g) := by
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hinv with ⟨h1, h2, h3, h4, h5⟩
  have hinvFull : Inv n pre st := ⟨h1, h2, h3, h4, h5⟩
  rcases hop with hop | hop
  · match hins : g.inputs with
    | [] =>
      have hst : stepGate n st g = (st.1 ++ [Sum.inl true], st.2) := by
        simp [stepGate, hop, hins]
      rw [hst]
      refine inv_step_aux n pre st g (Sum.inl true, st.2) hinvFull (Nat.le_succ _) h3 trivial
        ⟨[], by simp⟩ ?_
      intro x
      rw [hop, hins]
      rfl
    | [i] =>
      have hst : stepGate n st g = (st.1 ++ [st.1.getD i (Sum.inl false)], st.2) := by
        simp [stepGate, hop, hins]
      rw [hst]
      refine inv_step_aux n pre st g (st.1.getD i (Sum.inl false), st.2) hinvFull (Nat.le_succ _)
        h3 (h4 i) ⟨[], by simp⟩ ?_
      intro x
      rw [hop, hins]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true]
      exact (h5 x i).symm
    | [i, j] =>
      have hst : stepGate n st g =
          (st.1 ++ [(combineAnd n st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).1],
           (combineAnd n st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).2) := by
        simp [stepGate, hop, hins]
      rw [hst]
      have hc := combineAnd_spec n st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))
        h3 (h4 i) (h4 j)
      rcases hc with ⟨hc1, hc2, hc3, hc4⟩
      refine inv_step_aux n pre st g _ hinvFull hc1 hc2 hc3 (hc4 (fun _ => false)).1 ?_
      intro x
      rw [(hc4 x).2, hop, hins]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true]
      rw [h5 x i, h5 x j]
    | i :: j :: k :: rest =>
      simp [hins] at hlen
  · match hins : g.inputs with
    | [] =>
      have hst : stepGate n st g = (st.1 ++ [Sum.inl false], st.2) := by
        simp [stepGate, hop, hins]
      rw [hst]
      refine inv_step_aux n pre st g (Sum.inl false, st.2) hinvFull (Nat.le_succ _) h3 trivial
        ⟨[], by simp⟩ ?_
      intro x
      rw [hop, hins]
      rfl
    | [i] =>
      have hst : stepGate n st g = (st.1 ++ [st.1.getD i (Sum.inl false)], st.2) := by
        simp [stepGate, hop, hins]
      rw [hst]
      refine inv_step_aux n pre st g (st.1.getD i (Sum.inl false), st.2) hinvFull (Nat.le_succ _)
        h3 (h4 i) ⟨[], by simp⟩ ?_
      intro x
      rw [hop, hins]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      exact (h5 x i).symm
    | [i, j] =>
      have hst : stepGate n st g =
          (st.1 ++ [(combineOr n st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).1],
           (combineOr n st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))).2) := by
        simp [stepGate, hop, hins]
      rw [hst]
      have hc := combineOr_spec n st.2 (st.1.getD i (Sum.inl false)) (st.1.getD j (Sum.inl false))
        h3 (h4 i) (h4 j)
      rcases hc with ⟨hc1, hc2, hc3, hc4⟩
      refine inv_step_aux n pre st g _ hinvFull hc1 hc2 hc3 (hc4 (fun _ => false)).1 ?_
      intro x
      rw [(hc4 x).2, hop, hins]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [h5 x i, h5 x j]
    | i :: j :: k :: rest =>
      simp [hins] at hlen

lemma inv_init (n : ℕ) : Inv n [] (initState n) := by
  refine ⟨by simp [initState], by simp [initState], ?_, ?_, ?_⟩
  · refine ⟨by intro g hg; simp [initState] at hg,
            by intro j hj; simp [initState] at hj,
            by intro g hg; simp [initState] at hg⟩
  · intro w
    by_cases hw : w < n
    · simp [initState, List.getD_eq_getElem?_getD, hw, repBound]
    · have hge : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length ≤ w := by
        simp; omega
      rw [initState, getD_of_le _ _ _ hge]
      trivial
  · intro x w
    by_cases hw : w < n
    · simp [initState, evalGates, List.getD_eq_getElem?_getD, hw, repVal]
    · have hge1 : (List.ofFn x).length ≤ w := by simp; omega
      have hge2 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Bool ⊕ ℕ))).length ≤ w := by
        simp; omega
      simp only [initState, evalGates, List.foldl_nil]
      rw [getD_of_le _ _ _ hge1, getD_of_le _ _ _ hge2]
      rfl

lemma inv_foldl (n : ℕ) :
    ∀ (rest pre : List Gate) (st : List (Bool ⊕ ℕ) × List Gate),
      (∀ g ∈ rest, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      Inv n pre st →
      Inv n (pre ++ rest) (rest.foldl (stepGate n) st)
  | [], pre, st, _, hinv => by simpa using hinv
  | g :: rest, pre, st, hmono, hinv => by
    have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hmono g (by simp)
    have hrest : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (by simp [hg'])
    have hstep : Inv n (pre ++ [g]) (stepGate n st g) := inv_step n pre st g hg hinv
    have hrec := inv_foldl n rest (pre ++ [g]) (stepGate n st g) hrest hstep
    simpa [List.append_assoc] using hrec

lemma main_proof (x1 : ℕ) (x2 : Circuit) (hmono : Monotone2 x2)
    (hfalse : circuitFun x1 x2 (fun _ : Fin x1 => Bool.false) = Bool.false) :
    ∃ x5 : Circuit, IsAO2 x1 x5 ∧ x5.size ≤ x2.size ∧ circuitFun x1 x5 = circuitFun x1 x2 := by
  let st := x2.gates.foldl (stepGate x1) (initState x1)
  have hinv : Inv x1 x2.gates st := by
    simpa using inv_foldl x1 x2.gates [] (initState x1) hmono (inv_init x1)
  rcases hinv with ⟨_, hsz, hao, _, hev⟩
  cases hr : st.1.getD x2.output (Sum.inl false) with
  | inl b =>
    cases b with
    | true =>
      have h0 := hev (fun _ : Fin x1 => Bool.false) x2.output
      rw [hr] at h0
      simp only [repVal] at h0
      have hc : circuitFun x1 x2 (fun _ : Fin x1 => Bool.false) = Bool.true := h0
      rw [hfalse] at hc
      exact Bool.noConfusion hc
    | false =>
      refine ⟨⟨st.2, x1 + st.2.length⟩, isAO2_change_output x1 st.2 0 _ hao, hsz, ?_⟩
      funext x
      have hx := hev x x2.output
      rw [hr] at hx
      simp only [repVal] at hx
      have hlen : (evalGates st.2 (List.ofFn x)).length = x1 + st.2.length := by
        rw [evalGates_length, List.length_ofFn]
      have hout : circuitFun x1 ⟨st.2, x1 + st.2.length⟩ x = Bool.false := by
        change (evalGates st.2 (List.ofFn x)).getD (x1 + st.2.length) false = false
        rw [← hlen]
        exact getD_of_le _ _ false (Nat.le_refl _)
      exact hout.trans hx.symm
  | inr k =>
    refine ⟨⟨st.2, k⟩, isAO2_change_output x1 st.2 0 k hao, hsz, ?_⟩
    funext x
    have hx := hev x x2.output
    rw [hr] at hx
    simp only [repVal] at hx
    exact hx.symm

end PEqualNP.Outside.L_meta_4342

theorem PEqualNP.Outside.L_meta_4342 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x4 : Fin x1) => Bool.false) = Bool.false → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  exact PEqualNP.Outside.L_meta_4342.main_proof
