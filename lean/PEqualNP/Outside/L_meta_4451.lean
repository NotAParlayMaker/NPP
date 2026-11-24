import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

private def runWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w

private lemma runWires_append (gs1 gs2 : List Gate) (w : List Bool) :
    runWires (gs1 ++ gs2) w = runWires gs2 (runWires gs1 w) := by
  simp [runWires, List.foldl_append]

private lemma length_runWires (gs : List Gate) : ∀ w : List Bool,
    (runWires gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [runWires]
  | cons g gs ih =>
    intro w
    change (runWires gs (w ++ [_])).length = w.length + (gs.length + 1)
    rw [ih]
    simp; omega

private lemma getD_snoc_ne {α : Type} (L : List α) (a d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [a]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma getD_snoc_eq {α : Type} (L : List α) (a d : α) :
    (L ++ [a]).getD L.length d = a := by
  simp

private lemma getD_mem_or_default {α : Type} (L : List α) (i : ℕ) (d : α) :
    L.getD i d ∈ L ∨ L.getD i d = d := by
  by_cases h : i < L.length
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ (by omega)

private lemma runWires_input (gs : List Gate) : ∀ (w : List Bool) (i : ℕ),
    i < w.length → (runWires gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    change (runWires gs (w ++ [_])).getD i false = w.getD i false
    rw [ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]

private lemma monotone_gate (g : Gate) (w1 w2 : List Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hle i (h _ ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hle i hb⟩

private lemma monotone_runWires (gs : List Gate) : ∀ (w1 w2 : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    w1.length = w2.length →
    (∀ i, w1.getD i false = true → w2.getD i false = true) →
    ∀ i, (runWires gs w1).getD i false = true → (runWires gs w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ _ hle; exact hle
  | cons g gs ih =>
    intro w1 w2 hgs hlen hle
    have hg := hgs g List.mem_cons_self
    have hgs' := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    apply ih (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
      (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) hgs' (by simp [hlen])
    intro i hi
    by_cases h1 : i = w1.length
    · subst h1
      rw [getD_snoc_eq] at hi
      rw [hlen, getD_snoc_eq]
      exact monotone_gate g w1 w2 hg hle hi
    · rw [getD_snoc_ne w1 _ _ _ h1] at hi
      rw [getD_snoc_ne w2 _ _ _ (by omega)]
      exact hle i hi

private lemma monotone_circuitFun (n : ℕ) (C : Circuit) (hAO : AndOrOnly C)
    (x y : Fin n → Bool) (hle : ∀ i, x i = true → y i = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply monotone_runWires C.gates (List.ofFn x) (List.ofFn y) hAO (by simp)
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn] at hi ⊢
    exact hle ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

private lemma agree_except (k : ℕ) (gs : List Gate) : ∀ (w1 w2 : List Bool),
    (∀ g ∈ gs, k ∉ g.inputs) →
    w1.length = w2.length →
    (∀ i, i ≠ k → w1.getD i false = w2.getD i false) →
    ∀ i, i ≠ k → (runWires gs w1).getD i false = (runWires gs w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ _ h; exact h
  | cons g gs ih =>
    intro w1 w2 hno hlen h
    have hgk : k ∉ g.inputs := hno g List.mem_cons_self
    have hsame : (g.inputs.map fun i => w1.getD i false) = g.inputs.map fun i => w2.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hgk (e ▸ ha)))
    apply ih (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
      (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hlen])
    intro i hi
    by_cases h1 : i = w1.length
    · rw [h1, getD_snoc_eq, hlen, getD_snoc_eq, hsame]
    · rw [getD_snoc_ne w1 _ _ _ h1, getD_snoc_ne w2 _ _ _ (by omega)]
      exact h i hi

private lemma exists_gate_reading_u (n : ℕ) (C : Circuit) (u v : Fin n)
    (hu : circuitFun n C (fun i => decide (i = u)) = false)
    (hv : circuitFun n C (fun i => decide (i = v)) = false)
    (huv_true : circuitFun n C (fun i => decide (i = u ∨ i = v)) = true) :
    ∃ g ∈ C.gates, u.val ∈ g.inputs := by
  have hout : C.output ≠ u.val := by
    intro h
    have h1 : circuitFun n C (fun i => decide (i = u)) = true := by
      change (runWires C.gates (List.ofFn (fun i : Fin n => decide (i = u)))).getD C.output false = true
      rw [h, runWires_input _ _ _ (by simp [u.isLt]), List.getD_eq_getElem _ _ (by simp [u.isLt]),
          List.getElem_ofFn]
      simp
    rw [h1] at hu
    cases hu
  by_contra hno
  push_neg at hno
  have heq := agree_except u.val C.gates
    (List.ofFn (fun i : Fin n => decide (i = v)))
    (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v)))
    hno (by simp)
    (fun i hi => by
      by_cases hlt : i < n
      · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
            List.getElem_ofFn, List.getElem_ofFn]
        have hne : (⟨i, hlt⟩ : Fin n) ≠ u := fun e => hi (congrArg Fin.val e)
        simp [hne]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
    C.output hout
  change circuitFun n C (fun i => decide (i = v)) = circuitFun n C (fun i => decide (i = u ∨ i = v)) at heq
  rw [hv, huv_true] at heq
  cases heq

private def elimStep (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate) :
    List Gate × List (Option ℕ) :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] =>
    match st.2.getD a none, st.2.getD b none with
    | some a', some b' => (st.1 ++ [⟨GateOp.and, [a', b']⟩], st.2 ++ [some (n + st.1.length)])
    | _, _ => (st.1, st.2 ++ [none])
  | GateOp.or, [a, b] =>
    match st.2.getD a none, st.2.getD b none with
    | some a', some b' => (st.1 ++ [⟨GateOp.or, [a', b']⟩], st.2 ++ [some (n + st.1.length)])
    | some a', none => (st.1, st.2 ++ [some a'])
    | none, some b' => (st.1, st.2 ++ [some b'])
    | none, none => (st.1, st.2 ++ [none])
  | _, _ => (st.1, st.2 ++ [none])

private def elimAux (n : ℕ) (gs : List Gate) (st : List Gate × List (Option ℕ)) :
    List Gate × List (Option ℕ) :=
  gs.foldl (elimStep n) st

private lemma elimAux_cons (n : ℕ) (g : Gate) (gs : List Gate) (st : List Gate × List (Option ℕ)) :
    elimAux n (g :: gs) st = elimAux n gs (elimStep n st g) := rfl

private lemma elimStep_len_le (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate) :
    (elimStep n st g).1.length ≤ st.1.length + 1 ∧
    (elimStep n st g).2.length = st.2.length + 1 := by
  unfold elimStep
  split <;> (try split) <;> simp

private lemma elimAux_len_le (n : ℕ) (gs : List Gate) : ∀ st : List Gate × List (Option ℕ),
    (elimAux n gs st).1.length ≤ st.1.length + gs.length := by
  induction gs with
  | nil => intro st; simp [elimAux]
  | cons g gs ih =>
    intro st
    rw [elimAux_cons]
    have h1 := ih (elimStep n st g)
    have h2 := (elimStep_len_le n st g).1
    simp only [List.length_cons]
    omega

private lemma elimStep_preserves_none (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate)
    (u : ℕ) (hu : u < st.2.length) (hnone : st.2.getD u none = none) :
    (elimStep n st g).2.getD u none = none := by
  unfold elimStep
  split <;> (try split) <;> (dsimp only; rw [getD_snoc_ne st.2 _ _ _ (by omega)]; exact hnone)

private lemma elimStep_drops_on_none (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate)
    (u : ℕ) (hnone : st.2.getD u none = none) (hu : u ∈ g.inputs) :
    (elimStep n st g).1.length = st.1.length := by
  unfold elimStep
  split
  · rename_i a b heq1 heq2
    rw [heq2] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · simp only [hnone]
    · cases st.2.getD a none <;> simp only [hnone]
  · rename_i a b heq1 heq2
    rw [heq2] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · cases st.2.getD b none <;> simp only [hnone]
    · cases st.2.getD a none <;> simp only [hnone]
  · rfl

private lemma elimAux_len_lt (n : ℕ) (gs : List Gate) (u : ℕ) :
    ∀ st : List Gate × List (Option ℕ),
      u < st.2.length →
      st.2.getD u none = none →
      (∃ g ∈ gs, u ∈ g.inputs) →
      (elimAux n gs st).1.length < st.1.length + gs.length := by
  induction gs with
  | nil => intro st _ _ hex; rcases hex with ⟨g, hg, _⟩; simp at hg
  | cons g gs ih =>
    intro st hu hnone hex
    rw [elimAux_cons]
    by_cases hgu : u ∈ g.inputs
    · have hdrop := elimStep_drops_on_none n st g u hnone hgu
      have hle := elimAux_len_le n gs (elimStep n st g)
      simp only [List.length_cons]
      omega
    · have hex' : ∃ g' ∈ gs, u ∈ g'.inputs := by
        rcases hex with ⟨g', hg', hmem⟩
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact absurd hmem hgu
        · exact ⟨g', hg', hmem⟩
      have hlt := ih (elimStep n st g)
        (by rw [(elimStep_len_le n st g).2]; omega)
        (elimStep_preserves_none n st g u hu hnone) hex'
      have hle := (elimStep_len_le n st g).1
      simp only [List.length_cons]
      omega

private def StateOk (n : ℕ) (st : List Gate × List (Option ℕ)) : Prop :=
  (∀ g ∈ st.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < st.1.length, ∀ i ∈ (st.1.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧
  (∀ v ∈ st.2, ∀ k, v = some k → k < n + st.1.length)

private lemma elimStep_stateOk (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate)
    (hok : StateOk n st) : StateOk n (elimStep n st g) := by
  rcases hok with ⟨h1, h2, h3⟩
  have hmem_bound : ∀ idx k, st.2.getD idx none = some k → k < n + st.1.length := by
    intro idx k hk
    rcases getD_mem_or_default st.2 idx none with hm | hm
    · exact h3 _ hm k hk
    · rw [hm] at hk; cases hk
  have hstay : StateOk n (st.1, st.2 ++ [none]) := by
    refine ⟨h1, h2, ?_⟩
    intro v hv k hk
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact h3 v hv k hk
    · cases hk
  have hstaySome : ∀ a', a' < n + st.1.length → StateOk n (st.1, st.2 ++ [some a']) := by
    intro a' ha'
    refine ⟨h1, h2, ?_⟩
    intro v hv k hk
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact h3 v hv k hk
    · cases hk; exact ha'
  have hemit : ∀ op (a' b' : ℕ), (op = GateOp.and ∨ op = GateOp.or) →
      a' < n + st.1.length → b' < n + st.1.length →
      StateOk n (st.1 ++ [⟨op, [a', b']⟩], st.2 ++ [some (n + st.1.length)]) := by
    intro op a' b' hop ha' hb'
    refine ⟨?_, ?_, ?_⟩
    · intro g' hg'
      simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | rfl
      · exact h1 g' hg'
      · exact ⟨hop, rfl⟩
    · intro j hj i hi
      by_cases hjl : j < st.1.length
      · rw [List.getD_append _ _ _ _ hjl] at hi
        exact h2 j hjl i hi
      · have hjeq : j = st.1.length := by simp at hj; omega
        subst hjeq
        rw [getD_snoc_eq] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption
    · intro v hv k hk
      simp only [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · have := h3 v hv k hk
        simp; omega
      · cases hk; simp
  unfold elimStep
  split
  · rename_i a b _ _
    split
    · rename_i a' b' ha hb
      exact hemit GateOp.and a' b' (Or.inl rfl) (hmem_bound a a' ha) (hmem_bound b b' hb)
    · exact hstay
  · rename_i a b _ _
    split
    · rename_i a' b' ha hb
      exact hemit GateOp.or a' b' (Or.inr rfl) (hmem_bound a a' ha) (hmem_bound b b' hb)
    · rename_i a' ha _
      exact hstaySome a' (hmem_bound a a' ha)
    · rename_i b' _ hb
      exact hstaySome b' (hmem_bound b b' hb)
    · exact hstay
  · exact hstay

private lemma elimAux_stateOk (n : ℕ) (gs : List Gate) : ∀ st : List Gate × List (Option ℕ),
    StateOk n st → StateOk n (elimAux n gs st) := by
  induction gs with
  | nil => intro st hok; exact hok
  | cons g gs ih => intro st hok; exact ih _ (elimStep_stateOk n st g hok)

private def MatchState (base : List Bool) (st : List Gate × List (Option ℕ)) (w : List Bool) : Prop :=
  st.2.length = w.length ∧
  ∀ i, match st.2.getD i none with
    | none => w.getD i false = false
    | some k => (runWires st.1 base).getD k false = w.getD i false

private lemma elimStep_sound (n : ℕ) (base : List Bool) (hbase : base.length = n)
    (st : List Gate × List (Option ℕ)) (w : List Bool) (g : Gate)
    (hok : StateOk n st)
    (hmatch : MatchState base st w)
    (hAO : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) :
    MatchState base (elimStep n st g)
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := by
  rcases hmatch with ⟨hmlen, hm⟩
  have hw'len : (runWires st.1 base).length = n + st.1.length := by
    rw [length_runWires, hbase]
  rcases g with ⟨op, inputs⟩
  simp only at hAO hlen
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · have hma := hm a
    have hmb := hm b
    have hsame_prev : ∀ (v : Option ℕ) (val : Bool),
        (match v with | none => val = false | some k => (runWires st.1 base).getD k false = val) →
        MatchState base (st.1, st.2 ++ [v]) (w ++ [val]) := by
      intro v val hv
      refine ⟨by simp [hmlen], ?_⟩
      intro i
      by_cases hi : i = st.2.length
      · subst hi
        rw [getD_snoc_eq, hmlen, getD_snoc_eq]
        exact hv
      · rw [getD_snoc_ne st.2 _ _ _ hi, getD_snoc_ne w _ _ _ (by omega)]
        exact hm i
    have hemit_ok : ∀ (a' b' : ℕ),
        st.2.getD a none = some a' →
        st.2.getD b none = some b' →
        MatchState base (st.1 ++ [⟨op, [a', b']⟩], st.2 ++ [some (n + st.1.length)])
          (w ++ [op.eval (List.map (fun i => w.getD i false) [a, b])]) := by
      intro a' b' ha hb
      rw [ha] at hma
      rw [hb] at hmb
      have hrun : runWires (st.1 ++ [⟨op, [a', b']⟩]) base =
          runWires st.1 base ++ [op.eval [w.getD a false, w.getD b false]] := by
        rw [runWires_append]
        change runWires st.1 base ++ [op.eval [(runWires st.1 base).getD a' false, (runWires st.1 base).getD b' false]] = _
        rw [hma, hmb]
      refine ⟨by simp [hmlen], ?_⟩
      intro i
      by_cases hi : i = st.2.length
      · subst hi
        rw [getD_snoc_eq, hmlen, getD_snoc_eq]
        dsimp only
        rw [hrun, ← hw'len, getD_snoc_eq]
        rfl
      · rw [getD_snoc_ne st.2 _ _ _ hi, getD_snoc_ne w _ _ _ (by omega)]
        have hmi := hm i
        cases hst : st.2.getD i none with
        | none =>
          rw [hst] at hmi
          exact hmi
        | some k =>
          rw [hst] at hmi
          dsimp only
          have hklt : k < (runWires st.1 base).length := by
            rw [hw'len]
            rcases getD_mem_or_default st.2 i none with hmem | hdef
            · exact hok.2.2 _ hmem k hst
            · rw [hdef] at hst; cases hst
          rw [hrun, getD_snoc_ne (runWires st.1 base) _ _ _ (by omega)]
          exact hmi
    rcases hAO with rfl | rfl
    · unfold elimStep
      dsimp only
      cases ha : st.2.getD a none with
      | none =>
        rw [ha] at hma; dsimp only at hma
        simp only
        exact hsame_prev none _ (by simp only [List.map_cons, List.map_nil, GateOp.eval, hma]; rfl)
      | some a' =>
        cases hb : st.2.getD b none with
        | none =>
          rw [hb] at hmb; dsimp only at hmb
          simp only
          exact hsame_prev none _ (by simp only [List.map_cons, List.map_nil, GateOp.eval, hmb]; simp)
        | some b' =>
          simp only
          exact hemit_ok a' b' ha hb
    · unfold elimStep
      dsimp only
      cases ha : st.2.getD a none with
      | none =>
        rw [ha] at hma; dsimp only at hma
        cases hb : st.2.getD b none with
        | none =>
          rw [hb] at hmb; dsimp only at hmb
          simp only
          exact hsame_prev none _ (by simp only [List.map_cons, List.map_nil, GateOp.eval, hma, hmb]; rfl)
        | some b' =>
          rw [hb] at hmb; dsimp only at hmb
          simp only
          exact hsame_prev (some b') _ (by simp only [List.map_cons, List.map_nil, GateOp.eval, hma, hmb]; simp)
      | some a' =>
        rw [ha] at hma; dsimp only at hma
        cases hb : st.2.getD b none with
        | none =>
          rw [hb] at hmb; dsimp only at hmb
          simp only
          exact hsame_prev (some a') _ (by simp only [List.map_cons, List.map_nil, GateOp.eval, hma, hmb]; simp)
        | some b' =>
          simp only
          exact hemit_ok a' b' ha hb
  · simp at hlen

private lemma elimAux_sound (n : ℕ) (base : List Bool) (hbase : base.length = n) (gs : List Gate) :
    ∀ (st : List Gate × List (Option ℕ)) (w : List Bool),
      StateOk n st →
      MatchState base st w →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      MatchState base (elimAux n gs st) (runWires gs w) := by
  induction gs with
  | nil => intro st w _ hm _; exact hm
  | cons g gs ih =>
    intro st w hok hm hgs
    have hg := hgs g List.mem_cons_self
    have hgs' := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    rw [elimAux_cons]
    exact ih _ _ (elimStep_stateOk n st g hok)
      (elimStep_sound n base hbase st w g hok hm hg.1 hg.2) hgs'

private lemma main_elim (n : ℕ) (C : Circuit) (u v : Fin n)
    (hAO : IsAO2 n C)
    (hu : circuitFun n C (fun i => decide (i = u)) = false)
    (hv : circuitFun n C (fun i => decide (i = v)) = false)
    (huv_true : circuitFun n C (fun i => decide (i = u ∨ i = v)) = true) :
    ∃ D : Circuit,
      IsAO2 n D ∧
      D.size < C.size ∧
      (∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true) ∧
      (∀ x : Fin n → Bool, x u = false → circuitFun n D x = circuitFun n C x) := by
  let st0 : List Gate × List (Option ℕ) :=
    ([], List.ofFn fun i : Fin n => if i = u then none else some i.val)
  let res := elimAux n C.gates st0
  let out : ℕ := match res.2.getD C.output none with
    | some k => k
    | none => n + res.1.length
  let D : Circuit := ⟨res.1, out⟩
  have hst0_ok : StateOk n st0 := by
    refine ⟨by simp [st0], by simp [st0], ?_⟩
    intro a ha k hk
    simp only [st0, List.mem_ofFn] at ha
    rcases ha with ⟨i, rfl⟩
    by_cases hi : i = u
    · simp [hi] at hk
    · simp only [hi, ↓reduceIte, Option.some.injEq] at hk
      subst hk
      simp only [st0, List.length_nil, Nat.add_zero]
      exact i.isLt
  have hres_ok : StateOk n res := elimAux_stateOk n C.gates st0 hst0_ok
  have hD_AO2 : IsAO2 n D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg; exact (hres_ok.1 g hg).1
    · intro j hj i hi; exact hres_ok.2.1 j hj i hi
    · intro g hg; exact (hres_ok.1 g hg).2
  have hex : ∃ g ∈ C.gates, u.val ∈ g.inputs := exists_gate_reading_u n C u v hu hv huv_true
  have hD_size : D.size < C.size := by
    change res.1.length < C.gates.length
    have hnone : st0.2.getD u.val none = none := by
      rw [List.getD_eq_getElem _ _ (by simp [st0, u.isLt])]
      simp [st0]
    have hlt := elimAux_len_lt n C.gates u.val st0 (by simp [st0, u.isLt]) hnone hex
    simpa [st0] using hlt
  have hD_eval : ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (Function.update x u false) := by
    intro x
    have hm0 : MatchState (List.ofFn x) st0 (List.ofFn (Function.update x u false)) := by
      refine ⟨by simp [st0], ?_⟩
      intro i
      by_cases hlt : i < n
      · have hst0i : st0.2.getD i none = if (⟨i, hlt⟩ : Fin n) = u then none else some i := by
          rw [List.getD_eq_getElem _ _ (by simp [st0, hlt])]
          simp [st0]
        rw [hst0i]
        by_cases hiu : (⟨i, hlt⟩ : Fin n) = u
        · rw [ite_eq_left hiu]
          dsimp only
          rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn, hiu]
          simp
        · rw [ite_eq_right hiu]
          dsimp only
          change (List.ofFn x).getD i false = (List.ofFn (Function.update x u false)).getD i false
          rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
              List.getElem_ofFn, List.getElem_ofFn]
          simp [hiu]
      · rw [List.getD_eq_default st0.2 _ (by simp [st0]; omega),
            List.getD_eq_default _ _ (by simp; omega)]
    have hmres := elimAux_sound n (List.ofFn x) (by simp) C.gates st0
      (List.ofFn (Function.update x u false)) hst0_ok hm0
      (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩)
    have hmo := hmres.2 C.output
    change (runWires res.1 (List.ofFn x)).getD out false =
      (runWires C.gates (List.ofFn (Function.update x u false))).getD C.output false
    cases hco : res.2.getD C.output none with
    | none =>
      rw [hco] at hmo
      have hout_eq : out = n + res.1.length := by simp only [out, hco]
      rw [hout_eq, hmo, List.getD_eq_default _ _ (by rw [length_runWires]; simp)]
    | some k =>
      rw [hco] at hmo
      have hout_eq : out = k := by simp only [out, hco]
      rw [hout_eq]
      exact hmo
  refine ⟨D, hD_AO2, hD_size, ?_, ?_⟩
  · intro x hx
    rw [hD_eval x] at hx
    refine monotone_circuitFun n C hAO.1 (Function.update x u false) x ?_ hx
    intro i hi
    by_cases hiu : i = u
    · subst hiu; simp at hi
    · simpa [hiu] using hi
  · intro x hxu
    rw [hD_eval x]
    have hupd : Function.update x u false = x := by
      funext i
      by_cases hiu : i = u
      · subst hiu; simp [hxu]
      · simp [hiu]
    rw [hupd]

end PEqualNP.Outside.L_meta_4451

theorem PEqualNP.Outside.L_meta_4451 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x3 ≠ x4 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => Decidable.decide (x7 = x3)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x8 : Fin x1) => Decidable.decide (x8 = x4)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x9 : Fin x1) => Decidable.decide (x9 = x3 ∨ x9 = x4)) = Bool.true → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x10 ∧ x10.size < x2.size ∧ (∀ (x11 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x11 = Bool.true) ∧ ∀ (x11 : Fin x1 → Bool), x11 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x2 x11 := by
  intro n C u v hAO _ hu hv huv_true
  exact PEqualNP.Outside.L_meta_4451.main_elim n C u v hAO hu hv huv_true
