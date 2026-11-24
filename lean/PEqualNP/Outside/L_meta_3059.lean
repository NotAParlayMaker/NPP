import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3059

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive WireVal where
  | const (b : Bool)
  | wire (idx : ℕ) (pol : Bool)
  deriving DecidableEq

def WireVal.neg : WireVal → WireVal
  | .const b => .const (!b)
  | .wire i p => .wire i (!p)

def WireVal.xorPol (p : Bool) : WireVal → WireVal
  | .const b => .const (b != p)
  | .wire i q => .wire i (q != p)

def WireVal.eval (w : List Bool) : WireVal → Bool
  | .const b => b
  | .wire i p => w.getD i false != p

def WireVal.wf (n : ℕ) : WireVal → Prop
  | .const _ => True
  | .wire i _ => i < n

lemma WireVal.eval_neg (w : List Bool) (v : WireVal) :
    v.neg.eval w = !(v.eval w) := by
  cases v with
  | const b => rfl
  | wire i p => simp only [WireVal.neg, WireVal.eval]; cases w.getD i false <;> cases p <;> rfl

lemma WireVal.eval_xorPol (w : List Bool) (p : Bool) (v : WireVal) :
    (v.xorPol p).eval w = (v.eval w != p) := by
  cases v with
  | const b => rfl
  | wire i q => simp only [WireVal.xorPol, WireVal.eval]; cases w.getD i false <;> cases q <;> cases p <;> rfl

lemma WireVal.eval_append (w extra : List Bool) (v : WireVal) (h : v.wf w.length) :
    v.eval (w ++ extra) = v.eval w := by
  cases v with
  | const b => rfl
  | wire i p =>
    simp only [WireVal.eval]
    rw [List.getD_append w extra false i h]

lemma WireVal.wf_mono {m n : ℕ} (hmn : m ≤ n) {v : WireVal} (hv : v.wf m) : v.wf n := by
  cases v with
  | const _ => trivial
  | wire i _ => exact lt_of_lt_of_le hv hmn

lemma WireVal.wf_neg {n : ℕ} {v : WireVal} (hv : v.wf n) : v.neg.wf n := by
  cases v <;> exact hv

lemma WireVal.wf_xorPol {n : ℕ} (p : Bool) {v : WireVal} (hv : v.wf n) : (v.xorPol p).wf n := by
  cases v <;> exact hv

structure DMGate where
  isOr : Bool
  l : ℕ
  pl : Bool
  r : ℕ
  pr : Bool

def DMGate.eval (w : List Bool) (g : DMGate) : Bool :=
  let a := w.getD g.l false != g.pl
  let b := w.getD g.r false != g.pr
  if g.isOr then a || b else a && b

def dmStep (w : List Bool) (g : DMGate) : List Bool :=
  w ++ [g.eval w]

structure DMCircuit where
  gates : List DMGate
  out : WireVal

def DMCircuit.wires (C : DMCircuit) (inp : List Bool) : List Bool :=
  C.gates.foldl dmStep inp

def DMCircuit.eval (C : DMCircuit) (inp : List Bool) : Bool :=
  C.out.eval (C.wires inp)

def DMCircuit.size (C : DMCircuit) : ℕ :=
  C.gates.length

lemma foldl_dmStep_length (gs : List DMGate) (w : List Bool) :
    (gs.foldl dmStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, dmStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_dmStep_append_prefix (gs : List DMGate) (w : List Bool) :
    ∃ ext : List Bool, gs.foldl dmStep w = w ++ ext := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨ext, hext⟩ := ih (dmStep w g)
    refine ⟨g.eval w :: ext, ?_⟩
    simp only [List.foldl_cons]
    rw [hext]
    simp [dmStep]

lemma foldl_dmStep_getD_lt (gs : List DMGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl dmStep w).getD i false = w.getD i false := by
  obtain ⟨ext, hext⟩ := foldl_dmStep_append_prefix gs w
  rw [hext, List.getD_append w ext false i hi]

def combine (isOr : Bool) (nNext : ℕ) (a b : WireVal) : Option DMGate × WireVal :=
  match a, b with
  | .const ba, _ =>
    if isOr then (none, if ba then .const true else b)
    else (none, if ba then b else .const false)
  | _, .const bb =>
    if isOr then (none, if bb then .const true else a)
    else (none, if bb then a else .const false)
  | .wire ia pa, .wire ib pb =>
    if ia = ib then
      if pa = pb then (none, .wire ia pa)
      else (none, .const isOr)
    else
      (some ⟨isOr, ia, pa, ib, pb⟩, .wire nNext false)

lemma combine_spec (isOr : Bool) (w : List Bool) (a b : WireVal)
    (ha : a.wf w.length) (hb : b.wf w.length) :
    let res := combine isOr w.length a b
    let w' := match res.1 with | none => w | some g => dmStep w g
    res.2.wf w'.length ∧
    res.2.eval w' = (if isOr then a.eval w || b.eval w else a.eval w && b.eval w) := by
  cases a with
  | const ba =>
    cases isOr <;> cases ba <;>
      exact ⟨by first | exact hb | trivial, by simp [combine, WireVal.eval]⟩
  | wire ia pa =>
    cases b with
    | const bb =>
      cases isOr <;> cases bb <;>
        exact ⟨by first | exact ha | trivial, by simp [combine, WireVal.eval]⟩
    | wire ib pb =>
      by_cases hi : ia = ib
      · subst hi
        by_cases hp : pa = pb
        · subst hp
          cases isOr <;> exact ⟨by simpa [combine] using ha, by simp [combine, WireVal.eval]⟩
        · have hne : (w.getD ia false != pa) = !(w.getD ia false != pb) := by
            cases w.getD ia false <;> cases pa <;> cases pb <;> simp_all
          cases isOr <;> exact ⟨by simp [combine, hp, WireVal.wf], by
            simp only [combine, hp, ↓reduceIte, WireVal.eval]; rw [hne]
            cases w.getD ia false != pb <;> rfl⟩
      · simp only [combine, hi, ↓reduceIte, dmStep, WireVal.wf, WireVal.eval, DMGate.eval]
        refine ⟨by simp, ?_⟩
        rw [List.getD_append_right w _ false w.length (le_refl _)]
        simp

lemma combine_const_left (isOr : Bool) (nNext : ℕ) (ba : Bool) (b : WireVal) :
    (combine isOr nNext (.const ba) b).1 = none := by
  cases isOr <;> cases ba <;> rfl

lemma combine_const_right (isOr : Bool) (nNext : ℕ) (a : WireVal) (bb : Bool) :
    (combine isOr nNext a (.const bb)).1 = none := by
  cases a <;> cases isOr <;> cases bb <;> rfl

-- Part 1: Compiling FanInTwo circuits (x2, constant x4, x3) into DMCircuit on 8 inputs

def fanStep (nNew : ℕ) (st : List DMGate × List WireVal) (g : Gate) :
    List DMGate × List WireVal :=
  let acc := st.1
  let env := st.2
  let get (i : ℕ) : WireVal := env.getD i (.const false)
  match g.op with
  | .not =>
    let v : WireVal := match g.inputs with | [] => .const false | a :: _ => get a
    (acc, env ++ [v.neg])
  | .and =>
    match g.inputs with
    | [] => (acc, env ++ [.const true])
    | [a] => (acc, env ++ [get a])
    | [a, b] =>
      let res := combine false (nNew + acc.length) (get a) (get b)
      match res.1 with
      | none => (acc, env ++ [res.2])
      | some ng => (acc ++ [ng], env ++ [res.2])
    | _ => (acc, env ++ [.const false])
  | .or =>
    match g.inputs with
    | [] => (acc, env ++ [.const false])
    | [a] => (acc, env ++ [get a])
    | [a, b] =>
      let res := combine true (nNew + acc.length) (get a) (get b)
      match res.1 with
      | none => (acc, env ++ [res.2])
      | some ng => (acc ++ [ng], env ++ [res.2])
    | _ => (acc, env ++ [.const false])
  | _ => (acc, env ++ [.const false])

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fanStep_len_env (nNew : ℕ) (st : List DMGate × List WireVal) (g : Gate) :
    (fanStep nNew st g).2.length = st.2.length + 1 := by
  unfold fanStep
  cases g.op <;> try (simp; done)
  all_goals
    rcases g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp
    cases (combine _ _ _ _).1 <;> simp

lemma fanStep_env_prefix (nNew : ℕ) (st : List DMGate × List WireVal) (g : Gate) :
    ∃ v : WireVal, (fanStep nNew st g).2 = st.2 ++ [v] := by
  unfold fanStep
  cases g.op <;> try exact ⟨_, rfl⟩
  all_goals
    rcases g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> try exact ⟨_, rfl⟩
    dsimp only
    cases (combine _ _ _ _).1 <;> exact ⟨_, rfl⟩

lemma fanStep_acc_le (nNew : ℕ) (st : List DMGate × List WireVal) (g : Gate) :
    (fanStep nNew st g).1.length ≤ st.1.length + 1 := by
  unfold fanStep
  cases g.op <;> try simp
  all_goals
    rcases g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> try simp
    cases (combine _ _ _ _).1 <;> simp

lemma fanStep_acc_eq_of_hit (nNew : ℕ) (st : List DMGate × List WireVal) (g : Gate)
    (wIdx : ℕ) (c : Bool) (hc : st.2.getD wIdx (.const false) = .const c)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hhit : (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains wIdx = true) :
    (fanStep nNew st g).1.length = st.1.length := by
  rcases hfan with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · rw [hop] at hhit
    simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hhit
    rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [hi] at hhit
    · simp [fanStep, hop, hi]
    · simp [hi] at hhit
      unfold fanStep
      rw [hop, hi]
      dsimp only
      rcases hhit with rfl | rfl
      · rw [hc, combine_const_left]
      · rw [hc, combine_const_right]
    · simp [hi] at hlen
  · rw [hop] at hhit
    simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hhit
    rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [hi] at hhit
    · simp [fanStep, hop, hi]
    · simp [hi] at hhit
      unfold fanStep
      rw [hop, hi]
      dsimp only
      rcases hhit with rfl | rfl
      · rw [hc, combine_const_left]
      · rw [hc, combine_const_right]
    · simp [hi] at hlen
  · simp [fanStep, hop]

lemma fanStep_correct (nNew : ℕ) (st : List DMGate × List WireVal) (g : Gate)
    (inpNew : List Bool) (wOld : List Bool)
    (hinp : inpNew.length = nNew)
    (hlen : st.2.length = wOld.length)
    (hwf : ∀ v ∈ st.2, v.wf (nNew + st.1.length))
    (hmatch : ∀ i : ℕ, (st.2.getD i (.const false)).eval (st.1.foldl dmStep inpNew) = wOld.getD i false)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    let st' := fanStep nNew st g
    st'.2.length = (gateStep wOld g).length ∧
    (∀ v ∈ st'.2, v.wf (nNew + st'.1.length)) ∧
    (∀ i : ℕ, (st'.2.getD i (.const false)).eval (st'.1.foldl dmStep inpNew) = (gateStep wOld g).getD i false) := by
  have hwf_get : ∀ i : ℕ, (st.2.getD i (.const false)).wf (nNew + st.1.length) := by
    intro i
    by_cases hi : i < st.2.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hwf _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; trivial
  have hlen_w : (st.1.foldl dmStep inpNew).length = nNew + st.1.length := by
    rw [foldl_dmStep_length, hinp]
  have hstep_pack : ∀ (ngOpt : Option DMGate) (v : WireVal),
      (let acc' := match ngOpt with | none => st.1 | some ng => st.1 ++ [ng]
       let w' := acc'.foldl dmStep inpNew
       v.wf (nNew + acc'.length) ∧
       v.eval w' = g.op.eval (g.inputs.map fun i => wOld.getD i false)) →
      let acc' := match ngOpt with | none => st.1 | some ng => st.1 ++ [ng]
      let env' := st.2 ++ [v]
      env'.length = (gateStep wOld g).length ∧
      (∀ u ∈ env', u.wf (nNew + acc'.length)) ∧
      (∀ i : ℕ, (env'.getD i (.const false)).eval (acc'.foldl dmStep inpNew) =
        (gateStep wOld g).getD i false) := by
    intro ngOpt v ⟨hvwf, hvev⟩
    dsimp only
    have hacc_le : st.1.length ≤ (match ngOpt with | none => st.1 | some ng => st.1 ++ [ng]).length := by
      cases ngOpt <;> simp
    have hev_old : ∀ u : WireVal, u.wf (nNew + st.1.length) →
        u.eval ((match ngOpt with | none => st.1 | some ng => st.1 ++ [ng]).foldl dmStep inpNew) =
        u.eval (st.1.foldl dmStep inpNew) := by
      intro u hu
      cases ngOpt with
      | none => rfl
      | some ng =>
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact WireVal.eval_append _ _ u (by rw [hlen_w]; exact hu)
    refine ⟨by simp [gateStep, hlen], ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact WireVal.wf_mono (by omega) (hwf u hu)
      · simp at hu; subst hu; exact hvwf
    · intro i
      unfold gateStep
      by_cases hi : i < st.2.length
      · rw [List.getD_append st.2 [v] (.const false) i hi,
            List.getD_append wOld _ false i (by omega)]
        rw [hev_old _ (hwf_get i)]
        exact hmatch i
      · by_cases hi_eq : i = st.2.length
        · subst hi_eq
          rw [List.getD_append_right st.2 [v] (.const false) _ (le_refl _),
              List.getD_append_right wOld _ false _ (by omega)]
          simp only [Nat.sub_self, List.getD_cons_zero, hlen]
          exact hvev
        · rw [List.getD_eq_default (st.2 ++ [v]) _ (by simp; omega),
              List.getD_eq_default (wOld ++ _) _ (by simp; omega)]
          rfl
  rcases hfan with ⟨hop, hlen_g⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · unfold fanStep; rw [hop]; dsimp only
    rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · exact hstep_pack none (.const true) ⟨trivial, by rw [hop, hi]; rfl⟩
    · exact hstep_pack none (st.2.getD a (.const false))
        ⟨hwf_get a, by rw [hop, hi]; simp only [GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]; exact hmatch a⟩
    · dsimp only
      have hc := combine_spec false (st.1.foldl dmStep inpNew)
        (st.2.getD a (.const false)) (st.2.getD b (.const false))
        (by rw [hlen_w]; exact hwf_get a) (by rw [hlen_w]; exact hwf_get b)
      rw [hlen_w] at hc
      rcases hres : combine false (nNew + st.1.length)
        (st.2.getD a (.const false)) (st.2.getD b (.const false)) with ⟨ngOpt, v⟩
      rw [hres] at hc
      dsimp only at hc ⊢
      cases ngOpt with
      | none =>
        exact hstep_pack none v ⟨by rw [← hlen_w]; exact hc.1,
          by rw [hop, hi]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, ← hmatch a, ← hmatch b]; exact hc.2⟩
      | some ng =>
        refine hstep_pack (some ng) v ⟨?_, ?_⟩
        · have h1 := hc.1
          simp only [dmStep, List.length_append, List.length_singleton, hlen_w] at h1
          simpa [List.length_append, Nat.add_assoc] using h1
        · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hop, hi]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, ← hmatch a, ← hmatch b]
          exact hc.2
    · simp [hi] at hlen_g
  · unfold fanStep; rw [hop]; dsimp only
    rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · exact hstep_pack none (.const false) ⟨trivial, by rw [hop, hi]; rfl⟩
    · exact hstep_pack none (st.2.getD a (.const false))
        ⟨hwf_get a, by rw [hop, hi]; simp only [GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]; exact hmatch a⟩
    · dsimp only
      have hc := combine_spec true (st.1.foldl dmStep inpNew)
        (st.2.getD a (.const false)) (st.2.getD b (.const false))
        (by rw [hlen_w]; exact hwf_get a) (by rw [hlen_w]; exact hwf_get b)
      rw [hlen_w] at hc
      rcases hres : combine true (nNew + st.1.length)
        (st.2.getD a (.const false)) (st.2.getD b (.const false)) with ⟨ngOpt, v⟩
      rw [hres] at hc
      dsimp only at hc ⊢
      cases ngOpt with
      | none =>
        exact hstep_pack none v ⟨by rw [← hlen_w]; exact hc.1,
          by rw [hop, hi]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, ← hmatch a, ← hmatch b]; exact hc.2⟩
      | some ng =>
        refine hstep_pack (some ng) v ⟨?_, ?_⟩
        · have h1 := hc.1
          simp only [dmStep, List.length_append, List.length_singleton, hlen_w] at h1
          simpa [List.length_append, Nat.add_assoc] using h1
        · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hop, hi]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, ← hmatch a, ← hmatch b]
          exact hc.2
    · simp [hi] at hlen_g
  · unfold fanStep; rw [hop]; dsimp only
    rcases hi : g.inputs with _ | ⟨a, tl⟩
    · exact hstep_pack none (WireVal.const false).neg ⟨trivial, by rw [hop, hi]; rfl⟩
    · exact hstep_pack none (st.2.getD a (.const false)).neg
        ⟨WireVal.wf_neg (hwf_get a), by
          rw [WireVal.eval_neg, hmatch a, hop, hi]; rfl⟩

lemma foldl_fanStep_props (nNew : ℕ) (gs : List Gate) (st : List DMGate × List WireVal)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gs.foldl (fanStep nNew) st).2.length = st.2.length + gs.length ∧
    (gs.foldl (fanStep nNew) st).1.length ≤ st.1.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    have h1 := ih (fanStep nNew st g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have hlen := fanStep_len_env nNew st g
    have hacc := fanStep_acc_le nNew st g
    simp only [List.foldl_cons, List.length_cons]
    omega

lemma foldl_fanStep_countP (nNew : ℕ) (gs : List Gate) (st : List DMGate × List WireVal)
    (wIdx : ℕ) (c : Bool) (hwIdx : wIdx < st.2.length)
    (hc : st.2.getD wIdx (.const false) = .const c)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gs.foldl (fanStep nNew) st).1.length +
      gs.countP (fun g => (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains wIdx)
      ≤ st.1.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    have hg := hfan g (List.mem_cons_self ..)
    obtain ⟨v, hv⟩ := fanStep_env_prefix nNew st g
    have hwIdx' : wIdx < (fanStep nNew st g).2.length := by rw [hv]; simp; omega
    have hc' : (fanStep nNew st g).2.getD wIdx (.const false) = .const c := by
      rw [hv, List.getD_append st.2 [v] (.const false) wIdx hwIdx]; exact hc
    have hih := ih (fanStep nNew st g) hwIdx' hc' (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    simp only [List.foldl_cons, List.countP_cons, List.length_cons]
    by_cases hhit : (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains wIdx = true
    · have heq := fanStep_acc_eq_of_hit nNew st g wIdx c hc hg hhit
      simp only [hhit, ↓reduceIte]
      omega
    · have hle := fanStep_acc_le nNew st g
      have hhit' : ((if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains wIdx) = false :=
        Bool.eq_false_iff.mpr hhit
      simp only [hhit', Bool.false_eq_true, ↓reduceIte]
      omega

lemma foldl_fanStep_correct (nNew : ℕ) (gs : List Gate) (st : List DMGate × List WireVal)
    (inpNew : List Bool) (wOld : List Bool)
    (hinp : inpNew.length = nNew)
    (hlen : st.2.length = wOld.length)
    (hwf : ∀ v ∈ st.2, v.wf (nNew + st.1.length))
    (hmatch : ∀ i : ℕ, (st.2.getD i (.const false)).eval (st.1.foldl dmStep inpNew) = wOld.getD i false)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    let st' := gs.foldl (fanStep nNew) st
    st'.2.length = (gs.foldl gateStep wOld).length ∧
    (∀ v ∈ st'.2, v.wf (nNew + st'.1.length)) ∧
    (∀ i : ℕ, (st'.2.getD i (.const false)).eval (st'.1.foldl dmStep inpNew) =
      (gs.foldl gateStep wOld).getD i false) := by
  induction gs generalizing st wOld with
  | nil => exact ⟨hlen, hwf, hmatch⟩
  | cons g gs ih =>
    have h1 := fanStep_correct nNew st g inpNew wOld hinp hlen hwf hmatch
      (hfan g (List.mem_cons_self ..))
    exact ih (fanStep nNew st g) (gateStep wOld g) h1.1 h1.2.1 h1.2.2
      (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))

def idEnv (n : ℕ) : List WireVal :=
  List.ofFn fun i : Fin n => WireVal.wire i.val false

lemma idEnv_length (n : ℕ) : (idEnv n).length = n := by
  simp [idEnv]

lemma idEnv_wf (n : ℕ) : ∀ v ∈ idEnv n, v.wf n := by
  intro v hv
  simp only [idEnv, List.mem_ofFn] at hv
  obtain ⟨i, rfl⟩ := hv
  exact i.isLt

lemma idEnv_eval (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    ((idEnv n).getD i (.const false)).eval (List.ofFn x) = (List.ofFn x).getD i false := by
  by_cases hi : i < n
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp [idEnv, List.getElem?_ofFn, hi, WireVal.eval]
  · rw [List.getD_eq_default _ _ (by simp [idEnv]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    rfl

lemma compile_x2_x3 (x2 x3 : Circuit) (x4 : Bool)
    (hf2 : FanInTwo x2) (hf3 : FanInTwo x3) :
    ∃ D : DMCircuit,
      D.size + x3.gates.countP (fun g =>
        (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains (8 + x2.size))
        ≤ x2.size + x3.size ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = x3.eval (x2.wires (List.ofFn x) ++ [x4]) := by
  let st2 := x2.gates.foldl (fanStep 8) ([], idEnv 8)
  have hst2_props := foldl_fanStep_props 8 x2.gates ([], idEnv 8) hf2
  have hst2_len : st2.2.length = 8 + x2.size := by
    have := hst2_props.1; simp [idEnv, Circuit.size] at this ⊢; exact this
  have hst2_acc : st2.1.length ≤ x2.size := by
    have := hst2_props.2; simp [Circuit.size] at this ⊢; exact this
  let st2c : List DMGate × List WireVal := (st2.1, st2.2 ++ [.const x4])
  have hwIdx : 8 + x2.size < st2c.2.length := by simp [st2c, hst2_len]
  have hc : st2c.2.getD (8 + x2.size) (.const false) = .const x4 := by
    simp only [st2c]
    rw [List.getD_append_right st2.2 [.const x4] (.const false) (8 + x2.size) (by omega)]
    simp [hst2_len]
  let st3 := x3.gates.foldl (fanStep 8) st2c
  have hcnt := foldl_fanStep_countP 8 x3.gates st2c (8 + x2.size) x4 hwIdx hc hf3
  refine ⟨⟨st3.1, st3.2.getD x3.output (.const false)⟩, ?_, ?_⟩
  · simp only [DMCircuit.size, Circuit.size, st3, st2c] at hcnt hst2_acc ⊢
    omega
  · intro x
    have h2 := foldl_fanStep_correct 8 x2.gates ([], idEnv 8) (List.ofFn x) (List.ofFn x)
      (by simp) (by simp [idEnv]) (by simpa using idEnv_wf 8)
      (fun i => by simpa using idEnv_eval 8 x i) hf2
    have h2_match : ∀ i : ℕ,
        (st2c.2.getD i (.const false)).eval (st2c.1.foldl dmStep (List.ofFn x)) =
        (x2.wires (List.ofFn x) ++ [x4]).getD i false := by
      intro i
      have h2len : st2.2.length = (x2.gates.foldl gateStep (List.ofFn x)).length := h2.1
      change ((st2.2 ++ [WireVal.const x4]).getD i (WireVal.const false)).eval (st2.1.foldl dmStep (List.ofFn x)) =
        (x2.gates.foldl gateStep (List.ofFn x) ++ [x4]).getD i false
      by_cases hi : i < st2.2.length
      · rw [List.getD_append st2.2 _ _ i hi, List.getD_append _ _ _ i (by omega)]
        exact h2.2.2 i
      · by_cases hi_eq : i = st2.2.length
        · subst hi_eq
          rw [List.getD_append_right st2.2 _ _ _ (le_refl _),
              List.getD_append_right _ _ _ _ (by omega)]
          simp [h2len, WireVal.eval]
        · rw [List.getD_eq_default (st2.2 ++ _) _ (by simp; omega),
              List.getD_eq_default (_ ++ _) _ (by simp only [List.length_append, List.length_singleton, ← h2len]; omega)]
          rfl
    have h2_wf : ∀ v ∈ st2c.2, v.wf (8 + st2c.1.length) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2.2.1 v hv
      · simp at hv; subst hv; trivial
    have h3 := foldl_fanStep_correct 8 x3.gates st2c (List.ofFn x)
      (x2.wires (List.ofFn x) ++ [x4])
      (by simp) (by simp only [st2c, List.length_append, List.length_singleton]; exact congrArg (· + 1) h2.1) h2_wf h2_match hf3
    exact h3.2.2 x3.output

-- Part 2: General DMCircuit simplification and restriction

def simpStep (nNew : ℕ) (st : List DMGate × List WireVal) (g : DMGate) :
    List DMGate × List WireVal :=
  let acc := st.1
  let env := st.2
  let va := (env.getD g.l (.const false)).xorPol g.pl
  let vb := (env.getD g.r (.const false)).xorPol g.pr
  let res := combine g.isOr (nNew + acc.length) va vb
  match res.1 with
  | none => (acc, env ++ [res.2])
  | some ng => (acc ++ [ng], env ++ [res.2])

def simpEmits (env : List WireVal) (g : DMGate) : Bool :=
  let va := (env.getD g.l (.const false)).xorPol g.pl
  let vb := (env.getD g.r (.const false)).xorPol g.pr
  (combine g.isOr 0 va vb).1.isSome

lemma combine_isSome_indep (isOr : Bool) (n1 n2 : ℕ) (a b : WireVal) :
    (combine isOr n1 a b).1.isSome = (combine isOr n2 a b).1.isSome := by
  cases a <;> cases b <;> simp [combine]
  split <;> simp

lemma simpStep_env_prefix (nNew : ℕ) (st : List DMGate × List WireVal) (g : DMGate) :
    ∃ v : WireVal, (simpStep nNew st g).2 = st.2 ++ [v] := by
  unfold simpStep; dsimp only
  cases (combine _ _ _ _).1 <;> exact ⟨_, rfl⟩

lemma simpStep_env_length (nNew : ℕ) (st : List DMGate × List WireVal) (g : DMGate) :
    (simpStep nNew st g).2.length = st.2.length + 1 := by
  obtain ⟨v, hv⟩ := simpStep_env_prefix nNew st g
  rw [hv]; simp

lemma simpStep_acc_length (nNew : ℕ) (st : List DMGate × List WireVal) (g : DMGate) :
    (simpStep nNew st g).1.length = st.1.length + (if simpEmits st.2 g then 1 else 0) := by
  unfold simpStep simpEmits
  dsimp only
  have hind := combine_isSome_indep g.isOr (nNew + st.1.length) 0
    ((st.2.getD g.l (.const false)).xorPol g.pl)
    ((st.2.getD g.r (.const false)).xorPol g.pr)
  rw [← hind]
  cases (combine g.isOr (nNew + st.1.length)
    ((st.2.getD g.l (.const false)).xorPol g.pl)
    ((st.2.getD g.r (.const false)).xorPol g.pr)).1 <;> simp

lemma simpStep_correct (nNew : ℕ) (st : List DMGate × List WireVal) (g : DMGate)
    (inpNew : List Bool) (wOld : List Bool)
    (hinp : inpNew.length = nNew)
    (hlen : st.2.length = wOld.length)
    (hwf : ∀ v ∈ st.2, v.wf (nNew + st.1.length))
    (hmatch : ∀ i : ℕ, (st.2.getD i (.const false)).eval (st.1.foldl dmStep inpNew) = wOld.getD i false) :
    let st' := simpStep nNew st g
    st'.2.length = (dmStep wOld g).length ∧
    (∀ v ∈ st'.2, v.wf (nNew + st'.1.length)) ∧
    (∀ i : ℕ, (st'.2.getD i (.const false)).eval (st'.1.foldl dmStep inpNew) = (dmStep wOld g).getD i false) := by
  have hwf_get : ∀ i : ℕ, (st.2.getD i (.const false)).wf (nNew + st.1.length) := by
    intro i
    by_cases hi : i < st.2.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hwf _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; trivial
  have hlen_w : (st.1.foldl dmStep inpNew).length = nNew + st.1.length := by
    rw [foldl_dmStep_length, hinp]
  let va := (st.2.getD g.l (.const false)).xorPol g.pl
  let vb := (st.2.getD g.r (.const false)).xorPol g.pr
  have hva_wf : va.wf (st.1.foldl dmStep inpNew).length := by
    rw [hlen_w]; exact WireVal.wf_xorPol _ (hwf_get g.l)
  have hvb_wf : vb.wf (st.1.foldl dmStep inpNew).length := by
    rw [hlen_w]; exact WireVal.wf_xorPol _ (hwf_get g.r)
  have hc := combine_spec g.isOr (st.1.foldl dmStep inpNew) va vb hva_wf hvb_wf
  rw [hlen_w] at hc
  have hval : (if g.isOr then va.eval (st.1.foldl dmStep inpNew) || vb.eval (st.1.foldl dmStep inpNew)
      else va.eval (st.1.foldl dmStep inpNew) && vb.eval (st.1.foldl dmStep inpNew)) = g.eval wOld := by
    simp only [va, vb, WireVal.eval_xorPol, hmatch, DMGate.eval]
  unfold simpStep
  dsimp only
  rcases hres : combine g.isOr (nNew + st.1.length) va vb with ⟨ngOpt, v⟩
  rw [hres] at hc
  dsimp only at hc ⊢
  cases ngOpt with
  | none =>
    refine ⟨by simp [dmStep, hlen], ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hwf u hu
      · simp at hu; subst hu; rw [← hlen_w]; exact hc.1
    · intro i
      unfold dmStep
      by_cases hi : i < st.2.length
      · rw [List.getD_append st.2 [v] (.const false) i hi,
            List.getD_append wOld _ false i (by omega)]
        exact hmatch i
      · by_cases hi_eq : i = st.2.length
        · subst hi_eq
          rw [List.getD_append_right st.2 [v] (.const false) _ (le_refl _),
              List.getD_append_right wOld _ false _ (by omega)]
          simp only [Nat.sub_self, List.getD_cons_zero, hlen]
          exact hc.2.trans hval
        · rw [List.getD_eq_default (st.2 ++ [v]) _ (by simp; omega),
              List.getD_eq_default (wOld ++ _) _ (by simp; omega)]
          rfl
  | some ng =>
    refine ⟨by simp [dmStep, hlen], ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact WireVal.wf_mono (by simp) (hwf u hu)
      · simp at hu; subst hu
        have h1 := hc.1
        simp only [dmStep, List.length_append, List.length_singleton, hlen_w] at h1
        simpa [List.length_append, Nat.add_assoc] using h1
    · intro i
      by_cases hi : i < st.2.length
      · rw [List.getD_append st.2 [v] (.const false) i hi]
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        change (st.2.getD i (.const false)).eval (st.1.foldl dmStep inpNew ++ [ng.eval _]) = _
        rw [WireVal.eval_append _ _ _ (by rw [hlen_w]; exact hwf_get i)]
        unfold dmStep
        rw [List.getD_append wOld _ false i (by omega)]
        exact hmatch i
      · by_cases hi_eq : i = st.2.length
        · subst hi_eq
          rw [List.getD_append_right st.2 [v] (.const false) _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          unfold dmStep
          rw [List.getD_append_right wOld _ false _ (by omega)]
          simp only [hlen, Nat.sub_self, List.getD_cons_zero]
          exact hc.2.trans hval
        · unfold dmStep
          rw [List.getD_eq_default (st.2 ++ [v]) _ (by simp; omega),
              List.getD_eq_default (wOld ++ _) _ (by simp; omega)]
          rfl

lemma foldl_simpStep_correct (nNew : ℕ) (gs : List DMGate) (st : List DMGate × List WireVal)
    (inpNew : List Bool) (wOld : List Bool)
    (hinp : inpNew.length = nNew)
    (hlen : st.2.length = wOld.length)
    (hwf : ∀ v ∈ st.2, v.wf (nNew + st.1.length))
    (hmatch : ∀ i : ℕ, (st.2.getD i (.const false)).eval (st.1.foldl dmStep inpNew) = wOld.getD i false) :
    let st' := gs.foldl (simpStep nNew) st
    st'.2.length = (gs.foldl dmStep wOld).length ∧
    (∀ v ∈ st'.2, v.wf (nNew + st'.1.length)) ∧
    (∀ i : ℕ, (st'.2.getD i (.const false)).eval (st'.1.foldl dmStep inpNew) =
      (gs.foldl dmStep wOld).getD i false) := by
  induction gs generalizing st wOld with
  | nil => exact ⟨hlen, hwf, hmatch⟩
  | cons g gs ih =>
    have h1 := simpStep_correct nNew st g inpNew wOld hinp hlen hwf hmatch
    exact ih (simpStep nNew st g) (dmStep wOld g) h1.1 h1.2.1 h1.2.2

def simpTrace (nNew : ℕ) (env0 : List WireVal) (gs : List DMGate) (k : ℕ) :
    List DMGate × List WireVal :=
  (gs.take k).foldl (simpStep nNew) ([], env0)

lemma simpTrace_succ (nNew : ℕ) (env0 : List WireVal) (gs : List DMGate) (k : ℕ)
    (hk : k < gs.length) :
    simpTrace nNew env0 gs (k + 1) = simpStep nNew (simpTrace nNew env0 gs k) gs[k] := by
  unfold simpTrace
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma simpTrace_env_length (nNew : ℕ) (env0 : List WireVal) (gs : List DMGate) (k : ℕ)
    (hk : k ≤ gs.length) :
    (simpTrace nNew env0 gs k).2.length = env0.length + k := by
  induction k with
  | zero => simp [simpTrace]
  | succ k ih =>
    rw [simpTrace_succ nNew env0 gs k (by omega), simpStep_env_length, ih (by omega)]
    omega

lemma simpTrace_env_mono (nNew : ℕ) (env0 : List WireVal) (gs : List DMGate)
    {k1 k2 : ℕ} (hk : k1 ≤ k2) (hk2 : k2 ≤ gs.length)
    (i : ℕ) (hi : i < (simpTrace nNew env0 gs k1).2.length) :
    (simpTrace nNew env0 gs k2).2.getD i (.const false) =
    (simpTrace nNew env0 gs k1).2.getD i (.const false) := by
  induction k2 with
  | zero =>
    have : k1 = 0 := by omega
    subst this; rfl
  | succ k2 ih =>
    by_cases hlt : k1 ≤ k2
    · rw [simpTrace_succ nNew env0 gs k2 (by omega)]
      obtain ⟨v, hv⟩ := simpStep_env_prefix nNew (simpTrace nNew env0 gs k2) gs[k2]
      rw [hv]
      have hlen1 := simpTrace_env_length nNew env0 gs k1 (by omega)
      have hlen2 := simpTrace_env_length nNew env0 gs k2 (by omega)
      rw [List.getD_append _ _ _ i (by omega)]
      exact ih hlt (by omega)
    · have : k1 = k2 + 1 := by omega
      subst this; rfl

lemma simpTrace_acc_sum (nNew : ℕ) (env0 : List WireVal) (gs : List DMGate) (k : ℕ)
    (hk : k ≤ gs.length) :
    (simpTrace nNew env0 gs k).1.length =
    ∑ i ∈ Finset.range k,
      if h : i < gs.length then (if simpEmits (simpTrace nNew env0 gs i).2 gs[i] then 1 else 0) else 0 := by
  induction k with
  | zero => simp [simpTrace]
  | succ k ih =>
    rw [simpTrace_succ nNew env0 gs k (by omega), simpStep_acc_length, ih (by omega),
        Finset.sum_range_succ]
    have hlt : k < gs.length := by omega
    simp [hlt]

def simplifyDM (nNew : ℕ) (env0 : List WireVal) (C : DMCircuit) : DMCircuit :=
  let st := C.gates.foldl (simpStep nNew) ([], env0)
  let out' := match C.out with
    | .const b => .const b
    | .wire i p => (st.2.getD i (.const false)).xorPol p
  ⟨st.1, out'⟩

lemma simplifyDM_eval (nNew : ℕ) (env0 : List WireVal) (C : DMCircuit)
    (inpNew : List Bool) (hinp : inpNew.length = nNew)
    (hwf : ∀ v ∈ env0, v.wf nNew) :
    (simplifyDM nNew env0 C).eval inpNew = C.eval (env0.map fun v => v.eval inpNew) := by
  have hmatch0 : ∀ i : ℕ, (env0.getD i (.const false)).eval inpNew =
      (env0.map fun v => v.eval inpNew).getD i false := by
    intro i
    by_cases hi : i < env0.length
    · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simp; exact hi)]
      simp
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
      rfl
  have hfold := foldl_simpStep_correct nNew C.gates ([], env0) inpNew
    (env0.map fun v => v.eval inpNew) hinp (by simp) (by simpa using hwf)
    (by simpa using hmatch0)
  unfold simplifyDM DMCircuit.eval DMCircuit.wires
  dsimp only
  cases hout : C.out with
  | const b => rfl
  | wire i p =>
    rw [WireVal.eval_xorPol, hfold.2.2 i]
    rfl

lemma simplifyDM_size (nNew : ℕ) (env0 : List WireVal) (C : DMCircuit) :
    (simplifyDM nNew env0 C).size =
    ∑ i ∈ Finset.range C.size,
      if h : i < C.size then (if simpEmits (simpTrace nNew env0 C.gates i).2 C.gates[i] then 1 else 0) else 0 := by
  have h := simpTrace_acc_sum nNew env0 C.gates C.gates.length (le_refl _)
  unfold simplifyDM DMCircuit.size
  simpa [simpTrace] using h

lemma sum_le_card_sub_of_zeros {n : ℕ} (f : ℕ → ℕ) (S : Finset ℕ)
    (hf : ∀ i ∈ Finset.range n, f i ≤ 1)
    (hS : S ⊆ Finset.range n)
    (hzero : ∀ i ∈ S, f i = 0) :
    (∑ i ∈ Finset.range n, f i) + S.card ≤ n := by
  have hsplit := (Finset.sum_sdiff hS (f := f)).symm
  have hSz : ∑ i ∈ S, f i = 0 := Finset.sum_eq_zero hzero
  have hrest : ∑ i ∈ Finset.range n \ S, f i ≤ (Finset.range n \ S).card := by
    calc ∑ i ∈ Finset.range n \ S, f i
        ≤ ∑ _i ∈ Finset.range n \ S, 1 := Finset.sum_le_sum fun i hi =>
            hf i (Finset.mem_sdiff.mp hi).1
      _ = (Finset.range n \ S).card := by simp
  have hcard : (Finset.range n \ S).card + S.card = n := by
    have := Finset.card_sdiff_add_card_eq_card hS
    simpa using this
  omega

-- Helper: dead gate removal and gate replacement

def shiftIdx (k i : ℕ) : ℕ := if i < k then i else i - 1

def shiftWV (k : ℕ) : WireVal → WireVal
  | .const b => .const b
  | .wire i p => .wire (shiftIdx k i) p

def shiftGate (k : ℕ) (g : DMGate) : DMGate :=
  ⟨g.isOr, shiftIdx k g.l, g.pl, shiftIdx k g.r, g.pr⟩

def removeGate (n j : ℕ) (C : DMCircuit) : DMCircuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (shiftGate (n + j)), shiftWV (n + j) C.out⟩

lemma removeGate_size (n j : ℕ) (C : DMCircuit) (hj : j < C.size) :
    (removeGate n j C).size + 1 = C.size := by
  simp only [removeGate, DMCircuit.size, List.length_append, List.length_take,
    List.length_map, List.length_drop] at hj ⊢
  omega

lemma removeGate_eval (n j : ℕ) (C : DMCircuit) (inp : List Bool)
    (hinp : inp.length = n) (hj : j < C.size)
    (hdead : ∀ g ∈ C.gates.drop (j + 1), g.l ≠ n + j ∧ g.r ≠ n + j)
    (hout : ∀ p, C.out ≠ .wire (n + j) p) :
    (removeGate n j C).eval inp = C.eval inp := by
  have hj' : j < C.gates.length := hj
  let wPre := (C.gates.take j).foldl dmStep inp
  have hwPre_len : wPre.length = n + j := by
    rw [foldl_dmStep_length, hinp, List.length_take, Nat.min_eq_left (by omega)]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      rw [List.drop_eq_getElem_cons hj])
  let wOld0 := dmStep wPre C.gates[j]
  have hrel0 : ∀ i : ℕ, i ≠ n + j → wPre.getD (shiftIdx (n + j) i) false = wOld0.getD i false := by
    intro i hi
    unfold shiftIdx wOld0 dmStep
    by_cases hlt : i < n + j
    · simp only [hlt, ↓reduceIte]
      rw [List.getD_append wPre _ false i (by omega)]
    · simp only [hlt, ↓reduceIte]
      rw [List.getD_eq_default wPre _ (by omega), List.getD_eq_default (wPre ++ _) _ (by simp [hwPre_len]; omega)]
  have hfold : ∀ (gs : List DMGate) (w1 w2 : List Bool),
      w1.length + 1 = w2.length → n + j ≤ w1.length →
      (∀ g ∈ gs, g.l ≠ n + j ∧ g.r ≠ n + j) →
      (∀ i : ℕ, i ≠ n + j → w1.getD (shiftIdx (n + j) i) false = w2.getD i false) →
      ∀ i : ℕ, i ≠ n + j →
        ((gs.map (shiftGate (n + j))).foldl dmStep w1).getD (shiftIdx (n + j) i) false =
        (gs.foldl dmStep w2).getD i false := by
    intro gs
    induction gs with
    | nil => intro w1 w2 _ _ _ hr i hi; exact hr i hi
    | cons g gs ih =>
      intro w1 w2 hlen hnj hgs hr
      have hg := hgs g (List.mem_cons_self ..)
      have hgev : (shiftGate (n + j) g).eval w1 = g.eval w2 := by
        simp only [shiftGate, DMGate.eval, hr g.l hg.1, hr g.r hg.2]
      refine ih (dmStep w1 (shiftGate (n + j) g)) (dmStep w2 g)
        (by simp [dmStep]; omega) (by simp [dmStep]; omega)
        (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) ?_
      intro i hi
      unfold dmStep
      by_cases hlt : i < w2.length
      · have hlt' : shiftIdx (n + j) i < w1.length := by
          unfold shiftIdx; split <;> omega
        rw [List.getD_append w1 _ false _ hlt', List.getD_append w2 _ false i hlt]
        exact hr i hi
      · by_cases heq : i = w2.length
        · subst heq
          have hsh : shiftIdx (n + j) w2.length = w1.length := by
            unfold shiftIdx; split <;> omega
          rw [hsh, List.getD_append_right w1 _ false _ (le_refl _),
              List.getD_append_right w2 _ false _ (le_refl _)]
          simp [hgev]
        · have hge : w1.length + 1 ≤ shiftIdx (n + j) i := by
            unfold shiftIdx; split <;> omega
          rw [List.getD_eq_default (w1 ++ _) _ (by simp; omega),
              List.getD_eq_default (w2 ++ _) _ (by simp; omega)]
  have hfin := hfold (C.gates.drop (j + 1)) wPre wOld0 (by simp [wOld0, dmStep])
    (by omega) hdead hrel0
  unfold removeGate DMCircuit.eval DMCircuit.wires
  rw [List.foldl_append]
  conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  cases ho : C.out with
  | const b => rfl
  | wire idx p =>
    have hne : idx ≠ n + j := fun h => hout p (by rw [ho, h])
    simp only [shiftWV, WireVal.eval]
    rw [hfin idx hne]

-- Replace gate j (with j < C.size) by an earlier wire (wire k pol, k < n + j)

def replaceGate (n j k : ℕ) (pol : Bool) (C : DMCircuit) : DMCircuit :=
  let env0 := idEnv (n + j) ++ [.wire k pol]
  let st := (C.gates.drop (j + 1)).foldl (simpStep (n + j)) ([], env0)
  let out' := match C.out with
    | .const b => .const b
    | .wire i p => (st.2.getD i (.const false)).xorPol p
  ⟨C.gates.take j ++ st.1, out'⟩

lemma replaceGate_size (n j k : ℕ) (pol : Bool) (C : DMCircuit) (hj : j < C.size) :
    (replaceGate n j k pol C).size + 1 ≤ C.size := by
  have hsum := simpTrace_acc_sum (n + j) (idEnv (n + j) ++ [.wire k pol])
    (C.gates.drop (j + 1)) (C.gates.drop (j + 1)).length (le_refl _)
  have hle : ((C.gates.drop (j + 1)).foldl (simpStep (n + j)) ([], idEnv (n + j) ++ [.wire k pol])).1.length
      ≤ (C.gates.drop (j + 1)).length := by
    have h0 : ((C.gates.drop (j + 1)).foldl (simpStep (n + j)) ([], idEnv (n + j) ++ [.wire k pol])).1.length =
        (simpTrace (n + j) (idEnv (n + j) ++ [.wire k pol]) (C.gates.drop (j + 1))
          (C.gates.drop (j + 1)).length).1.length := by
      unfold simpTrace; rw [List.take_length]
    rw [h0, hsum]
    calc ∑ i ∈ Finset.range (C.gates.drop (j + 1)).length, _
        ≤ ∑ _i ∈ Finset.range (C.gates.drop (j + 1)).length, 1 := Finset.sum_le_sum fun i _ => by
          split <;> [split <;> omega; omega]
      _ = (C.gates.drop (j + 1)).length := by simp
  simp only [replaceGate, DMCircuit.size, List.length_append, List.length_take]
  simp only [List.length_drop, DMCircuit.size] at hle hj ⊢
  omega

lemma replaceGate_eval (n j k : ℕ) (pol : Bool) (C : DMCircuit) (inp : List Bool)
    (hinp : inp.length = n) (hj : j < C.size) (hk : k < n + j)
    (heq : let wPre := (C.gates.take j).foldl dmStep inp
           (wPre.getD k false != pol) = C.gates[j].eval wPre) :
    (replaceGate n j k pol C).eval inp = C.eval inp := by
  have hj' : j < C.gates.length := hj
  let wPre := (C.gates.take j).foldl dmStep inp
  have hwPre_len : wPre.length = n + j := by
    rw [foldl_dmStep_length, hinp, List.length_take, Nat.min_eq_left (by omega)]
  let env0 := idEnv (n + j) ++ [.wire k pol]
  have hwf0 : ∀ v ∈ env0, v.wf (n + j) := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact idEnv_wf (n + j) v hv
    · simp at hv; subst hv; exact hk
  have hmatch0 : ∀ i : ℕ, (env0.getD i (.const false)).eval wPre = (dmStep wPre C.gates[j]).getD i false := by
    intro i
    unfold dmStep
    by_cases hi : i < n + j
    · rw [List.getD_append (idEnv (n + j)) _ _ i (by simp [idEnv]; exact hi),
          List.getD_append wPre _ _ i (by omega)]
      rw [List.getD_eq_getElem?_getD]
      simp [idEnv, List.getElem?_ofFn, hi, WireVal.eval]
    · by_cases hi_eq : i = n + j
      · subst hi_eq
        rw [List.getD_append_right (idEnv (n + j)) _ _ _ (by simp [idEnv]),
            List.getD_append_right wPre _ _ _ (by omega)]
        simp only [idEnv_length, hwPre_len, Nat.sub_self, List.getD_cons_zero, WireVal.eval]
        exact heq
      · rw [List.getD_eq_default (idEnv (n + j) ++ _) _ (by simp [idEnv]; omega),
            List.getD_eq_default (wPre ++ _) _ (by simp [hwPre_len]; omega)]
        rfl
  have hfold := foldl_simpStep_correct (n + j) (C.gates.drop (j + 1)) ([], env0) wPre
    (dmStep wPre C.gates[j]) hwPre_len (by simp [env0, idEnv, dmStep, hwPre_len])
    (by simpa using hwf0) (by simpa using hmatch0)
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      rw [List.drop_eq_getElem_cons hj'])
  unfold replaceGate DMCircuit.eval DMCircuit.wires
  dsimp only
  rw [List.foldl_append]
  conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  cases ho : C.out with
  | const b => rfl
  | wire idx p =>
    rw [WireVal.eval_xorPol, hfold.2.2 idx]
    rfl

-- Part 3: Minimal DMCircuit structural properties

def Computes (n : ℕ) (f : (Fin n → Bool) → Bool) (C : DMCircuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

def MinimalDM (n : ℕ) (f : (Fin n → Bool) → Bool) (C : DMCircuit) : Prop :=
  Computes n f C ∧ ∀ C' : DMCircuit, Computes n f C' → C.size ≤ C'.size

def fanout (C : DMCircuit) (w : ℕ) : ℕ :=
  C.gates.countP fun g => g.l == w || g.r == w

def IsEss {n : ℕ} (f : (Fin n → Bool) → Bool) (v : Fin n) : Prop :=
  ∃ x : Fin n → Bool, f x ≠ f (Function.update x v (!x v))

lemma minimal_exists {n : ℕ} (f : (Fin n → Bool) → Bool) (C : DMCircuit) (hC : Computes n f C) :
    ∃ M : DMCircuit, MinimalDM n f M ∧ M.size ≤ C.size := by
  classical
  have hex : ∃ s : ℕ, ∃ M : DMCircuit, M.size = s ∧ Computes n f M := ⟨C.size, C, rfl, hC⟩
  let s := Nat.find hex
  obtain ⟨M, hMs, hMc⟩ := Nat.find_spec hex
  refine ⟨M, ⟨hMc, fun C' hC' => ?_⟩, ?_⟩
  · rw [hMs]; exact Nat.find_min' hex ⟨C', rfl, hC'⟩
  · rw [hMs]; exact Nat.find_min' hex ⟨C, rfl, hC⟩

lemma minimal_out_last {n : ℕ} {f : (Fin n → Bool) → Bool} {C : DMCircuit}
    (hmin : MinimalDM n f C)
    (hess : ∀ v : Fin n, IsEss f v) (hn : 2 ≤ n) :
    1 ≤ C.size ∧ ∃ p : Bool, C.out = .wire (n + C.size - 1) p := by
  cases ho : C.out with
  | const b =>
    obtain ⟨x, hx⟩ := hess ⟨0, by omega⟩
    have h1 := hmin.1 x
    have h2 := hmin.1 (Function.update x ⟨0, by omega⟩ (!x ⟨0, by omega⟩))
    simp [DMCircuit.eval, ho, WireVal.eval] at h1 h2
    exact absurd (h1.symm.trans h2) hx
  | wire idx p =>
    by_cases hlt_n : idx < n
    · let v : Fin n := if idx = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hv_ne : v.val ≠ idx := by
        dsimp only [v]
        split
        · rename_i h0; simp [h0]
        · rename_i hne; intro h; exact hne h.symm
      obtain ⟨x, hx⟩ := hess v
      have h1 := hmin.1 x
      have h2 := hmin.1 (Function.update x v (!x v))
      simp only [DMCircuit.eval, ho, WireVal.eval, DMCircuit.wires] at h1 h2
      rw [foldl_dmStep_getD_lt _ _ idx (by simp; exact hlt_n)] at h1 h2
      have heq : (List.ofFn x).getD idx false =
          (List.ofFn (Function.update x v (!x v))).getD idx false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
            List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hlt_n, ↓reduceDIte, Option.getD_some]
        have hne : (⟨idx, hlt_n⟩ : Fin n) ≠ v := fun h => hv_ne (congrArg Fin.val h.symm)
        simp [Function.update, hne]
      rw [heq] at h1
      exact absurd (h1.symm.trans h2) hx
    · by_cases hge : n + C.size ≤ idx
      · obtain ⟨x, hx⟩ := hess ⟨0, by omega⟩
        have h1 := hmin.1 x
        have h2 := hmin.1 (Function.update x ⟨0, by omega⟩ (!x ⟨0, by omega⟩))
        simp only [DMCircuit.eval, ho, WireVal.eval, DMCircuit.wires] at h1 h2
        rw [List.getD_eq_default _ _ (by rw [foldl_dmStep_length]; simp [DMCircuit.size] at hge ⊢; omega)] at h1 h2
        exact absurd (h1.symm.trans h2) hx
      · have hs : 1 ≤ C.size := by omega
        refine ⟨hs, p, ?_⟩
        by_cases heq : idx = n + C.size - 1
        · rw [heq]
        · have hlt : idx < n + (C.size - 1) := by omega
          let C' : DMCircuit := ⟨C.gates.take (C.size - 1), .wire idx p⟩
          have hC'_comp : Computes n f C' := by
            intro x
            rw [← hmin.1 x]
            simp only [DMCircuit.eval, ho, C', WireVal.eval, DMCircuit.wires]
            have hsp : C.gates = C.gates.take (C.size - 1) ++ C.gates.drop (C.size - 1) :=
              (List.take_append_drop _ _).symm
            conv_rhs =>
              rw [hsp, List.foldl_append, foldl_dmStep_getD_lt _ _ idx (by
                rw [foldl_dmStep_length]
                simp only [List.length_ofFn, List.length_take]
                simp only [DMCircuit.size] at hlt hs ⊢
                omega)]
          have hle := hmin.2 C' hC'_comp
          simp only [C', DMCircuit.size, List.length_take] at hle
          simp only [DMCircuit.size] at hs hle
          omega

lemma combine_isSome_spec {isOr : Bool} {m : ℕ} {a b : WireVal}
    (h : (combine isOr m a b).1.isSome = true) :
    (combine isOr m a b).2 = .wire m false ∧
    ∃ ia pa ib pb, a = .wire ia pa ∧ b = .wire ib pb ∧ ia ≠ ib := by
  cases a with
  | const ba => simp [combine_const_left] at h
  | wire ia pa =>
    cases b with
    | const bb => simp [combine_const_right] at h
    | wire ib pb =>
      by_cases hi : ia = ib
      · subst hi
        by_cases hp : pa = pb
        · simp [combine, hp] at h
        · simp [combine, hp] at h
      · simp [combine, hi]

lemma idEnv_append_one (n : ℕ) : idEnv n ++ [.wire n false] = idEnv (n + 1) := by
  apply List.ext_getElem
  · simp [idEnv]
  · intro i hi1 hi2
    simp only [idEnv, List.length_ofFn] at hi2
    by_cases hlt : i < n
    · rw [List.getElem_append_left (by simp [idEnv]; exact hlt)]
      simp only [idEnv, List.getElem_ofFn]
    · have heq : i = n := by omega
      subst heq
      rw [List.getElem_append_right (by simp [idEnv])]
      simp only [idEnv, List.length_ofFn, Nat.sub_self, List.getElem_cons_zero, List.getElem_ofFn]

lemma minimal_gate_wf {n : ℕ} {f : (Fin n → Bool) → Bool} {C : DMCircuit}
    (hmin : MinimalDM n f C) :
    ∀ j : ℕ, (hj : j < C.size) →
      C.gates[j].l < n + j ∧ C.gates[j].r < n + j ∧ C.gates[j].l ≠ C.gates[j].r := by
  have hcomp : Computes n f (simplifyDM n (idEnv n) C) := by
    intro x
    rw [simplifyDM_eval n (idEnv n) C (List.ofFn x) (by simp) (idEnv_wf n)]
    have hmap : (idEnv n).map (fun v => v.eval (List.ofFn x)) = List.ofFn x := by
      apply List.ext_getElem
      · simp [idEnv]
      · intro i hi1 hi2
        simp only [List.length_ofFn] at hi2
        simp [idEnv, WireVal.eval, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi2]
    rw [hmap]
    exact hmin.1 x
  have hsz_le := hmin.2 (simplifyDM n (idEnv n) C) hcomp
  have hall_emit : ∀ j : ℕ, (hj : j < C.size) →
      simpEmits (simpTrace n (idEnv n) C.gates j).2 C.gates[j] = true := by
    intro j hj
    by_contra hne
    have hfalse : simpEmits (simpTrace n (idEnv n) C.gates j).2 C.gates[j] = false := by
      cases h : simpEmits (simpTrace n (idEnv n) C.gates j).2 C.gates[j] <;> simp_all
    have hsum := sum_le_card_sub_of_zeros
      (n := C.size)
      (f := fun i => if h : i < C.size then
        (if simpEmits (simpTrace n (idEnv n) C.gates i).2 C.gates[i] then 1 else 0) else 0)
      {j}
      (fun i _ => by split <;> [split <;> omega; omega])
      (by intro i hi; simp at hi; subst hi; exact Finset.mem_range.mpr hj)
      (by intro i hi; simp at hi; subst hi; simp [hj, hfalse])
    rw [← simplifyDM_size] at hsum
    simp at hsum
    omega
  have hlenC : C.gates.length = C.size := rfl
  have htrace_id : ∀ k : ℕ, k ≤ C.size →
      (simpTrace n (idEnv n) C.gates k).2 = idEnv (n + k) ∧
      (simpTrace n (idEnv n) C.gates k).1.length = k := by
    intro k hk
    induction k with
    | zero => simp [simpTrace]
    | succ k ih =>
      obtain ⟨henv, hacc⟩ := ih (by omega)
      have hemit := hall_emit k (by omega)
      rw [simpTrace_succ n (idEnv n) C.gates k (by omega)]
      have hacc' : (simpStep n (simpTrace n (idEnv n) C.gates k) C.gates[k]).1.length = k + 1 := by
        rw [simpStep_acc_length, hacc, hemit]; simp
      refine ⟨?_, hacc'⟩
      unfold simpStep
      dsimp only
      rw [henv, hacc]
      unfold simpEmits at hemit
      rw [henv] at hemit
      have hsome : (combine C.gates[k].isOr (n + k)
          (((idEnv (n + k)).getD C.gates[k].l (.const false)).xorPol C.gates[k].pl)
          (((idEnv (n + k)).getD C.gates[k].r (.const false)).xorPol C.gates[k].pr)).1.isSome = true := by
        rw [combine_isSome_indep _ (n + k) 0]; exact hemit
      have hspec := combine_isSome_spec hsome
      rcases hres : combine C.gates[k].isOr (n + k)
          (((idEnv (n + k)).getD C.gates[k].l (.const false)).xorPol C.gates[k].pl)
          (((idEnv (n + k)).getD C.gates[k].r (.const false)).xorPol C.gates[k].pr) with ⟨ngOpt, v⟩
      rw [hres] at hspec
      have hv : v = .wire (n + k) false := hspec.1
      subst hv
      cases ngOpt <;> simp [idEnv_append_one, Nat.add_assoc]
  intro j hj
  have hemit := hall_emit j hj
  obtain ⟨henv, _⟩ := htrace_id j (by omega)
  unfold simpEmits at hemit
  rw [henv] at hemit
  obtain ⟨_, ia, pa, ib, pb, ha, hb, hne⟩ := combine_isSome_spec hemit
  have hl : C.gates[j].l < n + j ∧ ia = C.gates[j].l := by
    by_cases hlt : C.gates[j].l < n + j
    · rw [List.getD_eq_getElem?_getD] at ha
      simp [idEnv, List.getElem?_ofFn, hlt, WireVal.xorPol] at ha
      exact ⟨hlt, ha.1.symm⟩
    · rw [List.getD_eq_default _ _ (by simp [idEnv]; omega)] at ha
      simp [WireVal.xorPol] at ha
  have hr : C.gates[j].r < n + j ∧ ib = C.gates[j].r := by
    by_cases hlt : C.gates[j].r < n + j
    · rw [List.getD_eq_getElem?_getD] at hb
      simp [idEnv, List.getElem?_ofFn, hlt, WireVal.xorPol] at hb
      exact ⟨hlt, hb.1.symm⟩
    · rw [List.getD_eq_default _ _ (by simp [idEnv]; omega)] at hb
      simp [WireVal.xorPol] at hb
  exact ⟨hl.1, hr.1, by omega⟩

lemma minimal_fanout_gate {n : ℕ} {f : (Fin n → Bool) → Bool} {C : DMCircuit}
    (hmin : MinimalDM n f C) (hess : ∀ v : Fin n, IsEss f v) (hn : 2 ≤ n)
    (j : ℕ) (hj : j + 1 < C.size) :
    1 ≤ fanout C (n + j) := by
  by_contra h0
  have hzero : fanout C (n + j) = 0 := by omega
  have hdead_all : ∀ g ∈ C.gates, g.l ≠ n + j ∧ g.r ≠ n + j := by
    intro g hg
    have := List.countP_eq_zero.mp hzero g hg
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at this
    exact this
  obtain ⟨hs, p, hout⟩ := minimal_out_last hmin hess hn
  have hcomp : Computes n f (removeGate n j C) := by
    intro x
    rw [removeGate_eval n j C (List.ofFn x) (by simp) (by omega)
      (fun g hg => hdead_all g (List.mem_of_mem_drop hg))
      (fun q hq => by rw [hout] at hq; injection hq with heq; omega)]
    exact hmin.1 x
  have hle := hmin.2 (removeGate n j C) hcomp
  have hsz := removeGate_size n j C (by omega)
  omega

lemma foldl_dmStep_indep_wire (gs : List DMGate) (v : ℕ)
    (hno : ∀ g ∈ gs, g.l ≠ v ∧ g.r ≠ v) :
    ∀ w1 w2 : List Bool, w1.length = w2.length → v < w1.length →
      (∀ i : ℕ, i ≠ v → w1.getD i false = w2.getD i false) →
      ∀ i : ℕ, i ≠ v → (gs.foldl dmStep w1).getD i false = (gs.foldl dmStep w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ _ h i hi; exact h i hi
  | cons g gs ih =>
    intro w1 w2 hlen hv h
    have hg := hno g (List.mem_cons_self ..)
    have hgev : g.eval w1 = g.eval w2 := by
      simp only [DMGate.eval, h g.l hg.1, h g.r hg.2]
    refine ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
      (dmStep w1 g) (dmStep w2 g) (by simp [dmStep, hlen]) (by simp [dmStep]; omega) ?_
    intro i hi
    unfold dmStep
    by_cases hlt : i < w1.length
    · rw [List.getD_append w1 _ false i hlt, List.getD_append w2 _ false i (by omega)]
      exact h i hi
    · by_cases heq : i = w1.length
      · subst heq
        rw [List.getD_append_right w1 _ false _ (le_refl _),
            List.getD_append_right w2 _ false _ (by omega)]
        simp [hlen, hgev]
      · rw [List.getD_eq_default (w1 ++ _) _ (by simp; omega),
            List.getD_eq_default (w2 ++ _) _ (by simp; omega)]

lemma minimal_fanout_var {n : ℕ} {f : (Fin n → Bool) → Bool} {C : DMCircuit}
    (hmin : MinimalDM n f C) (hess : ∀ v : Fin n, IsEss f v) (hn : 2 ≤ n)
    (v : Fin n) :
    1 ≤ fanout C v.val := by
  by_contra h0
  have hzero : fanout C v.val = 0 := by omega
  have hno : ∀ g ∈ C.gates, g.l ≠ v.val ∧ g.r ≠ v.val := by
    intro g hg
    have := List.countP_eq_zero.mp hzero g hg
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at this
    exact this
  obtain ⟨hs, p, hout⟩ := minimal_out_last hmin hess hn
  obtain ⟨x, hx⟩ := hess v
  have h1 := hmin.1 x
  have h2 := hmin.1 (Function.update x v (!x v))
  have hagree : ∀ i : ℕ, i ≠ v.val →
      (List.ofFn x).getD i false = (List.ofFn (Function.update x v (!x v))).getD i false := by
    intro i hi
    by_cases hlt : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
          List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hlt, ↓reduceDIte, Option.getD_some]
      have hne : (⟨i, hlt⟩ : Fin n) ≠ v := fun h => hi (congrArg Fin.val h)
      simp [Function.update, hne]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hwire := foldl_dmStep_indep_wire C.gates v.val hno
    (List.ofFn x) (List.ofFn (Function.update x v (!x v)))
    (by simp) (by simp) hagree (n + C.size - 1) (by omega)
  simp only [DMCircuit.eval, hout, WireVal.eval, DMCircuit.wires] at h1 h2
  rw [hwire] at h1
  exact absurd (h1.symm.trans h2) hx

lemma fanout_sum_aux (gs : List DMGate) (M : ℕ)
    (hgs : ∀ g ∈ gs, g.l < M ∧ g.r < M ∧ g.l ≠ g.r) :
    ∑ w ∈ Finset.range M, gs.countP (fun g => g.l == w || g.r == w) = 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := hgs g (List.mem_cons_self ..)
    have hih := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    simp only [List.countP_cons, List.length_cons]
    rw [Finset.sum_add_distrib, hih]
    have h1 : ∑ w ∈ Finset.range M, (if (g.l == w || g.r == w) = true then 1 else 0) = 2 := by
      have hfilt : (Finset.range M).filter (fun w => (g.l == w || g.r == w) = true) = {g.l, g.r} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_range, Bool.or_eq_true, beq_iff_eq,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, rfl | rfl⟩ <;> simp
        · rintro (rfl | rfl)
          · exact ⟨hg.1, Or.inl rfl⟩
          · exact ⟨hg.2.1, Or.inr rfl⟩
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one, hfilt,
          Finset.card_pair hg.2.2]
    omega

lemma minimal_fanout_sum {n : ℕ} {f : (Fin n → Bool) → Bool} {C : DMCircuit}
    (hmin : MinimalDM n f C) (hs : 1 ≤ C.size) :
    ∑ w ∈ Finset.range (n + C.size - 1), fanout C w = 2 * C.size := by
  have hwf := minimal_gate_wf hmin
  refine fanout_sum_aux C.gates (n + C.size - 1) ?_
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have h := hwf j hj
  simp only [DMCircuit.size] at hs h ⊢
  exact ⟨by omega, by omega, h.2.2⟩

-- Part 4: P5 >= 5 and C6 >= 8

def P5 (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)

def C6 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)

lemma P5_ess : ∀ v : Fin 5, IsEss P5 v := by unfold IsEss; decide

lemma C6_ess : ∀ v : Fin 6, IsEss C6 v := by unfold IsEss; decide

lemma P5_cofactor_ge3 :
    ∀ (u v : Fin 5) (h00 h01 h10 h11 : Bool), u ≠ v →
      ∃ (a1 a2 b1 b2 : Bool) (x : Fin 5 → Bool),
        (match a1, a2 with
          | false, false => h00 | false, true => h01
          | true, false => h10 | true, true => h11) =
        (match b1, b2 with
          | false, false => h00 | false, true => h01
          | true, false => h10 | true, true => h11) ∧
        P5 (Function.update (Function.update x u a1) v a2) ≠
        P5 (Function.update (Function.update x u b1) v b2) := by
  decide

lemma C6_restrict_ess :
    ∀ (u v : Fin 6) (a : Bool), u ≠ v →
      ∃ x : Fin 6 → Bool, x u = a ∧ C6 x ≠ C6 (Function.update x v (!x v)) := by
  decide

lemma C6_restrict_nonconst :
    ∀ (u : Fin 6) (a : Bool),
      (∃ x : Fin 6 → Bool, x u = a ∧ C6 x = true) ∧
      (∃ y : Fin 6 → Bool, y u = a ∧ C6 y = false) := by
  decide

def rotMap (u : Fin 6) (i : Fin 6) : WireVal :=
  if i = u then .const false else .wire ((i.val + 5 - u.val) % 6) false

lemma rotMap_wf (u : Fin 6) (i : Fin 6) : (rotMap u i).wf 5 := by
  unfold rotMap
  split
  · trivial
  · rename_i hne
    have hval : i.val ≠ u.val := fun h => hne (Fin.ext h)
    have hi := i.isLt
    have hu := u.isLt
    simp only [WireVal.wf]
    omega

lemma C6_rotMap_eq_P5 :
    ∀ (u : Fin 6) (y : Fin 5 → Bool),
      C6 (fun i : Fin 6 => (rotMap u i).eval (List.ofFn y)) = P5 y := by
  decide

lemma foldl_dmStep_agree_from (gs : List DMGate) (u v : ℕ)
    (hno : ∀ g ∈ gs, g.l ≠ u ∧ g.r ≠ u ∧ g.l ≠ v ∧ g.r ≠ v) :
    ∀ w1 w2 : List Bool, w1.length = w2.length → u < w1.length → v < w1.length →
      (∀ i : ℕ, i ≠ u → i ≠ v → w1.getD i false = w2.getD i false) →
      ∀ i : ℕ, i ≠ u → i ≠ v →
        (gs.foldl dmStep w1).getD i false = (gs.foldl dmStep w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ _ _ h i hu hv; exact h i hu hv
  | cons g gs ih =>
    intro w1 w2 hlen hu hv h
    have hg := hno g (List.mem_cons_self ..)
    have hgev : g.eval w1 = g.eval w2 := by
      simp only [DMGate.eval, h g.l hg.1 hg.2.2.1, h g.r hg.2.1 hg.2.2.2]
    refine ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
      (dmStep w1 g) (dmStep w2 g) (by simp [dmStep, hlen]) (by simp [dmStep]; omega)
      (by simp [dmStep]; omega) ?_
    intro i hiu hiv
    unfold dmStep
    by_cases hlt : i < w1.length
    · rw [List.getD_append w1 _ false i hlt, List.getD_append w2 _ false i (by omega)]
      exact h i hiu hiv
    · by_cases heq : i = w1.length
      · subst heq
        rw [List.getD_append_right w1 _ false _ (le_refl _),
            List.getD_append_right w2 _ false _ (by omega)]
        simp [hlen, hgev]
      · rw [List.getD_eq_default (w1 ++ _) _ (by simp; omega),
            List.getD_eq_default (w2 ++ _) _ (by simp; omega)]

lemma P5_ge_5 (C : DMCircuit) (hC : Computes 5 P5 C) : 5 ≤ C.size := by
  by_contra hlt
  obtain ⟨M, hmin, hMle⟩ := minimal_exists P5 C hC
  have hMlt : M.size ≤ 4 := by omega
  obtain ⟨hs, p, hout⟩ := minimal_out_last hmin P5_ess (by omega)
  have hwf := minimal_gate_wf hmin
  have hsum := minimal_fanout_sum hmin hs
  have hfo_ge1 : ∀ w ∈ Finset.range (5 + M.size - 1), 1 ≤ fanout M w := by
    intro w hw
    rw [Finset.mem_range] at hw
    by_cases h5 : w < 5
    · exact minimal_fanout_var hmin P5_ess (by omega) ⟨w, h5⟩
    · have := minimal_fanout_gate hmin P5_ess (by omega) (w - 5) (by omega)
      have heq : 5 + (w - 5) = w := by omega
      rw [heq] at this
      exact this
  have hlb : 5 + M.size - 1 ≤ ∑ w ∈ Finset.range (5 + M.size - 1), fanout M w := by
    calc 5 + M.size - 1
        = ∑ _w ∈ Finset.range (5 + M.size - 1), 1 := by simp
      _ ≤ ∑ w ∈ Finset.range (5 + M.size - 1), fanout M w := Finset.sum_le_sum hfo_ge1
  have hsz4 : M.size = 4 := by omega
  have hfo_eq1 : ∀ w ∈ Finset.range 8, fanout M w = 1 := by
    have hsum8 : ∑ w ∈ Finset.range 8, fanout M w = 8 := by
      have : 5 + M.size - 1 = 8 := by omega
      rw [this] at hsum; omega
    intro w hw
    by_contra hne
    have hge2 : 2 ≤ fanout M w := by
      have := hfo_ge1 w (by rw [Finset.mem_range] at hw ⊢; omega)
      omega
    have hsplit := (Finset.add_sum_erase (Finset.range 8) (fanout M) hw).symm
    have hrest : 7 ≤ ∑ x ∈ (Finset.range 8).erase w, fanout M x := by
      calc 7 = ((Finset.range 8).erase w).card := by simp [Finset.card_erase_of_mem hw]
        _ = ∑ _x ∈ (Finset.range 8).erase w, 1 := by simp
        _ ≤ ∑ x ∈ (Finset.range 8).erase w, fanout M x := Finset.sum_le_sum fun x hx =>
            hfo_ge1 x (by
              have := Finset.mem_range.mp (Finset.mem_of_mem_erase hx)
              exact Finset.mem_range.mpr (by omega))
    omega
  rcases hgs : M.gates with _ | ⟨g0, tail⟩
  · simp [DMCircuit.size, hgs] at hsz4
  have hg0_wf : g0.l < 5 ∧ g0.r < 5 ∧ g0.l ≠ g0.r := by
    have := hwf 0 (by omega)
    simpa [hgs] using this
  have htl_no : ∀ g ∈ tail, g.l ≠ g0.l ∧ g.r ≠ g0.l ∧ g.l ≠ g0.r ∧ g.r ≠ g0.r := by
    have hl1 : fanout M g0.l = 1 := hfo_eq1 g0.l (Finset.mem_range.mpr (by omega))
    have hr1 : fanout M g0.r = 1 := hfo_eq1 g0.r (Finset.mem_range.mpr (by omega))
    simp only [fanout, hgs, List.countP_cons, beq_self_eq_true, Bool.true_or, Bool.or_true,
      ↓reduceIte] at hl1 hr1
    have htl_l : tail.countP (fun g => g.l == g0.l || g.r == g0.l) = 0 := by omega
    have htl_r : tail.countP (fun g => g.l == g0.r || g.r == g0.r) = 0 := by omega
    intro g hg
    have h1 := List.countP_eq_zero.mp htl_l g hg
    have h2 := List.countP_eq_zero.mp htl_r g hg
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h1 h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  let u : Fin 5 := ⟨g0.l, hg0_wf.1⟩
  let v : Fin 5 := ⟨g0.r, hg0_wf.2.1⟩
  have huv : u ≠ v := fun h => hg0_wf.2.2 (congrArg Fin.val h)
  let eval0 (a b : Bool) : Bool :=
    if g0.isOr then (a != g0.pl) || (b != g0.pr) else (a != g0.pl) && (b != g0.pr)
  obtain ⟨a1, a2, b1, b2, x, hev_eq, hP5_ne⟩ :=
    P5_cofactor_ge3 u v (eval0 false false) (eval0 false true)
      (eval0 true false) (eval0 true true) huv
  let xa := Function.update (Function.update x u a1) v a2
  let xb := Function.update (Function.update x u b1) v b2
  have hg0_eq : g0.eval (List.ofFn xa) = g0.eval (List.ofFn xb) := by
    have hxa_u : (List.ofFn xa).getD g0.l false = a1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hg0_wf.1, xa, u, huv]
    have hxa_v : (List.ofFn xa).getD g0.r false = a2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hg0_wf.2.1, xa, v]
    have hxb_u : (List.ofFn xb).getD g0.l false = b1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hg0_wf.1, xb, u, huv]
    have hxb_v : (List.ofFn xb).getD g0.r false = b2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hg0_wf.2.1, xb, v]
    simp only [DMGate.eval, hxa_u, hxa_v, hxb_u, hxb_v]
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> exact hev_eq
  have hw1_eq : ∀ i : ℕ, i ≠ g0.l → i ≠ g0.r →
      (dmStep (List.ofFn xa) g0).getD i false = (dmStep (List.ofFn xb) g0).getD i false := by
    intro i hiu hiv
    unfold dmStep
    by_cases h5 : i < 5
    · rw [List.getD_append (List.ofFn xa) _ _ i (by simp; exact h5),
          List.getD_append (List.ofFn xb) _ _ i (by simp; exact h5),
          List.getD_eq_getElem?_getD, List.getElem?_ofFn,
          List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [h5, ↓reduceDIte, Option.getD_some]
      have hne_u : (⟨i, h5⟩ : Fin 5) ≠ u := fun h => hiu (congrArg Fin.val h)
      have hne_v : (⟨i, h5⟩ : Fin 5) ≠ v := fun h => hiv (congrArg Fin.val h)
      dsimp only [xa, xb]
      rw [Function.update_of_ne hne_v, Function.update_of_ne hne_u,
          Function.update_of_ne hne_v, Function.update_of_ne hne_u]
    · by_cases h5eq : i = 5
      · subst h5eq
        rw [List.getD_append_right (List.ofFn xa) _ _ 5 (by simp),
            List.getD_append_right (List.ofFn xb) _ _ 5 (by simp)]
        simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
        exact hg0_eq
      · rw [List.getD_eq_default (List.ofFn xa ++ _) _ (by simp; omega),
            List.getD_eq_default (List.ofFn xb ++ _) _ (by simp; omega)]
  have hfin := foldl_dmStep_agree_from tail g0.l g0.r htl_no
    (dmStep (List.ofFn xa) g0) (dmStep (List.ofFn xb) g0)
    (by simp [dmStep]) (by simp [dmStep]; omega) (by simp [dmStep]; omega)
    hw1_eq (5 + M.size - 1) (by omega) (by omega)
  have h1 := hmin.1 xa
  have h2 := hmin.1 xb
  simp only [DMCircuit.eval, hout, WireVal.eval, DMCircuit.wires, hgs, List.foldl_cons] at h1 h2
  rw [hfin] at h1
  exact hP5_ne (h1.symm.trans h2)

-- Annihilator helper for DMGate

def annVal (isOr pol : Bool) : Bool :=
  if isOr then !pol else pol

lemma DMGate_ann_left (g : DMGate) (w : List Bool)
    (h : w.getD g.l false = annVal g.isOr g.pl) :
    g.eval w = g.isOr := by
  unfold DMGate.eval annVal at *
  rw [h]
  cases g.isOr <;> cases g.pl <;> simp

lemma DMGate_ann_right (g : DMGate) (w : List Bool)
    (h : w.getD g.r false = annVal g.isOr g.pr) :
    g.eval w = g.isOr := by
  unfold DMGate.eval annVal at *
  rw [h]
  cases g.isOr <;> cases g.pr <;> simp

lemma combine_ann_left (isOr : Bool) (nNext : ℕ) (pol : Bool) (b : WireVal) :
    (combine isOr nNext ((WireVal.const (annVal isOr pol)).xorPol pol) b) = (none, WireVal.const isOr) := by
  cases isOr <;> cases pol <;> rfl

lemma combine_ann_right (isOr : Bool) (nNext : ℕ) (a : WireVal) (pol : Bool) :
    (combine isOr nNext a ((WireVal.const (annVal isOr pol)).xorPol pol)) = (none, WireVal.const isOr) := by
  cases a with
  | const ba => cases ba <;> cases isOr <;> cases pol <;> rfl
  | wire ia pa => cases isOr <;> cases pol <;> rfl

lemma depth1_both_fanout_ge2 {M : DMCircuit} (hmin : MinimalDM 6 C6 M)
    (j : ℕ) (hj : j < M.gates.length)
    (hl : M.gates[j].l < 6) (hr : M.gates[j].r < 6) :
    2 ≤ fanout M M.gates[j].l ∧ 2 ≤ fanout M M.gates[j].r := by
  obtain ⟨hs, p, hout⟩ := minimal_out_last hmin C6_ess (by omega)
  have hwf := minimal_gate_wf hmin j hj
  have hside : ∀ (u v : Fin 6) (a : Bool), u ≠ v →
      (M.gates[j].l == v.val || M.gates[j].r == v.val) = true →
      (∀ w : List Bool, w.getD u.val false = a → M.gates[j].eval w = M.gates[j].isOr) →
      2 ≤ fanout M v.val := by
    intro u v a huv hmem hann
    by_contra hlt2
    have hge1 := minimal_fanout_var hmin C6_ess (by omega) v
    have hfo1 : fanout M v.val = 1 := by omega
    have hsplit : M.gates = M.gates.take j ++ M.gates[j] :: M.gates.drop (j + 1) := by
      simpa using (List.take_append_drop j M.gates).symm.trans (by
        rw [List.drop_eq_getElem_cons hj])
    have hcnt : M.gates.countP (fun g => g.l == v.val || g.r == v.val) = 1 := hfo1
    rw [hsplit, List.countP_append, List.countP_cons, hmem] at hcnt
    simp only [↓reduceIte] at hcnt
    have hpre0 : (M.gates.take j).countP (fun g => g.l == v.val || g.r == v.val) = 0 := by omega
    have hpost0 : (M.gates.drop (j + 1)).countP (fun g => g.l == v.val || g.r == v.val) = 0 := by omega
    have hpre : ∀ g ∈ M.gates.take j, g.l ≠ v.val ∧ g.r ≠ v.val := fun g hg => by
      have := List.countP_eq_zero.mp hpre0 g hg
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at this; exact this
    have hpost : ∀ g ∈ M.gates.drop (j + 1), g.l ≠ v.val ∧ g.r ≠ v.val := fun g hg => by
      have := List.countP_eq_zero.mp hpost0 g hg
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at this; exact this
    obtain ⟨x, hxu, hxne⟩ := C6_restrict_ess u v a huv
    let x' := Function.update x v (!x v)
    have hagree0 : ∀ i : ℕ, i ≠ v.val →
        (List.ofFn x).getD i false = (List.ofFn x').getD i false := by
      intro i hi
      by_cases h6 : i < 6
      · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
            List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [h6, ↓reduceDIte, Option.getD_some]
        have hne : (⟨i, h6⟩ : Fin 6) ≠ v := fun h => hi (congrArg Fin.val h)
        simp [x', Function.update, hne]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    let w1 := (M.gates.take j).foldl dmStep (List.ofFn x)
    let w2 := (M.gates.take j).foldl dmStep (List.ofFn x')
    have hw12 := foldl_dmStep_indep_wire (M.gates.take j) v.val hpre
      (List.ofFn x) (List.ofFn x') (by simp) (by simp) hagree0
    have hw1_len : w1.length = 6 + j := by
      rw [foldl_dmStep_length]; simp [List.length_take]; omega
    have hw2_len : w2.length = 6 + j := by
      rw [foldl_dmStep_length]; simp [List.length_take]; omega
    have hu1 : w1.getD u.val false = a := by
      rw [foldl_dmStep_getD_lt _ _ u.val (by simp)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [u.isLt, hxu]
    have hu2 : w2.getD u.val false = a := by
      rw [← hw12 u.val (fun h => huv (Fin.ext h)), hu1]
    have hgj_eq : M.gates[j].eval w1 = M.gates[j].eval w2 := by
      rw [hann w1 hu1, hann w2 hu2]
    have hstep_agree : ∀ i : ℕ, i ≠ v.val →
        (dmStep w1 M.gates[j]).getD i false = (dmStep w2 M.gates[j]).getD i false := by
      intro i hi
      unfold dmStep
      by_cases hlt : i < 6 + j
      · rw [List.getD_append w1 _ _ i (by omega), List.getD_append w2 _ _ i (by omega)]
        exact hw12 i hi
      · by_cases heq : i = 6 + j
        · subst heq
          rw [List.getD_append_right w1 _ _ _ (by omega), List.getD_append_right w2 _ _ _ (by omega)]
          simp [hw1_len, hw2_len, hgj_eq]
        · rw [List.getD_eq_default (w1 ++ _) _ (by simp [hw1_len]; omega),
              List.getD_eq_default (w2 ++ _) _ (by simp [hw2_len]; omega)]
    have hfin := foldl_dmStep_indep_wire (M.gates.drop (j + 1)) v.val hpost
      (dmStep w1 M.gates[j]) (dmStep w2 M.gates[j])
      (by simp [dmStep, hw1_len, hw2_len]) (by simp [dmStep, hw1_len]; omega)
      hstep_agree (6 + M.size - 1) (by omega)
    have h1 := hmin.1 x
    have h2 := hmin.1 x'
    simp only [DMCircuit.eval, hout, WireVal.eval, DMCircuit.wires] at h1 h2
    rw [hsplit, List.foldl_append, List.foldl_cons] at h1 h2
    change (((M.gates.drop (j + 1)).foldl dmStep (dmStep w1 M.gates[j])).getD (6 + M.size - 1) false != p) = C6 x at h1
    change (((M.gates.drop (j + 1)).foldl dmStep (dmStep w2 M.gates[j])).getD (6 + M.size - 1) false != p) = C6 x' at h2
    rw [hfin] at h1
    exact hxne (h1.symm.trans h2)
  refine ⟨?_, ?_⟩
  · exact hside ⟨M.gates[j].r, hr⟩ ⟨M.gates[j].l, hl⟩ (annVal M.gates[j].isOr M.gates[j].pr)
      (fun h => hwf.2.2 (congrArg Fin.val h).symm)
      (by simp)
      (fun w hw => DMGate_ann_right M.gates[j] w hw)
  · exact hside ⟨M.gates[j].l, hl⟩ ⟨M.gates[j].r, hr⟩ (annVal M.gates[j].isOr M.gates[j].pl)
      (fun h => hwf.2.2 (congrArg Fin.val h))
      (by simp)
      (fun w hw => DMGate_ann_left M.gates[j] w hw)

lemma fanout_Ico_sum (gs : List DMGate) (A B : ℕ) (hAB : A ≤ B)
    (hgs : ∀ g ∈ gs, g.l < B ∧ g.r < B ∧ g.l ≠ g.r) :
    ∑ w ∈ Finset.Ico A B, gs.countP (fun g => g.l == w || g.r == w) =
    (gs.map fun g => (if A ≤ g.l then 1 else 0) + (if A ≤ g.r then 1 else 0)).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := hgs g (List.mem_cons_self ..)
    have hih := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, hih]
    have h1 : ∑ w ∈ Finset.Ico A B, (if (g.l == w || g.r == w) = true then 1 else 0) =
        (if A ≤ g.l then 1 else 0) + (if A ≤ g.r then 1 else 0) := by
      have hterm : ∀ w : ℕ, (if (g.l == w || g.r == w) = true then (1 : ℕ) else 0) =
          (if g.l = w then 1 else 0) + (if g.r = w then 1 else 0) := by
        intro w
        by_cases hlw : g.l = w
        · subst hlw
          have hrw : g.r ≠ g.l := hg.2.2.symm
          simp [hrw]
        · by_cases hrw : g.r = w
          · subst hrw; simp [hlw]
          · simp [hlw, hrw]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib]
      have hl_sum : ∑ w ∈ Finset.Ico A B, (if g.l = w then (1 : ℕ) else 0) = if A ≤ g.l then 1 else 0 := by
        by_cases hAl : A ≤ g.l
        · have hmem : g.l ∈ Finset.Ico A B := Finset.mem_Ico.mpr ⟨hAl, hg.1⟩
          simp [hAl, Finset.sum_ite_eq, hmem]
        · have hmem : g.l ∉ Finset.Ico A B := by simp [hAl]
          simp [hAl, Finset.sum_ite_eq, hmem]
      have hr_sum : ∑ w ∈ Finset.Ico A B, (if g.r = w then (1 : ℕ) else 0) = if A ≤ g.r then 1 else 0 := by
        by_cases hAr : A ≤ g.r
        · have hmem : g.r ∈ Finset.Ico A B := Finset.mem_Ico.mpr ⟨hAr, hg.2.1⟩
          simp [hAr, Finset.sum_ite_eq, hmem]
        · have hmem : g.r ∉ Finset.Ico A B := by simp [hAr]
          simp [hAr, Finset.sum_ite_eq, hmem]
      rw [hl_sum, hr_sum]
    omega

lemma exists_gate_reading {C : DMCircuit} {w : ℕ} (h : 1 ≤ fanout C w) :
    ∃ j : ℕ, ∃ hj : j < C.size, C.gates[j].l = w ∨ C.gates[j].r = w := by
  have hne : C.gates.countP (fun g => g.l == w || g.r == w) ≠ 0 := by
    unfold fanout at h; omega
  have hex : ∃ g ∈ C.gates, (g.l == w || g.r == w) = true := by
    by_contra hno
    push_neg at hno
    apply hne
    rw [List.countP_eq_zero]
    intro g hg
    exact hno g hg
  obtain ⟨g, hg, hcond⟩ := hex
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  simp only [Bool.or_eq_true, beq_iff_eq] at hcond
  exact ⟨j, hj, hcond⟩

lemma simpEmits_false_of_const_l (env : List WireVal) (g : DMGate) (b : Bool)
    (h : env.getD g.l (.const false) = .const b) :
    simpEmits env g = false := by
  unfold simpEmits
  rw [h]
  simp [WireVal.xorPol, combine_const_left]

lemma simpEmits_false_of_const_r (env : List WireVal) (g : DMGate) (b : Bool)
    (h : env.getD g.r (.const false) = .const b) :
    simpEmits env g = false := by
  unfold simpEmits
  rw [h]
  simp [WireVal.xorPol, combine_const_right]

lemma simpTrace_ann_const (nNew : ℕ) (env0 : List WireVal) (gs : List DMGate)
    (j : ℕ) (hj : j < gs.length)
    (h : ((simpTrace nNew env0 gs j).2.getD gs[j].l (.const false) = .const (annVal gs[j].isOr gs[j].pl)) ∨
         ((simpTrace nNew env0 gs j).2.getD gs[j].r (.const false) = .const (annVal gs[j].isOr gs[j].pr))) :
    (simpTrace nNew env0 gs (j + 1)).2.getD (env0.length + j) (.const false) = .const gs[j].isOr := by
  rw [simpTrace_succ nNew env0 gs j hj]
  have hlen := simpTrace_env_length nNew env0 gs j (by omega)
  unfold simpStep
  dsimp only
  rcases h with hl | hr
  · rw [hl, combine_ann_left]
    dsimp only
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hlen]
  · rw [hr, combine_ann_right]
    dsimp only
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hlen]

lemma eq_of_ann_true (isOr1 pl1 pr1 isOr2 pl2 pr2 a b : Bool)
    (h1l : annVal isOr1 pl1 = true) (h1r : annVal isOr1 pr1 = true)
    (h2l : annVal isOr2 pl2 = true) (h2r : annVal isOr2 pr2 = true) :
    ((if isOr1 then (a != pl1) || (b != pr1) else (a != pl1) && (b != pr1)) != (isOr1 != isOr2)) =
    (if isOr2 then (a != pl2) || (b != pr2) else (a != pl2) && (b != pr2)) := by
  revert isOr1 pl1 pr1 isOr2 pl2 pr2 a b h1l h1r h2l h2r
  decide

lemma eq_of_ann_true_swap (isOr1 pl1 pr1 isOr2 pl2 pr2 a b : Bool)
    (h1l : annVal isOr1 pl1 = true) (h1r : annVal isOr1 pr1 = true)
    (h2l : annVal isOr2 pl2 = true) (h2r : annVal isOr2 pr2 = true) :
    ((if isOr1 then (a != pl1) || (b != pr1) else (a != pl1) && (b != pr1)) != (isOr1 != isOr2)) =
    (if isOr2 then (b != pl2) || (a != pr2) else (b != pl2) && (a != pr2)) := by
  revert isOr1 pl1 pr1 isOr2 pl2 pr2 a b h1l h1r h2l h2r
  decide

lemma C6_pigeonhole_contra (M : DMCircuit) (p : Bool)
    (hcomp : Computes 6 C6 M)
    (hsz7 : M.size = 7)
    (hout : M.out = .wire (6 + M.size - 1) p)
    (hwf : ∀ j : ℕ, (hj : j < M.size) → M.gates[j].l < 6 + j ∧ M.gates[j].r < 6 + j ∧ M.gates[j].l ≠ M.gates[j].r)
    (hfo_int : ∀ w : ℕ, 6 ≤ w → w < 12 → fanout M w = 1)
    (hno_other_d1 : ∀ j : ℕ, 0 < j → (hj : j < 7) → ¬ ((M.gates[j]'(by simp [DMCircuit.size] at hsz7; omega)).l < 6 ∧ (M.gates[j]'(by simp [DMCircuit.size] at hsz7; omega)).r < 6)) :
    False := by
  have hIco_sum : ∑ w ∈ Finset.Ico 6 12, fanout M w = 6 := by
    have h1 : ∀ w ∈ Finset.Ico 6 12, fanout M w = 1 := by
      intro w hw
      rw [Finset.mem_Ico] at hw
      exact hfo_int w hw.1 hw.2
    rw [Finset.sum_congr rfl h1]
    simp
  have hlen7 : M.gates.length = 7 := hsz7
  have hmap_sum := fanout_Ico_sum M.gates 6 12 (by omega) (by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have h := hwf j hj
    exact ⟨by omega, by omega, h.2.2⟩)
  change ∑ w ∈ Finset.Ico 6 12, fanout M w = _ at hmap_sum
  rw [hIco_sum] at hmap_sum
  rcases hgs7 : M.gates with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, _ | ⟨g5, _ | ⟨g6, _ | _⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp [DMCircuit.size, hgs7] at hsz7)
  have h1 : 6 ≤ g1.l ∨ 6 ≤ g1.r := by
    have := hno_other_d1 1 (by omega) (by omega); simp [hgs7] at this; omega
  have h2 : 6 ≤ g2.l ∨ 6 ≤ g2.r := by
    have := hno_other_d1 2 (by omega) (by omega); simp [hgs7] at this; omega
  have h3 : 6 ≤ g3.l ∨ 6 ≤ g3.r := by
    have := hno_other_d1 3 (by omega) (by omega); simp [hgs7] at this; omega
  have h4 : 6 ≤ g4.l ∨ 6 ≤ g4.r := by
    have := hno_other_d1 4 (by omega) (by omega); simp [hgs7] at this; omega
  have h5 : 6 ≤ g5.l ∨ 6 ≤ g5.r := by
    have := hno_other_d1 5 (by omega) (by omega); simp [hgs7] at this; omega
  simp only [hgs7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hmap_sum
  have hg6_has_var : g6.l < 6 ∨ g6.r < 6 := by
    by_contra hboth
    have hboth' : 6 ≤ g6.l ∧ 6 ≤ g6.r := by omega
    have c1 : 1 ≤ (if 6 ≤ g1.l then 1 else 0) + (if 6 ≤ g1.r then 1 else 0) := by
      rcases h1 with h | h <;> simp [h]
    have c2 : 1 ≤ (if 6 ≤ g2.l then 1 else 0) + (if 6 ≤ g2.r then 1 else 0) := by
      rcases h2 with h | h <;> simp [h]
    have c3 : 1 ≤ (if 6 ≤ g3.l then 1 else 0) + (if 6 ≤ g3.r then 1 else 0) := by
      rcases h3 with h | h <;> simp [h]
    have c4 : 1 ≤ (if 6 ≤ g4.l then 1 else 0) + (if 6 ≤ g4.r then 1 else 0) := by
      rcases h4 with h | h <;> simp [h]
    have c5 : 1 ≤ (if 6 ≤ g5.l then 1 else 0) + (if 6 ≤ g5.r then 1 else 0) := by
      rcases h5 with h | h <;> simp [h]
    have c6 : 2 ≤ (if 6 ≤ g6.l then 1 else 0) + (if 6 ≤ g6.r then 1 else 0) := by
      simp [hboth'.1, hboth'.2]
    omega
  have hout_eval : ∀ x : Fin 6 → Bool,
      C6 x = (g6.eval ([g0, g1, g2, g3, g4, g5].foldl dmStep (List.ofFn x)) != p) := by
    intro x
    rw [← hcomp x]
    simp only [DMCircuit.eval, hout, WireVal.eval, DMCircuit.wires, DMCircuit.size, hgs7,
      List.length_cons, List.length_nil]
    change ((([g0, g1, g2, g3, g4, g5] ++ [g6]).foldl dmStep (List.ofFn x)).getD 12 false != p) = _
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    let wp := [g0, g1, g2, g3, g4, g5].foldl dmStep (List.ofFn x)
    have hwp_len : wp.length = 12 := by rw [foldl_dmStep_length]; simp
    change ((wp ++ [g6.eval wp]).getD 12 false != p) = _
    rw [List.getD_append_right wp _ false 12 (by omega)]
    simp only [hwp_len, Nat.sub_self, List.getD_cons_zero]
    rfl
  rcases hg6_has_var with hl6 | hr6
  · let v : Fin 6 := ⟨g6.l, hl6⟩
    let a : Bool := annVal g6.isOr g6.pl
    obtain ⟨⟨x, hxv, hxt⟩, ⟨y, hyv, hyf⟩⟩ := C6_restrict_nonconst v a
    have hcx : C6 x = (g6.isOr != p) := by
      rw [hout_eval x, DMGate_ann_left g6]
      rw [foldl_dmStep_getD_lt _ _ g6.l (by simp; exact hl6),
          List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hl6, hxv, v, a]
    have hcy : C6 y = (g6.isOr != p) := by
      rw [hout_eval y, DMGate_ann_left g6]
      rw [foldl_dmStep_getD_lt _ _ g6.l (by simp; exact hl6),
          List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hl6, hyv, v, a]
    rw [hcx] at hxt; rw [hcy] at hyf; rw [hxt] at hyf; exact Bool.noConfusion hyf
  · let v : Fin 6 := ⟨g6.r, hr6⟩
    let a : Bool := annVal g6.isOr g6.pr
    obtain ⟨⟨x, hxv, hxt⟩, ⟨y, hyv, hyf⟩⟩ := C6_restrict_nonconst v a
    have hcx : C6 x = (g6.isOr != p) := by
      rw [hout_eval x, DMGate_ann_right g6]
      rw [foldl_dmStep_getD_lt _ _ g6.r (by simp; exact hr6),
          List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hr6, hxv, v, a]
    have hcy : C6 y = (g6.isOr != p) := by
      rw [hout_eval y, DMGate_ann_right g6]
      rw [foldl_dmStep_getD_lt _ _ g6.r (by simp; exact hr6),
          List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hr6, hyv, v, a]
    rw [hcx] at hxt; rw [hcy] at hyf; rw [hxt] at hyf; exact Bool.noConfusion hyf

lemma C6_ge_8 (C : DMCircuit) (hC : Computes 6 C6 C) : 8 ≤ C.size := by
  by_contra hlt
  obtain ⟨M, hmin, hMle⟩ := minimal_exists C6 C hC
  have hMlt : M.size ≤ 7 := by omega
  have hsz_eq : M.gates.length = M.size := rfl
  obtain ⟨hs, p, hout⟩ := minimal_out_last hmin C6_ess (by omega)
  have hwf := minimal_gate_wf hmin
  have hsum := minimal_fanout_sum hmin hs
  have hfo_ge1 : ∀ w ∈ Finset.range (6 + M.size - 1), 1 ≤ fanout M w := by
    intro w hw
    rw [Finset.mem_range] at hw
    by_cases h6 : w < 6
    · exact minimal_fanout_var hmin C6_ess (by omega) ⟨w, h6⟩
    · have := minimal_fanout_gate hmin C6_ess (by omega) (w - 6) (by omega)
      have heq : 6 + (w - 6) = w := by omega
      rw [heq] at this
      exact this
  have hg0_wf := hwf 0 (by omega)
  have hg0_fo := depth1_both_fanout_ge2 hmin 0 (by omega) (by omega) (by omega)
  let pair : Finset ℕ := {M.gates[0].l, M.gates[0].r}
  have hpair_sub : pair ⊆ Finset.range (6 + M.size - 1) := by
    intro w hw
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hw
    rw [Finset.mem_range]
    rcases hw with rfl | rfl <;> omega
  have hpair_card : pair.card = 2 := Finset.card_pair hg0_wf.2.2
  have hpair_sum : ∑ w ∈ pair, fanout M w = fanout M M.gates[0].l + fanout M M.gates[0].r :=
    Finset.sum_pair hg0_wf.2.2
  have hsplit_sum := (Finset.sum_sdiff hpair_sub (f := fanout M)).symm
  have hrest_card : (Finset.range (6 + M.size - 1) \ pair).card + 2 = 6 + M.size - 1 := by
    have := Finset.card_sdiff_add_card_eq_card hpair_sub
    simpa [hpair_card] using this
  have hrest_lb : (Finset.range (6 + M.size - 1) \ pair).card ≤
      ∑ w ∈ Finset.range (6 + M.size - 1) \ pair, fanout M w := by
    calc (Finset.range (6 + M.size - 1) \ pair).card
        = ∑ _w ∈ Finset.range (6 + M.size - 1) \ pair, 1 := by simp
      _ ≤ ∑ w ∈ Finset.range (6 + M.size - 1) \ pair, fanout M w :=
          Finset.sum_le_sum fun w hw => hfo_ge1 w (Finset.mem_sdiff.mp hw).1
  have hsz7 : M.size = 7 := by omega
  have hlen7 : M.gates.length = 7 := hsz7
  have hfo_l2 : fanout M M.gates[0].l = 2 := by omega
  have hfo_r2 : fanout M M.gates[0].r = 2 := by omega
  have hrest_eq : ∑ w ∈ Finset.range 12 \ pair, fanout M w = (Finset.range 12 \ pair).card := by
    have : 6 + M.size - 1 = 12 := by omega
    rw [this] at hsplit_sum hrest_card hrest_lb hsum
    omega
  have hfo_other1 : ∀ w : ℕ, w < 12 → w ≠ M.gates[0].l → w ≠ M.gates[0].r → fanout M w = 1 := by
    intro w hw hwl hwr
    have hw_mem : w ∈ Finset.range 12 \ pair := by
      simp [pair, hw, hwl, hwr]
    have hge1 : 1 ≤ fanout M w := hfo_ge1 w (Finset.mem_range.mpr (by omega))
    by_contra hne
    have hge2 : 2 ≤ fanout M w := by omega
    have hsp := (Finset.add_sum_erase (Finset.range 12 \ pair) (fanout M) hw_mem).symm
    have hrem : ((Finset.range 12 \ pair).erase w).card ≤
        ∑ x ∈ (Finset.range 12 \ pair).erase w, fanout M x := by
      calc ((Finset.range 12 \ pair).erase w).card
          = ∑ _x ∈ (Finset.range 12 \ pair).erase w, 1 := by simp
        _ ≤ ∑ x ∈ (Finset.range 12 \ pair).erase w, fanout M x :=
            Finset.sum_le_sum fun x hx =>
              hfo_ge1 x (by
                have hx' := Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx)
                have hx12 := Finset.mem_range.mp hx'.1
                exact Finset.mem_range.mpr (by omega))
    have hc := Finset.card_erase_add_one hw_mem
    omega
  -- Helper: if 3 distinct gates fail to emit under rotMap u, contradiction with P5 >= 5
  have hkill3 : ∀ (u : Fin 6) (i1 i2 i3 : ℕ),
      (hi1 : i1 < 7) → (hi2 : i2 < 7) → (hi3 : i3 < 7) → i1 ≠ i2 → i1 ≠ i3 → i2 ≠ i3 →
      let env0 := List.ofFn (rotMap u)
      simpEmits (simpTrace 5 env0 M.gates i1).2 M.gates[i1] = false →
      simpEmits (simpTrace 5 env0 M.gates i2).2 M.gates[i2] = false →
      simpEmits (simpTrace 5 env0 M.gates i3).2 M.gates[i3] = false → False := by
    intro u i1 i2 i3 hi1 hi2 hi3 h12 h13 h23 env0 he1 he2 he3
    let C5 := simplifyDM 5 env0 M
    have hcomp5 : Computes 5 P5 C5 := by
      intro y
      rw [simplifyDM_eval 5 env0 M (List.ofFn y) (by simp) (by
        intro v hv; simp only [env0, List.mem_ofFn] at hv; obtain ⟨k, rfl⟩ := hv; exact rotMap_wf u k)]
      have hmap : env0.map (fun v => v.eval (List.ofFn y)) =
          List.ofFn (fun k : Fin 6 => (rotMap u k).eval (List.ofFn y)) := by
        simp [env0, List.map_ofFn]
      rw [hmap, hmin.1, C6_rotMap_eq_P5]
    have hge5 := P5_ge_5 C5 hcomp5
    let S : Finset ℕ := {i1, i2, i3}
    have hScard : S.card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
    have hSsub : S ⊆ Finset.range M.size := by
      intro i hi
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_range]
      rcases hi with rfl | rfl | rfl <;> omega
    have hsum_le := sum_le_card_sub_of_zeros
      (n := M.size)
      (f := fun i => if h : i < M.size then
        (if simpEmits (simpTrace 5 env0 M.gates i).2 M.gates[i] then 1 else 0) else 0)
      S
      (fun i _ => by split <;> [split <;> omega; omega])
      hSsub
      (by
        intro i hi
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with h | h | h
        · rw [h]; split
          · exact if_neg (by change simpEmits (simpTrace 5 env0 M.gates i1).2 (M.gates[i1]'(by omega)) = true → False; rw [he1]; decide)
          · omega
        · rw [h]; split
          · exact if_neg (by change simpEmits (simpTrace 5 env0 M.gates i2).2 (M.gates[i2]'(by omega)) = true → False; rw [he2]; decide)
          · omega
        · rw [h]; split
          · exact if_neg (by change simpEmits (simpTrace 5 env0 M.gates i3).2 (M.gates[i3]'(by omega)) = true → False; rw [he3]; decide)
          · omega)
    rw [← simplifyDM_size] at hsum_le
    dsimp only [C5] at hge5
    omega
  -- Prove no gate j in {1..6} has both inputs < 6
  have hno_other_d1 : ∀ j : ℕ, 0 < j → (hj : j < 7) → ¬ (M.gates[j].l < 6 ∧ M.gates[j].r < 6) := by
    intro j hjpos hj ⟨hjl, hjr⟩
    have hgj_fo := depth1_both_fanout_ge2 hmin j (by omega) hjl hjr
    have hgj_wf := hwf j (by omega)
    have hl_in : M.gates[j].l = M.gates[0].l ∨ M.gates[j].l = M.gates[0].r := by
      by_contra h
      push_neg at h
      have := hfo_other1 M.gates[j].l (by omega) h.1 h.2
      omega
    have hr_in : M.gates[j].r = M.gates[0].l ∨ M.gates[j].r = M.gates[0].r := by
      by_contra h
      push_neg at h
      have := hfo_other1 M.gates[j].r (by omega) h.1 h.2
      omega
    have hpair_eq : (M.gates[j].l = M.gates[0].l ∧ M.gates[j].r = M.gates[0].r) ∨
        (M.gates[j].l = M.gates[0].r ∧ M.gates[j].r = M.gates[0].l) := by
      rcases hl_in with h1 | h1 <;> rcases hr_in with h2 | h2
      · exfalso; exact hgj_wf.2.2 (h1.trans h2.symm)
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exfalso; exact hgj_wf.2.2 (h1.trans h2.symm)
    -- First show j < 6 (cannot be output gate 6)
    have hj_lt6 : j < 6 := by
      by_contra hj6
      have hj_eq6 : j = 6 := by omega
      subst hj_eq6
      -- Pick a variable v : Fin 6 distinct from g0.l and g0.r
      have hex_v : ∃ v : Fin 6, v.val ≠ M.gates[0].l ∧ v.val ≠ M.gates[0].r := by
        set a0 := M.gates[0].l
        set b0 := M.gates[0].r
        by_cases h0 : (0 : ℕ) ≠ a0 ∧ (0 : ℕ) ≠ b0
        · exact ⟨⟨0, by omega⟩, h0⟩
        · by_cases h1 : (1 : ℕ) ≠ a0 ∧ (1 : ℕ) ≠ b0
          · exact ⟨⟨1, by omega⟩, h1⟩
          · refine ⟨⟨2, by omega⟩, ?_⟩
            dsimp only
            simp only [not_and_or, ne_eq, not_not] at h0 h1
            rcases h0 with h | h <;> rcases h1 with h' | h' <;> exact ⟨by omega, by omega⟩
      obtain ⟨v, hvl, hvr⟩ := hex_v
      obtain ⟨x, hxne⟩ := C6_ess v
      let x' := Function.update x v (!x v)
      have hsp : M.gates = M.gates.take 6 ++ [M.gates[6]] := by
        have h := (List.take_append_drop 6 M.gates).symm
        rw [List.drop_eq_getElem_cons (by omega),
            List.drop_eq_nil_of_le (by omega)] at h
        exact h
      have hev_eq : ∀ y : Fin 6 → Bool, M.eval (List.ofFn y) =
          (M.gates[6].eval (List.ofFn y) != p) := by
        intro y
        simp only [DMCircuit.eval, hout, WireVal.eval, DMCircuit.wires, hsz7]
        conv_lhs => rw [hsp, List.foldl_append, List.foldl_cons, List.foldl_nil]
        let wp := (M.gates.take 6).foldl dmStep (List.ofFn y)
        have hwp_len : wp.length = 12 := by
          rw [foldl_dmStep_length]; simp [List.length_take, hlen7]
        change ((wp ++ [M.gates[6].eval wp]).getD (6 + 7 - 1) false != p) = _
        rw [List.getD_append_right wp _ false 12 (by omega)]
        simp only [hwp_len, Nat.sub_self, List.getD_cons_zero]
        congr 1
        unfold DMGate.eval
        rw [foldl_dmStep_getD_lt _ _ M.gates[6].l (by simp; omega),
            foldl_dmStep_getD_lt _ _ M.gates[6].r (by simp; omega)]
      have hl_ne_v : M.gates[6].l ≠ v.val := by rcases hpair_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      have hr_ne_v : M.gates[6].r ≠ v.val := by rcases hpair_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      have hgl_eq : (List.ofFn x).getD M.gates[6].l false = (List.ofFn x').getD M.gates[6].l false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
            List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hjl, ↓reduceDIte, Option.getD_some]
        have hne : (⟨M.gates[6].l, hjl⟩ : Fin 6) ≠ v := fun h => hl_ne_v (congrArg Fin.val h)
        simp [x', Function.update, hne]
      have hgr_eq : (List.ofFn x).getD M.gates[6].r false = (List.ofFn x').getD M.gates[6].r false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
            List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hjr, ↓reduceDIte, Option.getD_some]
        have hne : (⟨M.gates[6].r, hjr⟩ : Fin 6) ≠ v := fun h => hr_ne_v (congrArg Fin.val h)
        simp [x', Function.update, hne]
      have h1 := (hmin.1 x).symm.trans (hev_eq x)
      have h2 := (hmin.1 x').symm.trans (hev_eq x')
      rw [h1, h2] at hxne
      apply hxne
      simp only [DMGate.eval, hgl_eq, hgr_eq]
    -- Helper to get rotMap env value at u
    have hrot_u : ∀ (u : Fin 6) (k : ℕ), k ≤ 7 →
        (simpTrace 5 (List.ofFn (rotMap u)) M.gates k).2.getD u.val (.const false) = .const false := by
      intro u k hk
      rw [simpTrace_env_mono 5 (List.ofFn (rotMap u)) M.gates (Nat.zero_le k) (by omega) u.val
        (by simp [simpTrace])]
      simp only [simpTrace, List.take_zero, List.foldl_nil]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [u.isLt, rotMap]
    -- Case A: gate 0 is annihilated by false on some input u
    have hcaseA : ∀ (u : Fin 6),
        (M.gates[0].l = u.val ∧ annVal M.gates[0].isOr M.gates[0].pl = false) ∨
        (M.gates[0].r = u.val ∧ annVal M.gates[0].isOr M.gates[0].pr = false) → False := by
      intro u hu
      let env0 := List.ofFn (rotMap u)
      have hfo6 : 1 ≤ fanout M 6 := by
        have := hfo_other1 6 (by omega) (by omega) (by omega); omega
      obtain ⟨h0, hh0_lt, hh0_rd⟩ := exists_gate_reading hfo6
      have hh0_gt0 : 0 < h0 := by
        have := hwf h0 hh0_lt; rcases hh0_rd with h | h <;> omega
      have hh0_ne_j : h0 ≠ j := by
        intro heq; subst heq; rcases hh0_rd with h | h <;> omega
      have he0 : simpEmits (simpTrace 5 env0 M.gates 0).2 M.gates[0] = false := by
        rcases hu with ⟨hl0, _⟩ | ⟨hr0, _⟩
        · exact simpEmits_false_of_const_l _ _ false (by rw [hl0]; exact hrot_u u 0 (by omega))
        · exact simpEmits_false_of_const_r _ _ false (by rw [hr0]; exact hrot_u u 0 (by omega))
      have hconst6 : (simpTrace 5 env0 M.gates 1).2.getD 6 (.const false) = .const M.gates[0].isOr := by
        have h := simpTrace_ann_const 5 env0 M.gates 0 (by omega) (by
          rcases hu with ⟨hl0, ha0⟩ | ⟨hr0, ha0⟩
          · left
            have h1 : (M.gates[0]'(by omega)).l = u.val := hl0
            have h2 : annVal (M.gates[0]'(by omega)).isOr (M.gates[0]'(by omega)).pl = false := ha0
            rw [h1, h2]; exact hrot_u u 0 (by omega)
          · right
            have h1 : (M.gates[0]'(by omega)).r = u.val := hr0
            have h2 : annVal (M.gates[0]'(by omega)).isOr (M.gates[0]'(by omega)).pr = false := ha0
            rw [h1, h2]; exact hrot_u u 0 (by omega))
        have hlen6 : env0.length + 0 = 6 := by simp [env0]
        rw [hlen6] at h
        exact h
      have hh0_const : (simpTrace 5 env0 M.gates h0).2.getD 6 (.const false) = .const M.gates[0].isOr := by
        rw [simpTrace_env_mono 5 env0 M.gates (show 1 ≤ h0 by omega) (by omega) 6
          (by rw [simpTrace_env_length 5 env0 M.gates 1 (by omega)]; simp [env0])]
        exact hconst6
      have heh0 : simpEmits (simpTrace 5 env0 M.gates h0).2 M.gates[h0] = false := by
        rcases hh0_rd with hl' | hr'
        · exact simpEmits_false_of_const_l _ _ M.gates[0].isOr (by rw [hl']; exact hh0_const)
        · exact simpEmits_false_of_const_r _ _ M.gates[0].isOr (by rw [hr']; exact hh0_const)
      have hej : simpEmits (simpTrace 5 env0 M.gates j).2 M.gates[j] = false := by
        have hju : M.gates[j].l = u.val ∨ M.gates[j].r = u.val := by
          rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases hpair_eq with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> omega
        rcases hju with h1 | h1
        · exact simpEmits_false_of_const_l _ _ false (by rw [h1]; exact hrot_u u j (by omega))
        · exact simpEmits_false_of_const_r _ _ false (by rw [h1]; exact hrot_u u j (by omega))
      exact hkill3 u 0 h0 j (by omega) (by omega) hj (by omega) (by omega) hh0_ne_j he0 heh0 hej
    -- Case B: gate j is annihilated by false on some input u
    have hcaseB : ∀ (u : Fin 6),
        (M.gates[j].l = u.val ∧ annVal M.gates[j].isOr M.gates[j].pl = false) ∨
        (M.gates[j].r = u.val ∧ annVal M.gates[j].isOr M.gates[j].pr = false) → False := by
      intro u hu
      let env0 := List.ofFn (rotMap u)
      have hfoj : 1 ≤ fanout M (6 + j) := by
        have := hfo_other1 (6 + j) (by omega) (by omega) (by omega); omega
      obtain ⟨hj', hhj'_lt, hhj'_rd⟩ := exists_gate_reading hfoj
      have hhj'_gtj : j < hj' := by
        have := hwf hj' hhj'_lt; rcases hhj'_rd with h | h <;> omega
      have he0 : simpEmits (simpTrace 5 env0 M.gates 0).2 M.gates[0] = false := by
        have h0u : M.gates[0].l = u.val ∨ M.gates[0].r = u.val := by
          rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases hpair_eq with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> omega
        rcases h0u with h1 | h1
        · exact simpEmits_false_of_const_l _ _ false (by rw [h1]; exact hrot_u u 0 (by omega))
        · exact simpEmits_false_of_const_r _ _ false (by rw [h1]; exact hrot_u u 0 (by omega))
      have hej : simpEmits (simpTrace 5 env0 M.gates j).2 M.gates[j] = false := by
        rcases hu with ⟨hlj, _⟩ | ⟨hrj, _⟩
        · exact simpEmits_false_of_const_l _ _ false (by rw [hlj]; exact hrot_u u j (by omega))
        · exact simpEmits_false_of_const_r _ _ false (by rw [hrj]; exact hrot_u u j (by omega))
      have hconstj : (simpTrace 5 env0 M.gates (j + 1)).2.getD (6 + j) (.const false) = .const M.gates[j].isOr := by
        have h := simpTrace_ann_const 5 env0 M.gates j (by omega) (by
          rcases hu with ⟨hlj, haj⟩ | ⟨hrj, haj⟩
          · left; rw [haj]; dsimp only [env0]; rw [hlj]; exact hrot_u u j (by omega)
          · right; rw [haj]; dsimp only [env0]; rw [hrj]; exact hrot_u u j (by omega))
        have hlenj : env0.length + j = 6 + j := by simp [env0]
        rw [hlenj] at h
        exact h
      have hhj'_const : (simpTrace 5 env0 M.gates hj').2.getD (6 + j) (.const false) = .const M.gates[j].isOr := by
        rw [simpTrace_env_mono 5 env0 M.gates (show j + 1 ≤ hj' by omega) (by omega) (6 + j)
          (by rw [simpTrace_env_length 5 env0 M.gates (j + 1) (by omega)]; simp [env0])]
        exact hconstj
      have hehj' : simpEmits (simpTrace 5 env0 M.gates hj').2 M.gates[hj'] = false := by
        rcases hhj'_rd with hl' | hr'
        · exact simpEmits_false_of_const_l _ _ M.gates[j].isOr (by rw [hl']; exact hhj'_const)
        · exact simpEmits_false_of_const_r _ _ M.gates[j].isOr (by rw [hr']; exact hhj'_const)
      exact hkill3 u 0 j hj' (by omega) hj (by omega) (by omega) (by omega) (by omega) he0 hej hehj'
    -- Now all four annVals must be true, so gate j equals gate 0 up to polarity!
    have hj_len' : j < M.gates.length := by omega
    have h0_len' : 0 < M.gates.length := by omega
    let g0_ := M.gates[0]'h0_len'
    let gj_ := M.gates[j]'hj_len'
    have ha0l : annVal g0_.isOr g0_.pl = true := by
      cases h : annVal g0_.isOr g0_.pl
      · exact absurd (Or.inl ⟨rfl, h⟩) (hcaseA ⟨g0_.l, hg0_wf.1⟩)
      · rfl
    have ha0r : annVal g0_.isOr g0_.pr = true := by
      cases h : annVal g0_.isOr g0_.pr
      · exact absurd (Or.inr ⟨rfl, h⟩) (hcaseA ⟨g0_.r, hg0_wf.2.1⟩)
      · rfl
    have hajl : annVal gj_.isOr gj_.pl = true := by
      cases h : annVal gj_.isOr gj_.pl
      · exact absurd (Or.inl ⟨rfl, h⟩) (hcaseB ⟨gj_.l, hjl⟩)
      · rfl
    have hajr : annVal gj_.isOr gj_.pr = true := by
      cases h : annVal gj_.isOr gj_.pr
      · exact absurd (Or.inr ⟨rfl, h⟩) (hcaseB ⟨gj_.r, hjr⟩)
      · rfl
    let pol : Bool := g0_.isOr != gj_.isOr
    let M' := replaceGate 6 j 6 pol M
    have hM'_comp : Computes 6 C6 M' := by
      intro x
      rw [replaceGate_eval 6 j 6 pol M (List.ofFn x) (by simp) (by omega) (by omega)]
      · exact hmin.1 x
      · dsimp only
        have htake : M.gates.take j = g0_ :: (M.gates.take j).tail := by
          rcases hgs : M.gates with _ | ⟨g0, tl⟩
          · simp [DMCircuit.size, hgs] at hsz7
          · have h1 : j = (j - 1) + 1 := by omega
            have hg0_eq : g0_ = g0 := by simp [g0_, hgs]
            rw [hg0_eq, h1]
            rfl
        let wPre := (M.gates.take j).foldl dmStep (List.ofFn x)
        have h6 : wPre.getD 6 false = g0_.eval (List.ofFn x) := by
          change ((M.gates.take j).foldl dmStep (List.ofFn x)).getD 6 false = _
          rw [htake, List.foldl_cons, foldl_dmStep_getD_lt _ _ 6 (by simp [dmStep])]
          unfold dmStep
          rw [List.getD_append_right (List.ofFn x) _ false 6 (by simp)]
          simp
        have hgl_pre : wPre.getD gj_.l false = (List.ofFn x).getD gj_.l false :=
          foldl_dmStep_getD_lt _ _ gj_.l (by simp; exact hjl)
        have hgr_pre : wPre.getD gj_.r false = (List.ofFn x).getD gj_.r false :=
          foldl_dmStep_getD_lt _ _ gj_.r (by simp; exact hjr)
        change (wPre.getD 6 false != pol) = gj_.eval wPre
        rw [h6]
        simp only [DMGate.eval, hgl_pre, hgr_pre, pol]
        rcases hpair_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · change gj_.l = g0_.l at h1; change gj_.r = g0_.r at h2
          rw [h1, h2]
          exact eq_of_ann_true g0_.isOr g0_.pl g0_.pr gj_.isOr gj_.pl gj_.pr
            ((List.ofFn x).getD g0_.l false) ((List.ofFn x).getD g0_.r false)
            ha0l ha0r hajl hajr
        · change gj_.l = g0_.r at h1; change gj_.r = g0_.l at h2
          rw [h1, h2]
          exact eq_of_ann_true_swap g0_.isOr g0_.pl g0_.pr gj_.isOr gj_.pl gj_.pr
            ((List.ofFn x).getD g0_.l false) ((List.ofFn x).getD g0_.r false)
            ha0l ha0r hajl hajr
    have hle := hmin.2 M' hM'_comp
    have hsz := replaceGate_size 6 j 6 pol M (by omega)
    dsimp only [M'] at hle
    omega
  -- Pigeonhole on internal gate wires 6..11
  exact C6_pigeonhole_contra M p hmin.1 hsz7 hout hwf
    (fun w hw6 hw12 => hfo_other1 w hw12 (by omega) (by omega))
    hno_other_d1

-- Part 5: Restricting f8 (x0 = false, then x3 = false and reindex) to C6

def f8 (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
   x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) || x 0 || x 3

def env8to7 : List WireVal :=
  [.const false, .wire 0 false, .wire 1 false, .wire 2 false,
   .wire 3 false, .wire 4 false, .wire 5 false, .wire 6 false]

def f7 (y : Fin 7 → Bool) : Bool :=
  f8 (fun i : Fin 8 => (env8to7.getD i.val (.const false)).eval (List.ofFn y))

-- In Fin 7: index 0=x1, 1=x2, 2=x3, 3=x4, 4=x5, 5=x6, 6=x7
-- C6(c0,c1,c2,c3,c4,c5) corresponds to (x1, x2, x6, x4, x7, x5)
-- So Fin 7 wire 0->c0, 1->c1, 2->const false, 3->c3, 4->c5, 5->c2, 6->c4
def env7to6 : List WireVal :=
  [.wire 0 false, .wire 1 false, .const false, .wire 3 false,
   .wire 5 false, .wire 2 false, .wire 4 false]

lemma f7_to_C6 :
    ∀ z : Fin 6 → Bool,
      f7 (fun i : Fin 7 => (env7to6.getD i.val (.const false)).eval (List.ofFn z)) = C6 z := by
  decide

lemma restrict_const_kills_one {n m : ℕ} (f : (Fin n → Bool) → Bool) (C : DMCircuit)
    (hC : Computes n f C) (env0 : List WireVal) (v : Fin n)
    (henv_len : env0.length = n)
    (hv_const : env0.getD v.val (.const false) = .const false)
    (hv_ess : IsEss f v)
    (hnot_single : ∃ w : Fin n, w ≠ v ∧ IsEss f w) :
    (simplifyDM m env0 C).size + 1 ≤ C.size := by
  have hex_gate : ∃ j : ℕ, ∃ hj : j < C.size, C.gates[j].l = v.val ∨ C.gates[j].r = v.val := by
    by_contra hno
    push_neg at hno
    have hall : ∀ g ∈ C.gates, g.l ≠ v.val ∧ g.r ≠ v.val := by
      intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact hno j hj
    cases ho : C.out with
    | const b =>
      obtain ⟨x, hx⟩ := hv_ess
      have h1 := hC x
      have h2 := hC (Function.update x v (!x v))
      simp [DMCircuit.eval, ho, WireVal.eval] at h1 h2
      exact hx (h1.symm.trans h2)
    | wire idx p =>
      by_cases hidx : idx = v.val
      · subst hidx
        obtain ⟨w, hwv, x, hx⟩ := hnot_single
        have h1 := hC x
        have h2 := hC (Function.update x w (!x w))
        simp only [DMCircuit.eval, ho, WireVal.eval, DMCircuit.wires] at h1 h2
        rw [foldl_dmStep_getD_lt _ _ v.val (by simp)] at h1 h2
        have heq : (List.ofFn x).getD v.val false =
            (List.ofFn (Function.update x w (!x w))).getD v.val false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
              List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp [v.isLt, Function.update, hwv.symm]
        rw [heq] at h1
        exact hx (h1.symm.trans h2)
      · obtain ⟨x, hx⟩ := hv_ess
        have h1 := hC x
        have h2 := hC (Function.update x v (!x v))
        have hagree : ∀ i : ℕ, i ≠ v.val →
            (List.ofFn x).getD i false = (List.ofFn (Function.update x v (!x v))).getD i false := by
          intro i hi
          by_cases hn : i < n
          · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
                List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            simp only [hn, ↓reduceDIte, Option.getD_some]
            have hne : (⟨i, hn⟩ : Fin n) ≠ v := fun h => hi (congrArg Fin.val h)
            simp [Function.update, hne]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        have hwire := foldl_dmStep_indep_wire C.gates v.val hall
          (List.ofFn x) (List.ofFn (Function.update x v (!x v)))
          (by simp) (by simp) hagree idx hidx
        simp only [DMCircuit.eval, ho, WireVal.eval, DMCircuit.wires] at h1 h2
        rw [hwire] at h1
        exact hx (h1.symm.trans h2)
  obtain ⟨j, hj, hjd⟩ := hex_gate
  have hj' : j < C.gates.length := hj
  have hv_j : (simpTrace m env0 C.gates j).2.getD v.val (.const false) = .const false := by
    rw [simpTrace_env_mono m env0 C.gates (Nat.zero_le j) (by omega) v.val
      (by simp [simpTrace, henv_len])]
    simpa [simpTrace] using hv_const
  have hej : simpEmits (simpTrace m env0 C.gates j).2 (C.gates[j]'hj') = false := by
    rcases hjd with hl | hr
    · have hl' : (C.gates[j]'hj').l = v.val := hl
      exact simpEmits_false_of_const_l _ _ false (by rw [hl']; exact hv_j)
    · have hr' : (C.gates[j]'hj').r = v.val := hr
      exact simpEmits_false_of_const_r _ _ false (by rw [hr']; exact hv_j)
  have hsum := sum_le_card_sub_of_zeros
    (n := C.size)
    (f := fun i => if h : i < C.size then
      (if simpEmits (simpTrace m env0 C.gates i).2 C.gates[i] then 1 else 0) else 0)
    {j}
    (fun i _ => by split <;> [split <;> omega; omega])
    (by intro i hi; simp at hi; subst hi; exact Finset.mem_range.mpr hj)
    (by
      intro i hi; simp at hi
      rw [hi]; split
      · have : simpEmits (simpTrace m env0 C.gates j).2 (C.gates[j]'hj) = false := hej
        simp only [this, Bool.false_eq_true, ↓reduceIte]
      · omega)
  rw [← simplifyDM_size] at hsum
  simpa using hsum

lemma f8_ess0 : IsEss f8 0 := ⟨fun _ => false, by decide⟩
lemma f8_ess3 : IsEss f8 3 := ⟨fun _ => false, by decide⟩
lemma f7_ess2 : IsEss f7 2 := ⟨fun _ => false, by decide⟩
lemma f7_ess0 : IsEss f7 0 := ⟨fun i => i == 1, by decide⟩

lemma f8_ge_10 (D8 : DMCircuit) (hD8 : Computes 8 f8 D8) : 10 ≤ D8.size := by
  let D7 := simplifyDM 7 env8to7 D8
  have hD7_comp : Computes 7 f7 D7 := by
    intro y
    rw [simplifyDM_eval 7 env8to7 D8 (List.ofFn y) (by simp) (by
      intro v hv; simp [env8to7] at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [WireVal.wf])]
    have hmap : env8to7.map (fun v => v.eval (List.ofFn y)) =
        List.ofFn (fun i : Fin 8 => (env8to7.getD i.val (.const false)).eval (List.ofFn y)) := by
      apply List.ext_getElem
      · simp [env8to7]
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_ofFn]
        rw [List.getD_eq_getElem _ _ (by simp [env8to7] at hi2 ⊢; omega)]
    rw [hmap]
    exact hD8 _
  have h78 : D7.size + 1 ≤ D8.size :=
    restrict_const_kills_one f8 D8 hD8 env8to7 0 rfl rfl f8_ess0 ⟨3, by decide, f8_ess3⟩
  let D6 := simplifyDM 6 env7to6 D7
  have hD6_comp : Computes 6 C6 D6 := by
    intro z
    rw [simplifyDM_eval 6 env7to6 D7 (List.ofFn z) (by simp) (by
      intro v hv; simp [env7to6] at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [WireVal.wf])]
    have hmap : env7to6.map (fun v => v.eval (List.ofFn z)) =
        List.ofFn (fun i : Fin 7 => (env7to6.getD i.val (.const false)).eval (List.ofFn z)) := by
      apply List.ext_getElem
      · simp [env7to6]
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_ofFn]
        rw [List.getD_eq_getElem _ _ (by simp [env7to6] at hi2 ⊢; omega)]
    rw [hmap, hD7_comp, f7_to_C6]
  have h67 : D6.size + 1 ≤ D7.size :=
    restrict_const_kills_one f7 D7 hD7_comp env7to6 2 rfl rfl f7_ess2 ⟨0, by decide, f7_ess0⟩
  have h6ge8 := C6_ge_8 D6 hD6_comp
  omega

theorem core :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ));
    ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      PEqualNP.MetaComplexity.FanInTwo x3 →
      (∀ (x7 : Fin (8 : ℕ) → Bool), x3.eval (x2.wires (List.ofFn x7) ++ [x4]) = (x1 x7 || x7 (0 : Fin (8 : ℕ)) || x7 (3 : Fin (8 : ℕ)))) →
      (10 : ℕ) + List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (if x8.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains ((8 : ℕ) + x2.size)) x3.gates ≤ x2.size + x3.size := by
  intro x1 x2 x3 x4 hf2 hf3 heval
  obtain ⟨D8, hsz, hD8_ev⟩ := compile_x2_x3 x2 x3 x4 hf2 hf3
  have hD8_comp : Computes 8 f8 D8 := fun x => (hD8_ev x).trans (heval x)
  have h10 := f8_ge_10 D8 hD8_comp
  omega

end PEqualNP.Outside.L_meta_3059

theorem PEqualNP.Outside.L_meta_3059 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x7 : Fin (8 : ℕ) → Bool), x3.eval (x2.wires (List.ofFn x7) ++ [x4]) = (x1 x7 || x7 (0 : Fin (8 : ℕ)) || x7 (3 : Fin (8 : ℕ)))) → (10 : ℕ) + List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (if x8.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains ((8 : ℕ) + x2.size)) x3.gates ≤ x2.size + x3.size :=
  PEqualNP.Outside.L_meta_3059.core


