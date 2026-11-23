import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_171_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def effReads (g : Gate) (u : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some u) ∨
  (g.op ≠ GateOp.not ∧ u ∈ g.inputs)

private def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private lemma runGates_nil (w : List Bool) : runGates [] w = w := rfl

private lemma runGates_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    runGates (g :: gs) w =
      runGates gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma runGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    runGates (gs1 ++ gs2) w = runGates gs2 (runGates gs1 w) := by
  unfold runGates
  exact List.foldl_append

private lemma runGates_length (gs : List Gate) (w : List Bool) :
    (runGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runGates]
  | cons g gs ih =>
    rw [runGates_cons, ih]
    simp
    omega

private lemma getD_eq_default_of_le {α : Type} (w : List α) (d : α) (i : ℕ) (h : w.length ≤ i) :
    w.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private lemma getD_append_left {α : Type} (w1 w2 : List α) (d : α) (i : ℕ) (h : i < w1.length) :
    (w1 ++ w2).getD i d = w1.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private lemma getD_append_right {α : Type} (w1 w2 : List α) (d : α) (i : ℕ) (h : w1.length ≤ i) :
    (w1 ++ w2).getD i d = w2.getD (i - w1.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private def remapWire (m top u : ℕ) : ℕ :=
  if u < m then u else if u = m then top else u - 1

private def remapGate (m top : ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (remapWire m top) }

private lemma runGates_remap_before (m top : ℕ) (hm : m ≤ top) :
    ∀ (gs : List Gate) (w : List Bool), w.length + gs.length ≤ m →
      runGates (gs.map (remapGate m top)) w = runGates gs w
  | [], _, _ => rfl
  | g :: gs, w, hlen => by
    simp only [List.map_cons, runGates_cons]
    have hw : w.length < m := by
      simp only [List.length_cons] at hlen
      omega
    have hmap :
        (remapGate m top g).inputs.map (fun i => w.getD i false) =
          g.inputs.map (fun i => w.getD i false) := by
      simp only [remapGate, List.map_map]
      apply List.map_congr_left
      intro u _
      simp only [Function.comp_apply, remapWire]
      split_ifs with h1 h2
      · rfl
      · rw [getD_eq_default_of_le w false top (by omega),
          getD_eq_default_of_le w false u (by omega)]
      · rw [getD_eq_default_of_le w false (u - 1) (by omega),
          getD_eq_default_of_le w false u (by omega)]
    rw [hmap]
    simp only [remapGate]
    apply runGates_remap_before m top hm gs
    simp only [List.length_append, List.length_singleton]
    simp only [List.length_cons] at hlen
    omega

private lemma getD_remap_skip (w0 w1 : List Bool) (b : Bool) (top u : ℕ) (hu : u ≠ w0.length) :
    (w0 ++ w1).getD (remapWire w0.length top u) false = (w0 ++ b :: w1).getD u false := by
  unfold remapWire
  split_ifs with h1
  · rw [getD_append_left w0 w1 false u h1, getD_append_left w0 (b :: w1) false u h1]
  · have hge : w0.length ≤ u - 1 := by omega
    have hge2 : w0.length ≤ u := by omega
    rw [getD_append_right w0 w1 false (u - 1) hge, getD_append_right w0 (b :: w1) false u hge2]
    have heq : u - w0.length = (u - 1 - w0.length) + 1 := by omega
    rw [heq]
    rfl

private lemma gate_eval_remap_skip (w0 w1 : List Bool) (b : Bool) (top : ℕ) (g : Gate)
    (hno : ¬ effReads g w0.length) :
    (remapGate w0.length top g).op.eval
      ((remapGate w0.length top g).inputs.map fun i => (w0 ++ w1).getD i false) =
    g.op.eval (g.inputs.map fun i => (w0 ++ b :: w1).getD i false) := by
  by_cases hop : g.op = GateOp.not
  · have hhd : g.inputs.head? ≠ some w0.length := by
      intro h
      exact hno (Or.inl ⟨hop, h⟩)
    simp only [remapGate, hop, GateOp.eval]
    cases h : g.inputs with
    | nil => rfl
    | cons u us =>
      simp only [h, List.head?_cons, ne_eq, Option.some.injEq] at hhd
      simp only [List.map_cons, List.headD_cons]
      rw [getD_remap_skip w0 w1 b top u hhd]
  · have hmem : w0.length ∉ g.inputs := by
      intro h
      exact hno (Or.inr ⟨hop, h⟩)
    simp only [remapGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    simp only [Function.comp_apply]
    exact getD_remap_skip w0 w1 b top u (fun heq => hmem (heq ▸ hu))

private lemma runGates_remap_after (w0 : List Bool) (b : Bool) (top : ℕ) :
    ∀ (gs : List Gate) (w1 : List Bool),
      (∀ g ∈ gs, ¬ effReads g w0.length) →
      ∀ u, u ≠ w0.length →
        (runGates (gs.map (remapGate w0.length top)) (w0 ++ w1)).getD (remapWire w0.length top u) false =
          (runGates gs (w0 ++ b :: w1)).getD u false
  | [], w1, _, u, hu => getD_remap_skip w0 w1 b top u hu
  | g :: gs, w1, hno, u, hu => by
    simp only [List.map_cons, runGates_cons]
    have hg : ¬ effReads g w0.length := hno g List.mem_cons_self
    have hval := gate_eval_remap_skip w0 w1 b top g hg
    rw [hval]
    have ha1 : (w0 ++ w1) ++ [g.op.eval (g.inputs.map fun i => (w0 ++ b :: w1).getD i false)] =
        w0 ++ (w1 ++ [g.op.eval (g.inputs.map fun i => (w0 ++ b :: w1).getD i false)]) := by
      rw [List.append_assoc]
    have ha2 : (w0 ++ b :: w1) ++ [g.op.eval (g.inputs.map fun i => (w0 ++ b :: w1).getD i false)] =
        w0 ++ b :: (w1 ++ [g.op.eval (g.inputs.map fun i => (w0 ++ b :: w1).getD i false)]) := by
      rw [List.append_assoc]
      rfl
    rw [ha1, ha2]
    exact runGates_remap_after w0 b top gs _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) u hu

private lemma list_split_at {α : Type} (l : List α) (j : Fin l.length) :
    l = l.take j.val ++ l.get j :: l.drop (j.val + 1) := by
  calc
    l = l.take j.val ++ l.drop j.val := (List.take_append_drop j.val l).symm
    _ = l.take j.val ++ l[j.val] :: l.drop (j.val + 1) := by
      rw [List.drop_eq_getElem_cons j.isLt]
    _ = l.take j.val ++ l.get j :: l.drop (j.val + 1) := rfl

private lemma dead_gate_contradiction (n : ℕ) (C : Circuit)
    (hmin : IsMinimalCircuit (n + 1) C) (j : Fin C.gates.length)
    (hout : C.output ≠ n + 1 + j.val)
    (hno : ∀ k : Fin C.gates.length, j.val < k.val → ¬ effReads (C.gates.get k) (n + 1 + j.val)) :
    False := by
  let pre := C.gates.take j.val
  let gj := C.gates.get j
  let post := C.gates.drop (j.val + 1)
  have hsplit : C.gates = pre ++ gj :: post := list_split_at C.gates j
  let m := n + 1 + j.val
  let top := n + 1 + C.gates.length
  let C' : Circuit :=
    { gates := (pre ++ post).map (remapGate m top), output := remapWire m top C.output }
  have hfit' : FanInTwo C' := by
    intro g' hg'
    simp only [C', List.mem_map] at hg'
    rcases hg' with ⟨g, hg, rfl⟩
    have hgin : g ∈ C.gates := by
      rw [hsplit]
      rcases List.mem_append.mp hg with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hfg := hmin.1 g hgin
    exact ⟨hfg.1, by simp [remapGate, hfg.2]⟩
  have hpost_no : ∀ g ∈ post, ¬ effReads g m := by
    intro g hg
    rcases List.mem_iff_getElem.mp hg with ⟨r, hr, rfl⟩
    have hr' : j.val + 1 + r < C.gates.length := by
      simp only [post, List.length_drop] at hr
      omega
    have hk := hno ⟨j.val + 1 + r, hr'⟩ (by dsimp; omega)
    have hget : post[r] = C.gates.get ⟨j.val + 1 + r, hr'⟩ := by
      simp [post, List.getElem_drop]
    rw [hget]
    exact hk
  have hfun : circuitFun (n + 1) C' = circuitFun (n + 1) C := by
    funext v
    change C'.eval (List.ofFn v) = C.eval (List.ofFn v)
    unfold Circuit.eval
    change (runGates C'.gates (List.ofFn v)).getD C'.output false =
      (runGates C.gates (List.ofFn v)).getD C.output false
    have hxlen : (List.ofFn v).length = n + 1 := List.length_ofFn
    have hprelen : pre.length = j.val := List.length_take_of_le (Nat.le_of_lt j.isLt)
    simp only [C', List.map_append, runGates_append]
    rw [hsplit, runGates_append, runGates_cons]
    have hbefore : runGates (pre.map (remapGate m top)) (List.ofFn v) =
        runGates pre (List.ofFn v) := by
      apply runGates_remap_before m top (by omega)
      rw [hxlen, hprelen]
    rw [hbefore]
    set w0 := runGates pre (List.ofFn v)
    have hw0 : w0.length = m := by
      rw [runGates_length, hxlen, hprelen]
    have hpost_no' : ∀ g ∈ post, ¬ effReads g w0.length := by
      rw [hw0]
      exact hpost_no
    have h1 := runGates_remap_after w0 (gj.op.eval (gj.inputs.map fun i => w0.getD i false)) top
      post [] hpost_no' C.output (by rw [hw0]; exact hout)
    rw [hw0] at h1
    simpa only [List.append_nil] using h1
  have hle : C.size ≤ C'.size := hmin.2 C' hfit' hfun
  have hsize : C'.size = C.gates.length - 1 := by
    simp only [Circuit.size, C', List.length_map, List.length_append, pre, post,
      List.length_take_of_le (Nat.le_of_lt j.isLt), List.length_drop]
    omega
  have hjlt : j.val < C.gates.length := j.isLt
  simp only [Circuit.size] at hle hsize
  omega

private def evalSym (dw : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr w => dw.getD w false

private def stepGate (n : ℕ) (env : List (Bool ⊕ ℕ)) (dgates : List Gate) (g : Gate) :
    (Bool ⊕ ℕ) × Option Gate :=
  match g.op with
  | GateOp.not =>
    match g.inputs.head? with
    | none => (Sum.inl true, none)
    | some u =>
      match env.getD u (Sum.inl false) with
      | Sum.inl b => (Sum.inl (!b), none)
      | Sum.inr w => (Sum.inr (n + dgates.length), some { op := GateOp.not, inputs := [w] })
  | GateOp.and =>
    match g.inputs.map (fun u => env.getD u (Sum.inl false)) with
    | [] => (Sum.inl true, none)
    | [v] => (v, none)
    | [Sum.inl false, _] => (Sum.inl false, none)
    | [Sum.inl true, v] => (v, none)
    | [Sum.inr _, Sum.inl false] => (Sum.inl false, none)
    | [Sum.inr w1, Sum.inl true] => (Sum.inr w1, none)
    | [Sum.inr w1, Sum.inr w2] =>
      (Sum.inr (n + dgates.length), some { op := GateOp.and, inputs := [w1, w2] })
    | _ => (Sum.inl false, none)
  | GateOp.or =>
    match g.inputs.map (fun u => env.getD u (Sum.inl false)) with
    | [] => (Sum.inl false, none)
    | [v] => (v, none)
    | [Sum.inl true, _] => (Sum.inl true, none)
    | [Sum.inl false, v] => (v, none)
    | [Sum.inr _, Sum.inl true] => (Sum.inl true, none)
    | [Sum.inr w1, Sum.inl false] => (Sum.inr w1, none)
    | [Sum.inr w1, Sum.inr w2] =>
      (Sum.inr (n + dgates.length), some { op := GateOp.or, inputs := [w1, w2] })
    | _ => (Sum.inl false, none)
  | _ => (Sum.inl false, none)

private def runSimp (n : ℕ) :
    List Gate → List (Bool ⊕ ℕ) → List Gate → List (Bool ⊕ ℕ) × List Gate
  | [], env, dgates => (env, dgates)
  | g :: gs, env, dgates =>
    match stepGate n env dgates g with
    | (sym, none) => runSimp n gs (env ++ [sym]) dgates
    | (sym, some g') => runSimp n gs (env ++ [sym]) (dgates ++ [g'])

private lemma runSimp_append (n : ℕ) (gs1 gs2 : List Gate)
    (env : List (Bool ⊕ ℕ)) (dgates : List Gate) :
    runSimp n (gs1 ++ gs2) env dgates =
      runSimp n gs2 (runSimp n gs1 env dgates).1 (runSimp n gs1 env dgates).2 := by
  induction gs1 generalizing env dgates with
  | nil => rfl
  | cons g gs1 ih =>
    simp only [List.cons_append, runSimp]
    cases stepGate n env dgates g with
    | mk sym og =>
      cases og with
      | none => exact ih _ _
      | some g' => exact ih _ _

private lemma runSimp_env_prefix (n : ℕ) (gs : List Gate)
    (env : List (Bool ⊕ ℕ)) (dgates : List Gate) :
    ∃ tail, (runSimp n gs env dgates).1 = env ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing env dgates with
  | nil => exact ⟨[], by simp [runSimp], rfl⟩
  | cons g gs ih =>
    simp only [runSimp]
    cases stepGate n env dgates g with
    | mk sym og =>
      cases og with
      | none =>
        rcases ih (env ++ [sym]) dgates with ⟨tail, h1, h2⟩
        exact ⟨sym :: tail, by simpa [List.append_assoc] using h1, by simp [h2]⟩
      | some g' =>
        rcases ih (env ++ [sym]) (dgates ++ [g']) with ⟨tail, h1, h2⟩
        exact ⟨sym :: tail, by simpa [List.append_assoc] using h1, by simp [h2]⟩

private lemma runSimp_env_getD_lt (n : ℕ) (gs : List Gate)
    (env : List (Bool ⊕ ℕ)) (dgates : List Gate) (i : ℕ) (hi : i < env.length) :
    (runSimp n gs env dgates).1.getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
  rcases runSimp_env_prefix n gs env dgates with ⟨tail, h1, _⟩
  rw [h1]
  exact getD_append_left env tail (Sum.inl false) i hi

private lemma runSimp_dgates_length_le (n : ℕ) (gs : List Gate)
    (env : List (Bool ⊕ ℕ)) (dgates : List Gate) :
    (runSimp n gs env dgates).2.length ≤ dgates.length + gs.length := by
  induction gs generalizing env dgates with
  | nil => simp [runSimp]
  | cons g gs ih =>
    simp only [runSimp]
    cases stepGate n env dgates g with
    | mk sym og =>
      cases og with
      | none =>
        have h := ih (env ++ [sym]) dgates
        simp only [List.length_cons]
        omega
      | some g' =>
        have h := ih (env ++ [sym]) (dgates ++ [g'])
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        omega

private lemma stepGate_fanInTwo (n : ℕ) (env : List (Bool ⊕ ℕ)) (dgates : List Gate)
    (g : Gate) (sym : Bool ⊕ ℕ) (g' : Gate) (h : stepGate n env dgates g = (sym, some g')) :
    g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  unfold stepGate at h
  cases hop : g.op <;> rw [hop] at h
  · dsimp only at h
    cases hm : g.inputs.map (fun u => env.getD u (Sum.inl false)) with
    | nil => rw [hm] at h; cases h
    | cons a l1 =>
      cases l1 with
      | nil => rw [hm] at h; cases h
      | cons b l2 =>
        cases l2 with
        | nil =>
          rw [hm] at h
          cases a with
          | inl ba => cases ba <;> cases h
          | inr wa =>
            cases b with
            | inl bb => cases bb <;> cases h
            | inr wb =>
              cases h
              exact ⟨Or.inl rfl, by simp⟩
        | cons _ _ => rw [hm] at h; cases h
  · dsimp only at h
    cases hm : g.inputs.map (fun u => env.getD u (Sum.inl false)) with
    | nil => rw [hm] at h; cases h
    | cons a l1 =>
      cases l1 with
      | nil => rw [hm] at h; cases h
      | cons b l2 =>
        cases l2 with
        | nil =>
          rw [hm] at h
          cases a with
          | inl ba => cases ba <;> cases h
          | inr wa =>
            cases b with
            | inl bb => cases bb <;> cases h
            | inr wb =>
              cases h
              exact ⟨Or.inr (Or.inl rfl), by simp⟩
        | cons _ _ => rw [hm] at h; cases h
  · dsimp only at h
    cases hh : g.inputs.head? with
    | none => rw [hh] at h; cases h
    | some u =>
      rw [hh] at h
      dsimp only at h
      cases hv : env.getD u (Sum.inl false) with
      | inl b => rw [hv] at h; cases h
      | inr w =>
        rw [hv] at h
        cases h
        exact ⟨Or.inr (Or.inr rfl), by simp⟩
  · cases h
  · cases h

private lemma runSimp_fanInTwo (n : ℕ) (gs : List Gate)
    (env : List (Bool ⊕ ℕ)) (dgates : List Gate)
    (h0 : ∀ g ∈ dgates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ (runSimp n gs env dgates).2,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing env dgates with
  | nil => exact h0
  | cons g gs ih =>
    simp only [runSimp]
    cases h : stepGate n env dgates g with
    | mk sym og =>
      cases og with
      | none => exact ih _ _ h0
      | some g' =>
        apply ih
        intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact h0 x h1
        · simp only [List.mem_singleton] at h2
          rw [h2]
          exact stepGate_fanInTwo n env dgates g sym g' h

private lemma getD_mem_or_default (env : List (Bool ⊕ ℕ)) (u : ℕ) :
    env.getD u (Sum.inl false) ∈ env ∨ env.getD u (Sum.inl false) = Sum.inl false := by
  by_cases h : u < env.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.getElem_mem h
  · right
    exact getD_eq_default_of_le env (Sum.inl false) u (Nat.le_of_not_lt h)

private lemma stepGate_bounds (n : ℕ) (env : List (Bool ⊕ ℕ)) (dgates : List Gate) (g : Gate)
    (hb : ∀ s ∈ env, ∀ w, s = Sum.inr w → w < n + dgates.length) :
    match stepGate n env dgates g with
    | (sym, none) => ∀ w, sym = Sum.inr w → w < n + dgates.length
    | (sym, some _) => ∀ w, sym = Sum.inr w → w < n + (dgates.length + 1) := by
  have hget : ∀ u w, env.getD u (Sum.inl false) = Sum.inr w → w < n + dgates.length := by
    intro u w hu
    rcases getD_mem_or_default env u with hm | hd
    · exact hb _ hm w hu
    · rw [hd] at hu; cases hu
  unfold stepGate
  cases hop : g.op <;> dsimp only
  · cases hm : g.inputs.map (fun u => env.getD u (Sum.inl false)) with
    | nil => intro w hw; cases hw
    | cons a l1 =>
      cases l1 with
      | nil =>
        intro w hw
        have ha : a ∈ g.inputs.map (fun u => env.getD u (Sum.inl false)) := by
          rw [hm]; exact List.mem_cons_self
        rcases List.mem_map.mp ha with ⟨u, _, rfl⟩
        exact hget u w hw
      | cons b l2 =>
        cases l2 with
        | nil =>
          have ha : a ∈ g.inputs.map (fun u => env.getD u (Sum.inl false)) := by
            rw [hm]; exact List.mem_cons_self
          have hb' : b ∈ g.inputs.map (fun u => env.getD u (Sum.inl false)) := by
            rw [hm]; exact List.mem_cons_of_mem _ List.mem_cons_self
          rcases List.mem_map.mp ha with ⟨ua, _, rfl⟩
          rcases List.mem_map.mp hb' with ⟨ub, _, rfl⟩
          cases h1 : env.getD ua (Sum.inl false) with
          | inl ba =>
            cases ba
            · intro w hw; cases hw
            · intro w hw; exact hget ub w hw
          | inr wa =>
            cases h2 : env.getD ub (Sum.inl false) with
            | inl bb =>
              cases bb
              · intro w hw; cases hw
              · intro w hw
                cases hw
                exact hget ua wa h1
            | inr wb =>
              intro w hw
              cases hw
              omega
        | cons _ _ => intro w hw; cases hw
  · cases hm : g.inputs.map (fun u => env.getD u (Sum.inl false)) with
    | nil => intro w hw; cases hw
    | cons a l1 =>
      cases l1 with
      | nil =>
        intro w hw
        have ha : a ∈ g.inputs.map (fun u => env.getD u (Sum.inl false)) := by
          rw [hm]; exact List.mem_cons_self
        rcases List.mem_map.mp ha with ⟨u, _, rfl⟩
        exact hget u w hw
      | cons b l2 =>
        cases l2 with
        | nil =>
          have ha : a ∈ g.inputs.map (fun u => env.getD u (Sum.inl false)) := by
            rw [hm]; exact List.mem_cons_self
          have hb' : b ∈ g.inputs.map (fun u => env.getD u (Sum.inl false)) := by
            rw [hm]; exact List.mem_cons_of_mem _ List.mem_cons_self
          rcases List.mem_map.mp ha with ⟨ua, _, rfl⟩
          rcases List.mem_map.mp hb' with ⟨ub, _, rfl⟩
          cases h1 : env.getD ua (Sum.inl false) with
          | inl ba =>
            cases ba
            · intro w hw; exact hget ub w hw
            · intro w hw; cases hw
          | inr wa =>
            cases h2 : env.getD ub (Sum.inl false) with
            | inl bb =>
              cases bb
              · intro w hw
                cases hw
                exact hget ua wa h1
              · intro w hw; cases hw
            | inr wb =>
              intro w hw
              cases hw
              omega
        | cons _ _ => intro w hw; cases hw
  · cases hh : g.inputs.head? with
    | none => intro w hw; cases hw
    | some u =>
      dsimp only
      cases hv : env.getD u (Sum.inl false) with
      | inl b => intro w hw; cases hw
      | inr w0 => intro w hw; cases hw; omega
  · intro w hw; cases hw
  · intro w hw; cases hw

private lemma stepGate_eval_correct (n : ℕ) (x_n cw : List Bool)
    (env : List (Bool ⊕ ℕ)) (dgates : List Gate) (g : Gate)
    (hxlen : x_n.length = n)
    (hfit : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hinv : ∀ i, cw.getD i false = evalSym (runGates dgates x_n) (env.getD i (Sum.inl false))) :
    let dw := runGates dgates x_n
    let b := g.op.eval (g.inputs.map fun i => cw.getD i false)
    match stepGate n env dgates g with
    | (sym, none) => b = evalSym dw sym
    | (sym, some g') =>
      sym = Sum.inr dw.length ∧
      b = g'.op.eval (g'.inputs.map fun i => dw.getD i false) := by
  dsimp only
  have hdwlen : (runGates dgates x_n).length = n + dgates.length := by
    rw [runGates_length, hxlen]
  rcases hfit with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · unfold stepGate
    rw [hop]
    dsimp only [GateOp.eval]
    cases hi : g.inputs with
    | nil => rfl
    | cons u1 rest1 =>
      cases rest1 with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact hinv u1
      | cons u2 rest2 =>
        cases rest2 with
        | nil =>
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          have hc1 := hinv u1
          have hc2 := hinv u2
          cases h1 : env.getD u1 (Sum.inl false) with
          | inl b1 =>
            rw [h1] at hc1
            cases b1
            · rw [hc1]; rfl
            · rw [hc1, hc2]; rfl
          | inr w1 =>
            rw [h1] at hc1
            cases h2 : env.getD u2 (Sum.inl false) with
            | inl b2 =>
              rw [h2] at hc2
              cases b2
              · rw [hc2]; simp [evalSym]
              · rw [hc1, hc2]; simp [evalSym]
            | inr w2 =>
              rw [h2] at hc2
              refine ⟨by rw [hdwlen], ?_⟩
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true]
              rw [hc1, hc2]
              rfl
        | cons _ _ =>
          simp only [hi, List.length_cons] at hlen
          omega
  · unfold stepGate
    rw [hop]
    dsimp only [GateOp.eval]
    cases hi : g.inputs with
    | nil => rfl
    | cons u1 rest1 =>
      cases rest1 with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact hinv u1
      | cons u2 rest2 =>
        cases rest2 with
        | nil =>
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          have hc1 := hinv u1
          have hc2 := hinv u2
          cases h1 : env.getD u1 (Sum.inl false) with
          | inl b1 =>
            rw [h1] at hc1
            cases b1
            · rw [hc1, hc2]; rfl
            · rw [hc1]; rfl
          | inr w1 =>
            rw [h1] at hc1
            cases h2 : env.getD u2 (Sum.inl false) with
            | inl b2 =>
              rw [h2] at hc2
              cases b2
              · rw [hc1, hc2]; simp [evalSym]
              · rw [hc2]; simp [evalSym]
            | inr w2 =>
              rw [h2] at hc2
              refine ⟨by rw [hdwlen], ?_⟩
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false]
              rw [hc1, hc2]
              rfl
        | cons _ _ =>
          simp only [hi, List.length_cons] at hlen
          omega
  · unfold stepGate
    rw [hop]
    dsimp only [GateOp.eval]
    cases hi : g.inputs with
    | nil => rfl
    | cons u1 rest1 =>
      simp only [List.head?_cons, List.map_cons, List.headD_cons]
      have hc1 := hinv u1
      cases h1 : env.getD u1 (Sum.inl false) with
      | inl b1 =>
        rw [h1] at hc1
        rw [hc1]
        rfl
      | inr w1 =>
        rw [h1] at hc1
        refine ⟨by rw [hdwlen], ?_⟩
        simp only [List.map_cons, List.map_nil, List.headD_cons]
        rw [hc1]
        rfl

private lemma runSimp_correct (n : ℕ) (x_n : List Bool) (hxlen : x_n.length = n) :
    ∀ (gs : List Gate) (cw : List Bool) (env : List (Bool ⊕ ℕ)) (dgates : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      cw.length = env.length →
      (∀ s ∈ env, ∀ w, s = Sum.inr w → w < n + dgates.length) →
      (∀ i, cw.getD i false = evalSym (runGates dgates x_n) (env.getD i (Sum.inl false))) →
      ∀ i, (runGates gs cw).getD i false =
        evalSym (runGates (runSimp n gs env dgates).2 x_n)
          ((runSimp n gs env dgates).1.getD i (Sum.inl false))
  | [], cw, env, dgates, _, _, _, hinv, i => hinv i
  | g :: gs, cw, env, dgates, hfit, hlen, hb, hinv, i => by
    simp only [runGates_cons, runSimp]
    have hgfit := hfit g List.mem_cons_self
    have hgsfit : ∀ g' ∈ gs,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg')
    have hstep := stepGate_eval_correct n x_n cw env dgates g hxlen hgfit hinv
    have hstepb := stepGate_bounds n env dgates g hb
    cases hs : stepGate n env dgates g with
    | mk sym og =>
      rw [hs] at hstep hstepb
      cases og with
      | none =>
        dsimp only at hstep hstepb
        apply runSimp_correct n x_n hxlen gs _ (env ++ [sym]) dgates hgsfit
        · simp [hlen]
        · intro s hs' w hw
          rcases List.mem_append.mp hs' with h1 | h2
          · exact hb s h1 w hw
          · simp only [List.mem_singleton] at h2
            rw [h2] at hw
            exact hstepb w hw
        · intro k
          by_cases hk : k < cw.length
          · have hk' : k < env.length := by omega
            rw [getD_append_left cw _ false k hk,
              getD_append_left env [sym] (Sum.inl false) k hk', hinv k]
          · by_cases heq : k = cw.length
            · subst heq
              rw [getD_append_right cw _ false cw.length (Nat.le_refl _), Nat.sub_self]
              rw [getD_append_right env [sym] (Sum.inl false) cw.length (by omega), hlen,
                Nat.sub_self]
              exact hstep
            · have hgt : (cw ++ [g.op.eval (g.inputs.map fun j => cw.getD j false)]).length ≤ k := by
                simp; omega
              have hgt' : (env ++ [sym]).length ≤ k := by
                simp; omega
              rw [getD_eq_default_of_le _ false k hgt,
                getD_eq_default_of_le _ (Sum.inl false) k hgt']
              rfl
      | some g' =>
        dsimp only at hstep hstepb
        rcases hstep with ⟨hsym, hbeval⟩
        apply runSimp_correct n x_n hxlen gs _ (env ++ [sym]) (dgates ++ [g']) hgsfit
        · simp [hlen]
        · intro s hs' w hw
          rcases List.mem_append.mp hs' with h1 | h2
          · have := hb s h1 w hw
            simp only [List.length_append, List.length_singleton]
            omega
          · simp only [List.mem_singleton] at h2
            rw [h2] at hw
            have := hstepb w hw
            simp only [List.length_append, List.length_singleton]
            omega
        · intro k
          set dw := runGates dgates x_n
          have hdwlen : dw.length = n + dgates.length := by
            rw [runGates_length, hxlen]
          have hdw' : runGates (dgates ++ [g']) x_n =
              dw ++ [g'.op.eval (g'.inputs.map fun j => dw.getD j false)] := by
            rw [runGates_append, runGates_cons, runGates_nil]
          rw [hdw']
          by_cases hk : k < cw.length
          · have hk' : k < env.length := by omega
            rw [getD_append_left cw _ false k hk,
              getD_append_left env [sym] (Sum.inl false) k hk', hinv k]
            have hmem : env.getD k (Sum.inl false) ∈ env := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
              exact List.getElem_mem hk'
            cases hval : env.getD k (Sum.inl false) with
            | inl c => rfl
            | inr w =>
              have hwlt : w < dw.length := by
                rw [hdwlen]
                exact hb _ hmem w hval
              simp only [evalSym]
              rw [getD_append_left dw _ false w hwlt]
          · by_cases heq : k = cw.length
            · subst heq
              rw [getD_append_right cw _ false cw.length (Nat.le_refl _), Nat.sub_self]
              rw [getD_append_right env [sym] (Sum.inl false) cw.length (by omega), hlen,
                Nat.sub_self, hsym]
              simp only [List.getD_cons_zero, evalSym]
              rw [getD_append_right dw _ false dw.length (Nat.le_refl _), Nat.sub_self]
              exact hbeval
            · have hgt : (cw ++ [g.op.eval (g.inputs.map fun j => cw.getD j false)]).length ≤ k := by
                simp; omega
              have hgt' : (env ++ [sym]).length ≤ k := by
                simp; omega
              rw [getD_eq_default_of_le _ false k hgt,
                getD_eq_default_of_le _ (Sum.inl false) k hgt']
              rfl

private def initEnv (n : ℕ) : List (Bool ⊕ ℕ) :=
  (List.range n).map Sum.inr ++ [Sum.inl true]

private lemma initEnv_length (n : ℕ) : (initEnv n).length = n + 1 := by
  simp [initEnv]

private lemma initEnv_bounds (n : ℕ) :
    ∀ s ∈ initEnv n, ∀ w, s = Sum.inr w → w < n + ([] : List Gate).length := by
  intro s hs w hw
  simp only [initEnv, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hs
  rcases hs with ⟨u, hu, rfl⟩ | rfl
  · cases hw
    simpa using hu
  · cases hw

private lemma initEnv_getD_n (n : ℕ) : (initEnv n).getD n (Sum.inl false) = Sum.inl true := by
  unfold initEnv
  rw [getD_append_right ((List.range n).map Sum.inr) [Sum.inl true] (Sum.inl false) n (by simp)]
  simp

private lemma initEnv_correct (n : ℕ) (y : Fin n → Bool) (i : ℕ) :
    (List.ofFn (Fin.snoc y true)).getD i false =
      evalSym (runGates [] (List.ofFn y)) ((initEnv n).getD i (Sum.inl false)) := by
  rw [runGates_nil]
  by_cases hi : i < n
  · have h1 : (List.ofFn (Fin.snoc y true)).getD i false = y ⟨i, hi⟩ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      have hi' : i < n + 1 := by omega
      simp only [dite_eq_left, hi', Option.getD_some]
      have hcast : (⟨i, hi'⟩ : Fin (n + 1)) = (⟨i, hi⟩ : Fin n).castSucc := rfl
      rw [hcast]
      exact Fin.snoc_castSucc (α := fun _ => Bool) true y ⟨i, hi⟩
    have h2 : (initEnv n).getD i (Sum.inl false) = Sum.inr i := by
      unfold initEnv
      rw [getD_append_left ((List.range n).map Sum.inr) [Sum.inl true] (Sum.inl false) i
        (by simp [hi])]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rfl
    have h3 : (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [dite_eq_left, hi, Option.getD_some]
    rw [h1, h2]
    exact h3.symm
  · by_cases heq : i = n
    · rw [heq]
      have h1 : (List.ofFn (Fin.snoc y true)).getD n false = true := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        have hn : n < n + 1 := Nat.lt_succ_self n
        simp only [dite_eq_left, hn, Option.getD_some]
        exact Fin.snoc_last (α := fun _ => Bool) true y
      rw [h1, initEnv_getD_n]
      rfl
    · have hgt1 : (List.ofFn (Fin.snoc y true)).length ≤ i := by
        rw [List.length_ofFn]; omega
      have hgt2 : (initEnv n).length ≤ i := by
        rw [initEnv_length]; omega
      rw [getD_eq_default_of_le _ false i hgt1,
        getD_eq_default_of_le _ (Sum.inl false) i hgt2]
      rfl

private lemma stepGate_const_elim (n : ℕ) (env : List (Bool ⊕ ℕ)) (dgates : List Gate)
    (g : Gate) (u : ℕ) (b : Bool)
    (hfit : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hread : effReads g u)
    (hu : env.getD u (Sum.inl false) = Sum.inl b) :
    (stepGate n env dgates g).2 = none := by
  rcases hfit with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · have hmem : u ∈ g.inputs := by
      rcases hread with ⟨h, _⟩ | ⟨_, h⟩
      · rw [hop] at h; cases h
      · exact h
    unfold stepGate
    rw [hop]
    dsimp only
    cases hi : g.inputs with
    | nil => simp [hi] at hmem
    | cons a l1 =>
      cases l1 with
      | nil => rfl
      | cons c l2 =>
        cases l2 with
        | nil =>
          simp only [hi, List.mem_cons, List.not_mem_nil, or_false] at hmem
          simp only [List.map_cons, List.map_nil]
          rcases hmem with rfl | rfl
          · rw [hu]
            cases b <;> rfl
          · rw [hu]
            cases env.getD a (Sum.inl false) with
            | inl ba => cases ba <;> rfl
            | inr wa => cases b <;> rfl
        | cons _ _ =>
          simp only [hi, List.length_cons] at hlen
          omega
  · have hmem : u ∈ g.inputs := by
      rcases hread with ⟨h, _⟩ | ⟨_, h⟩
      · rw [hop] at h; cases h
      · exact h
    unfold stepGate
    rw [hop]
    dsimp only
    cases hi : g.inputs with
    | nil => simp [hi] at hmem
    | cons a l1 =>
      cases l1 with
      | nil => rfl
      | cons c l2 =>
        cases l2 with
        | nil =>
          simp only [hi, List.mem_cons, List.not_mem_nil, or_false] at hmem
          simp only [List.map_cons, List.map_nil]
          rcases hmem with rfl | rfl
          · rw [hu]
            cases b <;> rfl
          · rw [hu]
            cases env.getD a (Sum.inl false) with
            | inl ba => cases ba <;> rfl
            | inr wa => cases b <;> rfl
        | cons _ _ =>
          simp only [hi, List.length_cons] at hlen
          omega
  · have hhd : g.inputs.head? = some u := by
      rcases hread with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd hop h
    unfold stepGate
    rw [hop]
    dsimp only
    rw [hhd]
    dsimp only
    rw [hu]

private lemma stepGate_bad_reader (n : ℕ) (env : List (Bool ⊕ ℕ)) (dgates : List Gate) (g : Gate)
    (hfit : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hread : effReads g n)
    (hn : env.getD n (Sum.inl false) = Sum.inl true)
    (hbad : ¬ (g.op = GateOp.and ∧ g.inputs.length = 2 ∧ n ∈ g.inputs ∧
      ∃ w ∈ g.inputs, w ≠ n ∧ w < env.length)) :
    ∃ b : Bool, stepGate n env dgates g = (Sum.inl b, none) := by
  rcases hfit with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · have hmem : n ∈ g.inputs := by
      rcases hread with ⟨h, _⟩ | ⟨_, h⟩
      · rw [hop] at h; cases h
      · exact h
    unfold stepGate
    rw [hop]
    dsimp only
    cases hi : g.inputs with
    | nil => simp [hi] at hmem
    | cons a l1 =>
      cases l1 with
      | nil =>
        simp only [hi, List.mem_singleton] at hmem
        subst hmem
        simp only [List.map_cons, List.map_nil]
        rw [hn]
        exact ⟨true, rfl⟩
      | cons c l2 =>
        cases l2 with
        | nil =>
          simp only [hi, List.mem_cons, List.not_mem_nil, or_false] at hmem
          simp only [List.map_cons, List.map_nil]
          rcases hmem with rfl | rfl
          · by_cases hcn : c = n
            · subst hcn
              rw [hn]
              exact ⟨true, rfl⟩
            · have hge : env.length ≤ c := by
                by_contra hlt
                push Not at hlt
                apply hbad
                refine ⟨hop, by simp [hi], by simp [hi], c, by simp [hi], hcn, hlt⟩
              have hc : env.getD c (Sum.inl false) = Sum.inl false :=
                getD_eq_default_of_le env (Sum.inl false) c hge
              rw [hn, hc]
              exact ⟨false, rfl⟩
          · by_cases han : a = n
            · subst han
              rw [hn]
              exact ⟨true, rfl⟩
            · have hge : env.length ≤ a := by
                by_contra hlt
                push Not at hlt
                apply hbad
                refine ⟨hop, by simp [hi], by simp [hi], a, by simp [hi], han, hlt⟩
              have ha : env.getD a (Sum.inl false) = Sum.inl false :=
                getD_eq_default_of_le env (Sum.inl false) a hge
              rw [hn, ha]
              exact ⟨false, rfl⟩
        | cons _ _ =>
          simp only [hi, List.length_cons] at hlen
          omega
  · have hmem : n ∈ g.inputs := by
      rcases hread with ⟨h, _⟩ | ⟨_, h⟩
      · rw [hop] at h; cases h
      · exact h
    unfold stepGate
    rw [hop]
    dsimp only
    cases hi : g.inputs with
    | nil => simp [hi] at hmem
    | cons a l1 =>
      cases l1 with
      | nil =>
        simp only [hi, List.mem_singleton] at hmem
        subst hmem
        simp only [List.map_cons, List.map_nil]
        rw [hn]
        exact ⟨true, rfl⟩
      | cons c l2 =>
        cases l2 with
        | nil =>
          simp only [hi, List.mem_cons, List.not_mem_nil, or_false] at hmem
          simp only [List.map_cons, List.map_nil]
          rcases hmem with rfl | rfl
          · rw [hn]
            exact ⟨true, rfl⟩
          · rw [hn]
            cases env.getD a (Sum.inl false) with
            | inl ba => cases ba <;> exact ⟨true, rfl⟩
            | inr wa => exact ⟨true, rfl⟩
        | cons _ _ =>
          simp only [hi, List.length_cons] at hlen
          omega
  · have hhd : g.inputs.head? = some n := by
      rcases hread with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd hop h
    unfold stepGate
    rw [hop]
    dsimp only
    rw [hhd]
    dsimp only
    rw [hn]
    exact ⟨false, rfl⟩

end PEqualNP.Outside.L_meta_171_aux

open PEqualNP.Outside.L_meta_171_aux in
theorem PEqualNP.Outside.L_meta_171 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' true)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) s → C.size ≤ s + 1) → ∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.gates.get j).inputs.length = 2 ∧ n ∈ (C.gates.get j).inputs ∧ ∃ w ∈ (C.gates.get j).inputs, w ≠ n ∧ w < n + 1 + j.val := by
  intro n C hmin _ hnc hlift j hread
  by_contra hbad
  set res := runSimp n C.gates (initEnv n) []
  have hcorr : ∀ (y : Fin n → Bool) (i : ℕ),
      (C.wires (List.ofFn (Fin.snoc y true))).getD i false =
        evalSym (runGates res.2 (List.ofFn y)) (res.1.getD i (Sum.inl false)) := by
    intro y i
    exact runSimp_correct n (List.ofFn y) List.length_ofFn C.gates
      (List.ofFn (Fin.snoc y true)) (initEnv n) [] hmin.1
      (by rw [List.length_ofFn, initEnv_length])
      (initEnv_bounds n)
      (initEnv_correct n y) i
  have hout_inr : ∃ outW : ℕ, res.1.getD C.output (Sum.inl false) = Sum.inr outW := by
    cases h : res.1.getD C.output (Sum.inl false) with
    | inl b =>
      exfalso
      rcases hnc with ⟨y, y', hne⟩
      apply hne
      change (C.wires (List.ofFn (Fin.snoc y true))).getD C.output false =
        (C.wires (List.ofFn (Fin.snoc y' true))).getD C.output false
      rw [hcorr y C.output, hcorr y' C.output, h]
      rfl
    | inr outW => exact ⟨outW, rfl⟩
  rcases hout_inr with ⟨outW, houtW⟩
  have hD_size : C.size ≤ res.2.length + 1 := by
    apply hlift res.2.length
    refine ⟨{ gates := res.2, output := outW }, ?_, le_rfl, ?_⟩
    · exact runSimp_fanInTwo n C.gates (initEnv n) [] (by simp)
    · intro y
      change (runGates res.2 (List.ofFn y)).getD outW false =
        (C.wires (List.ofFn (Fin.snoc y true))).getD C.output false
      rw [hcorr y C.output, houtW]
      rfl
  let pre := C.gates.take j.val
  let gj := C.gates.get j
  let rest := C.gates.drop (j.val + 1)
  have hsplit1 : C.gates = pre ++ gj :: rest := list_split_at C.gates j
  have hprelen : pre.length = j.val := List.length_take_of_le (Nat.le_of_lt j.isLt)
  set r1 := runSimp n pre (initEnv n) []
  have hr1_env_len : r1.1.length = n + 1 + j.val := by
    rcases runSimp_env_prefix n pre (initEnv n) [] with ⟨t, ht, htl⟩
    rw [ht, List.length_append, initEnv_length, htl, hprelen]
  have hr1_n : r1.1.getD n (Sum.inl false) = Sum.inl true := by
    rw [runSimp_env_getD_lt n pre (initEnv n) [] n (by rw [initEnv_length]; omega)]
    exact initEnv_getD_n n
  have hgj_fit : gj.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      gj.inputs.length ≤ 2 := hmin.1 gj (List.get_mem C.gates j)
  have hstep1 : ∃ b : Bool, stepGate n r1.1 r1.2 gj = (Sum.inl b, none) := by
    apply stepGate_bad_reader n r1.1 r1.2 gj hgj_fit hread hr1_n
    rw [hr1_env_len]
    exact hbad
  rcases hstep1 with ⟨bj, hbj⟩
  have hres_eq1 : res = runSimp n rest (r1.1 ++ [Sum.inl bj]) r1.2 := by
    show runSimp n C.gates (initEnv n) [] = _
    rw [hsplit1, runSimp_append]
    change runSimp n (gj :: rest) r1.1 r1.2 = _
    simp only [runSimp, hbj]
  have hres_j : res.1.getD (n + 1 + j.val) (Sum.inl false) = Sum.inl bj := by
    rw [hres_eq1]
    have hlt : n + 1 + j.val < (r1.1 ++ [Sum.inl bj]).length := by
      simp [hr1_env_len]
    rw [runSimp_env_getD_lt n rest (r1.1 ++ [Sum.inl bj]) r1.2 (n + 1 + j.val) hlt]
    rw [getD_append_right r1.1 [Sum.inl bj] (Sum.inl false) (n + 1 + j.val) (by rw [hr1_env_len])]
    simp [hr1_env_len]
  have hout_ne : C.output ≠ n + 1 + j.val := by
    intro heq
    rw [heq, hres_j] at houtW
    cases houtW
  have hex_k : ∃ k : Fin C.gates.length, j.val < k.val ∧ effReads (C.gates.get k) (n + 1 + j.val) := by
    by_contra hno
    push Not at hno
    exact dead_gate_contradiction n C hmin j hout_ne hno
  rcases hex_k with ⟨k, hjk, hkread⟩
  have hrlt : k.val - (j.val + 1) < rest.length := by
    simp only [rest, List.length_drop]
    omega
  let rfin : Fin rest.length := ⟨k.val - (j.val + 1), hrlt⟩
  let mid := rest.take rfin.val
  let gk := rest.get rfin
  let post := rest.drop (rfin.val + 1)
  have hsplit2 : rest = mid ++ gk :: post := list_split_at rest rfin
  have hgk_eq : gk = C.gates.get k := by
    change rest[k.val - (j.val + 1)] = C.gates[k.val]
    simp only [rest, List.getElem_drop]
    congr 1
    omega
  set env2 := r1.1 ++ [Sum.inl bj]
  set r2 := runSimp n mid env2 r1.2
  have hr2_j : r2.1.getD (n + 1 + j.val) (Sum.inl false) = Sum.inl bj := by
    have hlt : n + 1 + j.val < env2.length := by
      simp [env2, hr1_env_len]
    rw [runSimp_env_getD_lt n mid env2 r1.2 (n + 1 + j.val) hlt]
    rw [getD_append_right r1.1 [Sum.inl bj] (Sum.inl false) (n + 1 + j.val) (by rw [hr1_env_len])]
    simp [hr1_env_len]
  have hgk_fit : gk.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      gk.inputs.length ≤ 2 := by
    rw [hgk_eq]
    exact hmin.1 (C.gates.get k) (List.get_mem C.gates k)
  have hstep2 : (stepGate n r2.1 r2.2 gk).2 = none :=
    stepGate_const_elim n r2.1 r2.2 gk (n + 1 + j.val) bj hgk_fit (hgk_eq ▸ hkread) hr2_j
  have hres_eq2 : res = runSimp n post (r2.1 ++ [(stepGate n r2.1 r2.2 gk).1]) r2.2 := by
    rw [hres_eq1, hsplit2, runSimp_append]
    change runSimp n (gk :: post) r2.1 r2.2 = _
    simp only [runSimp]
    cases hs : stepGate n r2.1 r2.2 gk with
    | mk sym og =>
      rw [hs] at hstep2
      dsimp only at hstep2
      subst hstep2
      rfl
  have hlen1 : r1.2.length ≤ pre.length := by
    simpa using runSimp_dgates_length_le n pre (initEnv n) []
  have hlen2 : r2.2.length ≤ r1.2.length + mid.length :=
    runSimp_dgates_length_le n mid env2 r1.2
  have hlen3 : res.2.length ≤ r2.2.length + post.length := by
    rw [hres_eq2]
    exact runSimp_dgates_length_le n post (r2.1 ++ [(stepGate n r2.1 r2.2 gk).1]) r2.2
  have hCsize : C.size = pre.length + mid.length + post.length + 2 := by
    have h1 : C.gates.length = pre.length + (rest.length + 1) := by
      have := congrArg List.length hsplit1
      simp only [List.length_append, List.length_cons] at this
      omega
    have h2 : rest.length = mid.length + (post.length + 1) := by
      have := congrArg List.length hsplit2
      simp only [List.length_append, List.length_cons] at this
      omega
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  omega
