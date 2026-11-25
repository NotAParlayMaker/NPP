import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15291_aux.Signed

open scoped BigOperators

/-- A wire and a zero-cost inverter bit. -/
structure Ref where
  ix : Nat
  inverted : Bool := false
  deriving DecidableEq

def Ref.read (r : Ref) (ws : List Bool) : Bool := (ws.getD r.ix false) ^^ r.inverted

/-- The normalized signed graph explicitly counts binary operations only. -/
structure Gate where
  andGate : Bool
  left : Ref
  right : Ref
  deriving DecidableEq

def Gate.eval (g : Gate) (ws : List Bool) : Bool :=
  if g.andGate then g.left.read ws && g.right.read ws
  else g.left.read ws || g.right.read ws

def Gate.pins (g : Gate) : List Nat := [g.left.ix, g.right.ix]

def wires (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.eval ws]) inp

def run (gs : List Gate) (negative : Bool) (inp : List Bool) : Bool :=
  ((wires gs inp).getD (inp.length + gs.length - 1) false) ^^ negative

def uses (gs : List Gate) : List Nat := gs.flatMap Gate.pins

def Fanout (gs : List Gate) (r : Nat) : Nat := (uses gs).count r

/-- After dead-node removal the last gate is output. Every earlier source occurs
at least once, and no pin can point to the last output. The first condition
also rules out future references and duplicate sources. -/
structure LiveBinary (n : Nat) (gs : List Gate) : Prop where
  nonempty : gs ≠ []
  forward : ∀ i (hi : i < gs.length),
    (gs[i]'hi).left.ix < n + i ∧ (gs[i]'hi).right.ix < n + i ∧
      (gs[i]'hi).left.ix ≠ (gs[i]'hi).right.ix
  bounded : ∀ r ∈ uses gs, r < n + gs.length - 1
  live : ∀ r < n + gs.length - 1, r ∈ uses gs

@[simp] theorem uses_length (gs : List Gate) : (uses gs).length = 2 * gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change (g.left.ix :: g.right.ix :: uses gs).length = _
    simp only [List.length_cons, ih]
    omega

private theorem fanout_pos {n : Nat} {gs : List Gate} (h : LiveBinary n gs)
    (i : Nat) (hi : i < n + gs.length - 1) : 1 ≤ Fanout gs i :=
  Nat.succ_le_iff.mpr (List.count_pos_iff.mpr (h.live i hi))

private def EqExcept (a : Nat) (x y : List Bool) : Prop :=
  ∀ i, i ≠ a → x.getD i false = y.getD i false

private theorem append_same {a : Nat} {x y : List Bool} (h : EqExcept a x y)
    (hxy : x.length = y.length) (t : Bool) : EqExcept a (x ++ [t]) (y ++ [t]) := by
  intro i hi
  by_cases hx : i < x.length
  · rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega : x.length ≤ i),
        List.getD_append_right _ _ _ _ (by omega : y.length ≤ i), hxy]

private theorem eval_not_using {g : Gate} {a : Nat} {x y : List Bool}
    (h : EqExcept a x y) (hl : g.left.ix ≠ a) (hr : g.right.ix ≠ a) :
    g.eval x = g.eval y := by
  simp only [Gate.eval, Ref.read, h _ hl, h _ hr]

private theorem tail_preserve (gs : List Gate) {a : Nat} {x y : List Bool}
    (hne : a ∉ uses gs) (h : EqExcept a x y) (hxy : x.length = y.length) :
    EqExcept a (wires gs x) (wires gs y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    change a ∉ g.left.ix :: g.right.ix :: uses gs at hne
    have hL : g.left.ix ≠ a := fun e => hne (by simp [e])
    have hR : g.right.ix ≠ a := fun e => hne (by simp [e])
    have ht : a ∉ uses gs := fun he => hne (by simp [he])
    have he := eval_not_using h hL hR
    change EqExcept a (wires gs (x ++ [g.eval x])) (wires gs (y ++ [g.eval y]))
    rw [he]
    exact ih ht (append_same h hxy _) (by simp [hxy])

end PEqualNP.Outside.L_meta_15291_aux.Signed

namespace PEqualNP.Outside.L_meta_15291_aux.Signed

/-- A replacement wire after assigning selected inputs: either a constant, or a
signed copy of an earlier compacted wire. -/
inductive Alias where
  | constant (value : Bool)
  | wire (ref : Ref)
  deriving DecidableEq

def Alias.eval (a : Alias) (ws : List Bool) : Bool :=
  match a with
  | .constant b => b
  | .wire r => r.read ws

def Alias.flip (a : Alias) (flip : Bool) : Alias :=
  match a with
  | .constant b => .constant (b ^^ flip)
  | .wire r => .wire ⟨r.ix, r.inverted ^^ flip⟩

@[simp] theorem Alias.eval_flip (a : Alias) (flip : Bool) (ws : List Bool) :
    (a.flip flip).eval ws = (a.eval ws ^^ flip) := by
  cases a with
  | constant b => rfl
  | wire r =>
    simp only [Alias.flip, Alias.eval, Ref.read]
    exact (Bool.xor_assoc _ _ _).symm

private def join (isAnd : Bool) (a b : Bool) : Bool :=
  if isAnd then a && b else a || b

/-- One local compaction instruction. A binary gate with a constant input
emits no gate; a local copy is returned as a signed-wire alias. -/
def simplify (isAnd : Bool) : Alias → Alias → Sum Alias Gate
  | .constant a, b =>
    if a = !isAnd then .inl (.constant a) else .inl b
  | a, .constant b =>
    if b = !isAnd then .inl (.constant b) else .inl a
  | .wire a, .wire b =>
    if a.ix = b.ix then
      if a.inverted = b.inverted then .inl (.wire a) else .inl (.constant (!isAnd))
    else .inr ⟨isAnd, a, b⟩

def instValue (cmd : Sum Alias Gate) (ws : List Bool) : Bool :=
  match cmd with
  | .inl a => a.eval ws
  | .inr g => g.eval ws

theorem simplify_correct (isAnd : Bool) (a b : Alias) (ws : List Bool) :
    instValue (simplify isAnd a b) ws = join isAnd (a.eval ws) (b.eval ws) := by
  cases a with
  | constant u =>
    cases u <;> cases isAnd <;> simp [simplify, instValue, Alias.eval, join]
  | wire r =>
    cases b with
    | constant v =>
      cases v <;> cases isAnd <;> simp [simplify, instValue, Alias.eval, join]
    | wire q =>
      by_cases hi : r.ix = q.ix
      · rw [simplify,ite_eq_left hi]
        by_cases hs : r.inverted = q.inverted
        · rw [ite_eq_left hs]
          simp only [instValue,Alias.eval,Ref.read,hi,hs]
          cases isAnd <;> simp [join]
        · rw [ite_eq_right hs]
          simp only [instValue,Alias.eval,Ref.read,hi]
          generalize ws.getD q.ix false = z
          cases hr : r.inverted <;> cases hq : q.inverted <;>
            simp only [hr,hq] at hs ⊢ <;>
            cases z <;> cases isAnd <;> (first | contradiction | rfl)
      · rw [simplify,ite_eq_right hi]
        rfl

def Alias.readIn (r : Ref) (env : List Alias) : Alias :=
  (env.getD r.ix (.constant false)).flip r.inverted

def compactGate (g : Gate) (env : List Alias) : Sum Alias Gate :=
  simplify g.andGate (Alias.readIn g.left env) (Alias.readIn g.right env)

def emits (cmd : Sum Alias Gate) : Nat :=
  match cmd with
  | .inl _ => 0
  | .inr _ => 1

theorem compactGate_le_one (g : Gate) (env : List Alias) :
    emits (compactGate g env) ≤ 1 := by
  cases compactGate g env <;> simp [emits]

theorem compactGate_drops_fixed (g : Gate) (env : List Alias) (i : Nat) (b : Bool)
    (hpin : i ∈ g.pins) (hfix : env.getD i (.constant false) = .constant b) :
    emits (compactGate g env) = 0 := by
  have hh (r : Ref) (eq : r.ix = i) :
      Alias.readIn r env = .constant (b ^^ r.inverted) := by
    rw [Alias.readIn, eq, hfix]
    rfl
  simp [Gate.pins] at hpin
  rcases hpin with h | h
  · rw [compactGate, hh _ h.symm]
    generalize (b ^^ g.left.inverted) = z
    generalize g.andGate = op
    cases z <;> cases op <;> rfl
  · rw [compactGate, hh _ h.symm]
    generalize (b ^^ g.right.inverted) = z
    generalize g.andGate = op
    generalize Alias.readIn g.left env = a
    cases a with
    | constant v => cases v <;> cases z <;> cases op <;> rfl
    | wire q => cases z <;> cases op <;> rfl

/-- A coherent alias environment represents all old values, including the
default value on out-of-range addresses. -/
def Coherent (old : List Bool) (env : List Alias) (ws : List Bool) : Prop :=
  env.length = old.length ∧
    ∀ j, (env.getD j (.constant false)).eval ws = old.getD j false

theorem compactGate_eval (g : Gate) {old : List Bool} {env : List Alias} {ws : List Bool}
    (coh : Coherent old env ws) :
    instValue (compactGate g env) ws = g.eval old := by
  rcases coh with ⟨_, hc⟩
  rw [compactGate, simplify_correct]
  simp only [Alias.readIn, Alias.eval_flip, hc, join, Gate.eval, Ref.read]

/-- Gate-measure inequality for the emitted instruction when an input is fixed. -/
theorem compactGate_emits_le_unread (g : Gate) (env : List Alias) (i : Nat) (b : Bool)
    (hfix : env.getD i (.constant false) = .constant b) :
    emits (compactGate g env) ≤ (if i ∈ g.pins then 0 else 1) := by
  split
  next hpin => rw [compactGate_drops_fixed g env i b hpin hfix]
  next _ => exact compactGate_le_one g env


def Alias.bounded (m : Nat) : Alias → Prop
  | .constant _ => True
  | .wire r => r.ix < m

def EnvBound (m : Nat) (env : List Alias) : Prop :=
  ∀ j, (env.getD j (.constant false)).bounded m

private theorem bound_mono {a : Alias} {lo hi : Nat} (hle : lo ≤ hi)
    (ha : a.bounded lo) : a.bounded hi := by
  cases a <;> simp_all [Alias.bounded]
  omega

private theorem bounded_pin (r : Ref) {m : Nat} {env : List Alias}
    (hb : EnvBound m env) : (Alias.readIn r env).bounded m := by
  specialize hb r.ix
  unfold Alias.readIn
  generalize ev : env.getD r.ix (.constant false) = a at *
  cases a with
  | constant b => trivial
  | wire q => exact hb

private theorem bounded_simplify (m : Nat) (op : Bool) (a b : Alias)
    (ha : a.bounded m) (hb : b.bounded m) :
    match simplify op a b with
    | .inl c => c.bounded m
    | .inr g => g.left.ix < m ∧ g.right.ix < m := by
  cases a with
  | constant u =>
    cases u <;> cases op <;> trivial
  | wire r =>
    cases b with
    | constant v =>
      cases v <;> cases op <;> trivial
    | wire q =>
      by_cases hi : r.ix = q.ix
      · rw [simplify,ite_eq_left hi]
        by_cases hs : r.inverted = q.inverted
        · rw [ite_eq_left hs]
          exact ha
        · rw [ite_eq_right hs]
          trivial
      · rw [simplify,ite_eq_right hi]
        exact ⟨ha,hb⟩

private theorem bounded_command (g : Gate) {m : Nat} {env : List Alias}
    (h : EnvBound m env) :
    match compactGate g env with
    | .inl c => c.bounded m
    | .inr k => k.left.ix < m ∧ k.right.ix < m :=
  bounded_simplify m _ _ _ (bounded_pin g.left h) (bounded_pin g.right h)

theorem emitted_distinct (op : Bool) (a b : Alias) (g : Gate)
    (h : simplify op a b = .inr g) : g.left.ix ≠ g.right.ix := by
  cases a with
  | constant u =>
    cases u <;> cases op <;> simp [simplify] at h
  | wire r =>
    cases b with
    | constant v =>
      cases v <;> cases op <;> simp [simplify] at h
    | wire q =>
      by_cases hi : r.ix = q.ix
      · rw [simplify,ite_eq_left hi] at h
        split at h <;> simp at h
      · rw [simplify,ite_eq_right hi] at h
        injection h with h'
        cases h'
        exact hi

def instruction (cmd : Sum Alias Gate) : List Gate :=
  match cmd with
  | .inl _ => []
  | .inr g => [g]

def chosen (cmd : Sum Alias Gate) (m : Nat) : Alias :=
  match cmd with
  | .inl a => a
  | .inr _ => .wire ⟨m,false⟩

@[simp] theorem instruction_length (cmd : Sum Alias Gate) :
    (instruction cmd).length = emits cmd := by cases cmd <;> rfl

@[simp] theorem wires_length (gs : List Gate) (inp : List Bool) :
    (wires gs inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp [wires]
  | cons g gs ih =>
    change (wires gs (inp ++ [g.eval inp])).length = _
    rw [ih]
    simp
    omega

theorem wires_concat (a b : List Gate) (inp : List Bool) :
    wires (a ++ b) inp = wires b (wires a inp) := by simp [wires, List.foldl_append]

private theorem alias_preserve (cmd : Sum Alias Gate) (ws : List Bool) (a : Alias)
    (hb : a.bounded ws.length) :
    a.eval (wires (instruction cmd) ws) = a.eval ws := by
  cases cmd with
  | inl a' => rfl
  | inr g =>
    cases a with
    | constant t => rfl
    | wire r =>
      change r.ix < ws.length at hb
      change ((ws ++ [g.eval ws]).getD r.ix false ^^ r.inverted) = _
      rw [List.getD_append _ _ _ _ hb]
      rfl

private theorem chosen_eval (cmd : Sum Alias Gate) (ws : List Bool) :
    (chosen cmd ws.length).eval (wires (instruction cmd) ws) = instValue cmd ws := by
  cases cmd with
  | inl a => rfl
  | inr g =>
    change ((ws ++ [g.eval ws]).getD ws.length false ^^ false) = _
    rw [List.getD_append_right _ _ _ _ (by rfl : ws.length ≤ ws.length)]
    simp [instValue]

private theorem chosen_bound (cmd : Sum Alias Gate) (ws : List Bool)
    (hc : match cmd with
      | .inl a => a.bounded ws.length
      | .inr g => g.left.ix < ws.length ∧ g.right.ix < ws.length) :
    (chosen cmd ws.length).bounded (wires (instruction cmd) ws).length := by
  cases cmd with
  | inl a => exact hc
  | inr g => simp [chosen, Alias.bounded, emits]

private def CommandBound (m : Nat) : Sum Alias Gate → Prop
  | .inl a => a.bounded m
  | .inr g => g.left.ix < m ∧ g.right.ix < m

private theorem instruction_represented (cmd : Sum Alias Gate) (t : Bool)
    {old ws : List Bool} {env : List Alias}
    (hc : Coherent old env ws) (hb : EnvBound ws.length env)
    (hval : instValue cmd ws = t)
    (hcmd : CommandBound ws.length cmd) :
    let ws' := wires (instruction cmd) ws
    let env' := env ++ [chosen cmd ws.length]
    Coherent (old ++ [t]) env' ws' ∧ EnvBound ws'.length env' := by
  intro ws' env'
  have hc0 := hc.1
  have hc1 := hc.2
  have evNew : (chosen cmd ws.length).eval ws' = t :=
    (chosen_eval cmd ws).trans hval
  have hbNew : (chosen cmd ws.length).bounded ws'.length :=
    chosen_bound cmd ws (by cases cmd <;> exact hcmd)
  have hl : ws.length ≤ ws'.length := by simp [ws']
  constructor
  · refine ⟨by simp [env', hc0], ?_⟩
    intro j
    by_cases hj : j < env.length
    · change ((env ++ [chosen cmd ws.length]).getD j (.constant false)).eval ws' =
        (old ++ [t]).getD j false
      rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (by omega)]
      exact (alias_preserve cmd ws _ (hb j)).trans (hc1 j)
    · change ((env ++ [chosen cmd ws.length]).getD j (.constant false)).eval ws' =
        (old ++ [t]).getD j false
      rw [List.getD_append_right _ _ _ _ (by omega : env.length ≤ j),
          List.getD_append_right _ _ _ _ (by omega : old.length ≤ j), ← hc0]
      cases j - env.length with
      | zero => exact evNew
      | succ k => simp [Alias.eval]
  · intro j
    change ((env ++ [chosen cmd ws.length]).getD j (.constant false)).bounded ws'.length
    by_cases hj : j < env.length
    · rw [List.getD_append _ _ _ _ hj]
      exact bound_mono hl (hb j)
    · rw [List.getD_append_right _ _ _ _ (by omega : env.length ≤ j)]
      cases j - env.length with
      | zero => exact hbNew
      | succ k => simp [Alias.bounded]

private theorem step_represented (g : Gate) {old ws : List Bool} {env : List Alias}
    (hc : Coherent old env ws) (hb : EnvBound ws.length env) :
    let cmd := compactGate g env
    let ws' := wires (instruction cmd) ws
    let env' := env ++ [chosen cmd ws.length]
    Coherent (old ++ [g.eval old]) env' ws' ∧ EnvBound ws'.length env' :=
  instruction_represented (compactGate g env) (g.eval old) hc hb
    (compactGate_eval g hc) (by
      unfold CommandBound
      exact bounded_command g hb)

/-- Compact all gates in topological order, inlining copies and propagating
constants. Output aliases keep all old address labels meaningful. -/
def compile (gs : List Gate) (m : Nat) (env : List Alias) : List Gate × List Alias :=
  match gs with
  | [] => ([], env)
  | g :: gs =>
    let cmd := compactGate g env
    let recur := compile gs (m + emits cmd) (env ++ [chosen cmd m])
    (instruction cmd ++ recur.1, recur.2)

theorem compile_correct (gs : List Gate) (env : List Alias) (old ws : List Bool)
    (hc : Coherent old env ws) (hb : EnvBound ws.length env) :
    let out := compile gs ws.length env
    Coherent (wires gs old) out.2 (wires out.1 ws) ∧
      EnvBound (wires out.1 ws).length out.2 := by
  induction gs generalizing env old ws with
  | nil => exact ⟨hc,hb⟩
  | cons g gs ih =>
    let cmd := compactGate g env
    let ws' := wires (instruction cmd) ws
    let env' := env ++ [chosen cmd ws.length]
    have hs := step_represented g hc hb
    have hr := ih env' (old ++ [g.eval old]) ws' hs.1 hs.2
    have hl : ws'.length = ws.length + emits cmd := by simp [ws']
    rw [hl] at hr
    simp only [compile, wires_concat]
    exact hr

/-- Every old direct reader of a fixed address contributes zero kept binary
nodes. Other gates can only contribute one, and propagated constants can
cause further losses. -/
theorem compile_emits_le_unread (gs : List Gate) (m : Nat) (env : List Alias)
    (i : Nat) (value : Bool) (hi : i < env.length)
    (hfix : env.getD i (.constant false) = .constant value) :
    (compile gs m env).1.length ≤
      (gs.filter (fun g => !(g.pins.contains i))).length := by
  induction gs generalizing m env with
  | nil => simp [compile]
  | cons g gs ih =>
    let cmd := compactGate g env
    let env' := env ++ [chosen cmd m]
    have hi' : i < env'.length := by simp [env']; omega
    have hfix' : env'.getD i (.constant false) = .constant value := by
      change (env ++ [chosen cmd m]).getD i (.constant false) = _
      rw [List.getD_append _ _ _ _ hi, hfix]
    have ht := ih (m + emits cmd) env' hi' hfix'
    change (instruction cmd ++ (compile gs (m + emits cmd) env').1).length ≤ _
    simp only [List.length_append, instruction_length]
    by_cases hpin : i ∈ g.pins
    · have hz : g.pins.contains i = true := List.contains_iff_mem.mpr hpin
      have hg0 : emits cmd = 0 := compactGate_drops_fixed g env i value hpin hfix
      rw [List.filter_cons_of_neg (p := fun q : Gate => !(q.pins.contains i)) (by simp only [hz, Bool.not_true, Bool.false_eq_true, not_false_eq_true])]
      omega
    · have hz : g.pins.contains i = false := by
        cases h : g.pins.contains i
        · rfl
        · exact False.elim (hpin (List.contains_iff_mem.mp h))
      rw [List.filter_cons_of_pos (p := fun q : Gate => !(q.pins.contains i)) (by simp only [hz, Bool.not_false])]
      have hg' : emits cmd ≤ 1 := compactGate_le_one g env
      simp only [List.length_cons]
      omega


/-- A width-n raw input tape with one coordinate interpreted as a constant. -/
def fixedInput (n i : Nat) (value : Bool) (ws : List Bool) : List Bool :=
  List.ofFn (fun j : Fin n => if j.val = i then value else ws.getD j.val false)

/-- Initial address translation. This retains raw width and makes the fixed
raw absent from all output gate dependencies. -/
def fixedAliases (n i : Nat) (value : Bool) : List Alias :=
  List.ofFn (fun j : Fin n => if j.val = i then .constant value else .wire ⟨j.val,false⟩)

private theorem getD_ofFn {α : Type} {n : Nat} {f : Fin n → α} {j : Nat}
    (h : j < n) (d : α) :
    (List.ofFn f).getD j d = f ⟨j,h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa)]
  simp only [List.getElem_ofFn]

theorem fixed_aliases_ok {n i : Nat} (b : Bool) {ws : List Bool} (hw : ws.length = n) :
    Coherent (fixedInput n i b ws) (fixedAliases n i b) ws ∧
    EnvBound ws.length (fixedAliases n i b) := by
  constructor
  · refine ⟨by simp [fixedAliases, fixedInput], ?_⟩
    intro j
    by_cases hj : j < n
    · unfold fixedAliases fixedInput
      rw [getD_ofFn hj, getD_ofFn hj]
      split <;> simp [Alias.eval, Ref.read, *]
    · have ho : (fixedInput n i b ws).length ≤ j := by
        simp only [fixedInput, List.length_ofFn]; omega
      have he : (fixedAliases n i b).length ≤ j := by
        simp only [fixedAliases, List.length_ofFn]; omega
      rw [List.getD_eq_default _ _ he, List.getD_eq_default _ _ ho]
      rfl
  · intro j
    by_cases hj : j < n
    · unfold fixedAliases
      rw [getD_ofFn hj]
      split <;> simp [Alias.bounded, hw, hj]
    · have he : (fixedAliases n i b).length ≤ j := by
        simp only [fixedAliases, List.length_ofFn]; omega
      rw [List.getD_eq_default _ _ he]
      trivial

/-- Correctness and binary gate-count improvement for fixing one raw input in
an already signed network. The compacted output may be a constant or a signed
wire at any earlier address. -/
theorem fixed_raw_compile (gs : List Gate) {n i : Nat} (hi : i < n) (b sgn : Bool)
    (ws : List Bool) (hw : ws.length = n) :
    let out := compile gs n (fixedAliases n i b)
    out.1.length ≤ (gs.filter (fun g => !(g.pins.contains i))).length ∧
    (((out.2.getD (n + gs.length - 1) (.constant false)).eval
        (wires out.1 ws)) ^^ sgn) = run gs sgn (fixedInput n i b ws) := by
  intro out
  have ha : (fixedAliases n i b).getD i (.constant false) = .constant b := by
    unfold fixedAliases
    rw [getD_ofFn hi]
    simp
  refine ⟨compile_emits_le_unread gs n (fixedAliases n i b) i b (by simpa [fixedAliases]) ha, ?_⟩
  obtain ⟨hc,hbound⟩ := fixed_aliases_ok b hw (i := i)
  have hc' := compile_correct gs (fixedAliases n i b) (fixedInput n i b ws) ws hc hbound
  rw [hw] at hc'
  have hh := hc'.1.2 (n + gs.length - 1)
  rw [hh]
  simp [run, fixedInput]

end PEqualNP.Outside.L_meta_15291_aux.Signed

namespace PEqualNP.Outside.L_meta_15291_aux.Signed

open PEqualNP.MetaComplexity
abbrev OGate := PEqualNP.CircuitLowerBounds.Gate
abbrev OCirc := PEqualNP.CircuitLowerBounds.Circuit
open PEqualNP.CircuitLowerBounds (GateOp)

private def before (env : List Alias) (k : Nat) : Alias :=
  env.getD k (.constant false)

private def translateBinary (op : Bool) (env : List Alias) : List Nat → Sum Alias Gate
  | [] => .inl (.constant op)
  | [k] => .inl (before env k)
  | k :: j :: _ => simplify op (before env k) (before env j)

/-- Lower one ordinary gate to a zero-cost alias, or exactly one binary node. -/
def translateGate (g : OGate) (env : List Alias) : Sum Alias Gate :=
  match g.op with
  | .and => translateBinary true env g.inputs
  | .or => translateBinary false env g.inputs
  | .not =>
    match g.inputs with
    | [] => .inl (.constant true)
    | k :: _ => .inl ((before env k).flip true)
  | _ => .inl (.constant false)

private def goodGate (g : OGate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private theorem binary_value (op : Bool) (xs : List Nat) {old ws : List Bool}
    {env : List Alias} (h : Coherent old env ws) (hl : xs.length ≤ 2) :
    instValue (translateBinary op env xs) ws =
      ((if op then GateOp.and else GateOp.or).eval (xs.map fun i => old.getD i false)) := by
  cases xs with
  | nil =>
    cases op <;> rfl
  | cons k xs =>
    cases xs with
    | nil =>
      change (before env k).eval ws = _
      rw [show (before env k).eval ws = old.getD k false from h.2 k]
      cases op <;> simp [GateOp.eval]
    | cons j rest =>
      cases rest with
      | nil =>
        rw [translateBinary,simplify_correct]
        rw [show (before env k).eval ws = old.getD k false from h.2 k,
            show (before env j).eval ws = old.getD j false from h.2 j]
        cases op <;> simp [join,GateOp.eval]
      | cons l more => simp at hl

private theorem translate_value (g : OGate) {old ws : List Bool} {env : List Alias}
    (hc : Coherent old env ws) (h : goodGate g) :
    instValue (translateGate g env) ws = g.op.eval (g.inputs.map fun i => old.getD i false) := by
  rcases h with ⟨ho,hr⟩
  rcases ho with hi | hi | hi
  · simpa [translateGate,hi] using binary_value true g.inputs hc hr
  · simpa [translateGate,hi] using binary_value false g.inputs hc hr
  · cases e : g.inputs with
    | nil => rw [translateGate,hi,e]; rfl
    | cons k xs =>
      rw [translateGate,hi,e]
      simp only [instValue,Alias.eval_flip,before,hc.2,List.map_cons,GateOp.eval,
        List.headD_cons]
      cases old.getD k false <;> rfl

private theorem binary_valid (op : Bool) (xs : List Nat) {m : Nat}
    {env : List Alias} (hb : EnvBound m env) :
    match translateBinary op env xs with
    | .inl ar => ar.bounded m
    | .inr g => g.left.ix < m ∧ g.right.ix < m := by
  cases xs with
  | nil => trivial
  | cons k xs =>
    cases xs with
    | nil => exact hb k
    | cons j rest => exact bounded_simplify m op _ _ (hb k) (hb j)

private theorem translate_valid (g : OGate) {m : Nat} {env : List Alias}
    (hb : EnvBound m env) :
    match translateGate g env with
    | .inl a => a.bounded m
    | .inr k => k.left.ix < m ∧ k.right.ix < m := by
  cases he : g.op with
  | and => simpa only [translateGate,he] using binary_valid true g.inputs hb
  | or => simpa only [translateGate,he] using binary_valid false g.inputs hb
  | not =>
    cases e : g.inputs with
    | nil => simp [translateGate,he,e,Alias.bounded]
    | cons k rest =>
      simpa only [translateGate,he,e,before,Alias.readIn] using
        (bounded_pin (⟨k,true⟩ : Ref) hb)
  | mod r => simp [translateGate,he,Alias.bounded]
  | maj => simp [translateGate,he,Alias.bounded]

def binaryOperation (g : OGate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

private theorem binary_emits_le (op : Bool) (xs : List Nat) (env : List Alias) :
    emits (translateBinary op env xs) ≤ 1 := by
  cases translateBinary op env xs <;> simp [emits]

private theorem translate_emits_le (g : OGate) (env : List Alias) :
    emits (translateGate g env) ≤ (if binaryOperation g then 1 else 0) := by
  cases h : g.op with
  | and => simpa [binaryOperation,translateGate,h] using binary_emits_le true g.inputs env
  | or => simpa [binaryOperation,translateGate,h] using binary_emits_le false g.inputs env
  | not => cases e : g.inputs <;> simp [translateGate,binaryOperation,h,e,emits]
  | mod r => simp [translateGate,binaryOperation,h,emits]
  | maj => simp [translateGate,binaryOperation,h,emits]

/-- Strip all explicit NOT gates by using free signs on output and operand aliases. -/
def lower : List OGate → Nat → List Alias → List Gate × List Alias
  | [], _, env => ([], env)
  | g :: gs, m, env =>
    let cmd := translateGate g env
    let r := lower gs (m + emits cmd) (env ++ [chosen cmd m])
    (instruction cmd ++ r.1, r.2)

private def ordinaryWires (gs : List OGate) (xs : List Bool) : List Bool :=
  gs.foldl (fun ys g => ys ++ [g.op.eval (g.inputs.map fun i => ys.getD i false)]) xs

theorem lower_correct (gs : List OGate) (env : List Alias) (old ws : List Bool)
    (hc : Coherent old env ws) (hb : EnvBound ws.length env)
    (hgood : ∀ g ∈ gs, goodGate g) :
    let out := lower gs ws.length env
    Coherent (ordinaryWires gs old) out.2 (wires out.1 ws) ∧
      EnvBound (wires out.1 ws).length out.2 := by
  induction gs generalizing env old ws with
  | nil => exact ⟨hc,hb⟩
  | cons g gs ih =>
    let cmd := translateGate g env
    let ws' := wires (instruction cmd) ws
    let env' := env ++ [chosen cmd ws.length]
    let t := g.op.eval (g.inputs.map fun i => old.getD i false)
    have hs := instruction_represented cmd t hc hb
      (translate_value g hc (hgood g (by simp))) (by
        unfold CommandBound
        exact translate_valid g hb)
    have hr := ih env' (old ++ [t]) ws' hs.1 hs.2 (fun k hk => hgood k (by simp [hk]))
    have hl : ws'.length = ws.length + emits cmd := by simp [ws']
    rw [hl] at hr
    simp only [lower,wires_concat]
    exact hr

theorem lower_count (gs : List OGate) (m : Nat) (env : List Alias) :
    (lower gs m env).1.length ≤ (gs.filter binaryOperation).length := by
  induction gs generalizing m env with
  | nil => simp [lower]
  | cons g gs ih =>
    let cmd := translateGate g env
    let env' := env ++ [chosen cmd m]
    have hn := ih (m + emits cmd) env'
    have he := translate_emits_le g env
    change (instruction cmd ++ (lower gs (m + emits cmd) env').1).length ≤ _
    simp only [List.length_append,instruction_length,List.filter_cons]
    cases h : binaryOperation g <;> simp only [h,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at he ⊢ <;>
      change emits cmd ≤ _ at he <;> omega

/-- The initial signed alias for every raw directly refers to the raw wire. -/
def identities (n : Nat) : List Alias := List.ofFn (fun j : Fin n => .wire ⟨j.val,false⟩)

private theorem identities_ok {ws : List Bool} :
    Coherent ws (identities ws.length) ws ∧ EnvBound ws.length (identities ws.length) := by
  constructor
  · refine ⟨by simp [identities], ?_⟩
    intro i
    by_cases h : i < ws.length
    · rw [identities,getD_ofFn h]
      simp [Alias.eval,Ref.read]
    · have h1 : (identities ws.length).length ≤ i := by simpa [identities] using (not_lt.mp h)
      rw [List.getD_eq_default _ _ h1,List.getD_eq_default _ _ (not_lt.mp h)]
      rfl
  · intro i
    by_cases h : i < ws.length
    · rw [identities,getD_ofFn h]
      exact h
    · have h1 : (identities ws.length).length ≤ i := by simpa [identities] using (not_lt.mp h)
      rw [List.getD_eq_default _ _ h1]
      trivial

/-- A signed lowering of the official circuit model, with a certified budget
counting only its original binary operations. The output is an arbitrary
signed alias; reducing to LiveBinary additionally requires dead-code pruning. -/
theorem lower_official (C : OCirc) (n : Nat) (hfan : FanInTwo C) :
    let out := lower C.gates n (identities n)
    out.1.length ≤ (C.gates.filter binaryOperation).length ∧
      ∀ ws : List Bool, ws.length = n →
        ((out.2.getD C.output (.constant false)).eval (wires out.1 ws)) = C.eval ws := by
  intro out
  refine ⟨lower_count C.gates n (identities n), ?_⟩
  intro ws hw
  have hg : ∀ g ∈ C.gates, goodGate g := by
    intro g hm
    have hs := hfan g hm
    exact ⟨by simpa using hs.1, hs.2⟩
  obtain ⟨hc,hb⟩ := identities_ok (ws := ws)
  have hh := lower_correct C.gates (identities ws.length) ws ws hc hb hg
  have he := hh.1.2 C.output
  rw [hw] at he
  exact he


/-- Valid earlier source indexes and distinct pins, independent of liveness. -/
inductive ForwardDistinct : Nat → List Gate → Prop
  | nil (m : Nat) : ForwardDistinct m []
  | cons {m : Nat} {g : Gate} {gs : List Gate} :
      g.left.ix < m → g.right.ix < m → g.left.ix ≠ g.right.ix →
      ForwardDistinct (m + 1) gs → ForwardDistinct m (g :: gs)

private theorem translated_binary_distinct (op : Bool) (env : List Alias)
    (inputs : List Nat) (g : Gate) (h : translateBinary op env inputs = .inr g) :
    g.left.ix ≠ g.right.ix := by
  cases inputs with
  | nil => simp [translateBinary] at h
  | cons k rest =>
    cases rest with
    | nil => simp [translateBinary] at h
    | cons j rest => exact emitted_distinct op (before env k) (before env j) g h

private theorem translated_distinct (raw : OGate) (env : List Alias) (g : Gate)
    (h : translateGate raw env = .inr g) : g.left.ix ≠ g.right.ix := by
  cases hp : raw.op with
  | and => exact translated_binary_distinct true env raw.inputs g (by simpa [translateGate,hp] using h)
  | or => exact translated_binary_distinct false env raw.inputs g (by simpa [translateGate,hp] using h)
  | not => cases e : raw.inputs <;> simp [translateGate,hp,e] at h
  | mod n => simp [translateGate,hp] at h
  | maj => simp [translateGate,hp] at h

private theorem coherent_alias_map (env : List Alias) (ws : List Bool) :
    Coherent (env.map (fun a => a.eval ws)) env ws := by
  refine ⟨by simp, ?_⟩
  intro j
  exact (List.getD_map env (.constant false) (fun a => a.eval ws)).symm

theorem lower_forward (gs : List OGate) (env : List Alias) (ws : List Bool)
    (hb : EnvBound ws.length env) :
    ForwardDistinct ws.length (lower gs ws.length env).1 := by
  induction gs generalizing env ws with
  | nil => exact .nil ws.length
  | cons op gs ih =>
    let cmd := translateGate op env
    let ws' := wires (instruction cmd) ws
    let env' := env ++ [chosen cmd ws.length]
    have hvalid : CommandBound ws.length cmd := translate_valid op hb
    have hrepr := instruction_represented cmd (instValue cmd ws) (coherent_alias_map env ws) hb rfl hvalid
    have htail := ih env' ws' hrepr.2
    have hlen : ws'.length = ws.length + emits cmd := by simp [ws']
    rw [hlen] at htail
    change ForwardDistinct ws.length (instruction cmd ++ (lower gs (ws.length + emits cmd) env').1)
    cases he : cmd with
    | inl c =>
      simp only [he,instruction,emits,Nat.add_zero,List.nil_append] at htail ⊢
      exact htail
    | inr g =>
      have hne := translated_distinct op env g he
      rw [he] at hvalid
      have hv : g.left.ix < ws.length ∧ g.right.ix < ws.length := hvalid
      simp only [he,instruction,emits,List.singleton_append] at htail ⊢
      exact .cons hv.1 hv.2 hne htail

/-- Official lowering emits only gates with distinct earlier source IDs. -/
theorem official_lower_forward (C : OCirc) (n : Nat) :
    ForwardDistinct n (lower C.gates n (identities n)).1 := by
  let ws := List.replicate n false
  have hlen : ws.length = n := by simp [ws]
  have h := lower_forward C.gates (identities ws.length) ws (identities_ok (ws := ws)).2
  rwa [hlen] at h

end PEqualNP.Outside.L_meta_15291_aux.Signed

namespace PEqualNP.Outside.L_meta_15291_aux.Signed
open PEqualNP.MetaComplexity

/-- Monotone renumbering on the complement of a deleted address. -/
def lowerAddress (removed i : Nat) : Nat := if removed < i then i-1 else i

def Ref.shift (r : Ref) (removed : Nat) : Ref := ⟨lowerAddress removed r.ix, r.inverted⟩

def Gate.shift (g : Gate) (removed : Nat) : Gate :=
  ⟨g.andGate,g.left.shift removed,g.right.shift removed⟩

private theorem address_small (k m i : Nat) (hkm : k < m) (hi : i < m) (hki : i ≠ k) :
    lowerAddress k i < m-1 := by
  unfold lowerAddress
  split <;> omega

private theorem address_injective {k i j : Nat}
    (hi : i ≠ k) (hj : j ≠ k) (h : lowerAddress k i = lowerAddress k j) :
    i = j := by
  unfold lowerAddress at h
  split at h <;> split at h <;> omega

private theorem erase_then_lookup {α : Type} (xs : List α) (k j : Nat) (d : α)
    (hjk : j ≠ k) : (xs.eraseIdx k).getD (lowerAddress k j) d = xs.getD j d := by
  simp only [List.getD_eq_getElem?_getD,lowerAddress]
  split
  next h =>
    rw [List.getElem?_eraseIdx_of_ge (by omega : k ≤ j-1), show j-1+1=j by omega]
  next h =>
    rw [List.getElem?_eraseIdx_of_lt (by omega : j < k)]

private theorem erase_append_one {α : Type} (xs : List α) (k : Nat) (t : α)
    (hk : k < xs.length) :
    (xs ++ [t]).eraseIdx k = xs.eraseIdx k ++ [t] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change x :: ((xs ++ [t]).eraseIdx k) = x :: (xs.eraseIdx k ++ [t])
      rw [ih k (by simpa using hk)]

private theorem ref_shift_eval (r : Ref) (xs : List Bool) (k : Nat) (hne : r.ix ≠ k) :
    (r.shift k).read (xs.eraseIdx k) = r.read xs := by
  simp only [Ref.read,Ref.shift,erase_then_lookup _ _ _ _ hne]

private theorem gate_shift_eval (g : Gate) (xs : List Bool) (k : Nat)
    (hl : g.left.ix ≠ k) (hr : g.right.ix ≠ k) :
    (g.shift k).eval (xs.eraseIdx k) = g.eval xs := by
  simp only [Gate.eval,Gate.shift,ref_shift_eval _ _ _ hl,ref_shift_eval _ _ _ hr]

private theorem gate_pin_misses {g : Gate} {gs : List Gate} {k : Nat}
    (h : k ∉ uses (g :: gs)) : g.left.ix ≠ k ∧ g.right.ix ≠ k ∧ k ∉ uses gs := by
  change k ∉ g.left.ix :: g.right.ix :: uses gs at h
  exact ⟨fun e => h (by simp [e]),fun e => h (by simp [e]),fun e => h (by simp [e])⟩

/-- If no gate reads an already-allocated removed address, renumbering all
future reads makes evaluation commute with deleting that register. -/
theorem shift_wires (gs : List Gate) (xs : List Bool) (k : Nat)
    (hk : k < xs.length) (hm : k ∉ uses gs) :
    wires (gs.map (·.shift k)) (xs.eraseIdx k) = (wires gs xs).eraseIdx k := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hl,hr,hm'⟩ := gate_pin_misses hm
    change wires (gs.map (·.shift k)) (xs.eraseIdx k ++ [(g.shift k).eval (xs.eraseIdx k)]) =
      (wires gs (xs ++ [g.eval xs])).eraseIdx k
    rw [gate_shift_eval g xs k hl hr,←erase_append_one xs k (g.eval xs) hk]
    exact ih (xs ++ [g.eval xs]) (by simp; omega) hm'

/-- The combinational companion to shift_wires. -/
theorem shift_forward {m : Nat} {gs : List Gate} (hf : ForwardDistinct m gs)
    (k : Nat) (hk : k < m) (hm : k ∉ uses gs) :
    ForwardDistinct (m-1) (gs.map (·.shift k)) := by
  induction hf with
  | nil _ => exact .nil _
  | @cons m g gs hl hr hne hf ih =>
    obtain ⟨hl',hr',hm'⟩ := gate_pin_misses hm
    obtain ht := ih (by omega) hm'
    change ForwardDistinct (m-1) (g.shift k :: gs.map (·.shift k))
    refine .cons (address_small k m g.left.ix hk hl hl')
      (address_small k m g.right.ix hk hr hr') ?_ ?_
    · exact fun h => hne (address_injective hl' hr' h)
    · have hs : m+1-1=(m-1)+1 := by omega
      rwa [hs] at ht

private theorem shift_unchanged (g : Gate) (m k : Nat) (h : m ≤ k)
    (hl : g.left.ix < m) (hr : g.right.ix < m) : g.shift k = g := by
  have hl' : ¬ k < g.left.ix := by omega
  have hr' : ¬ k < g.right.ix := by omega
  cases g with
  | mk op l r =>
    cases l; cases r; simp_all [Gate.shift,Ref.shift,lowerAddress]

/-- Drop a gate whose produced wire is not read by any other gate. The
removed address is reindexed consistently throughout the entire DAG. -/
theorem erase_gate_forward {m : Nat} {gs : List Gate} (hf : ForwardDistinct m gs)
    (p : Nat) (hp : p < gs.length) (hm : m+p ∉ uses (gs.eraseIdx p)) :
    ForwardDistinct m ((gs.eraseIdx p).map (·.shift (m+p))) := by
  induction hf generalizing p with
  | nil _ => simp at hp
  | @cons m g gs hl hr hne ht ih =>
    cases p with
    | zero =>
      have h := shift_forward ht m (by omega) (by simpa using hm)
      simpa using h
    | succ p =>
      change m+(p+1) ∉ uses (g :: gs.eraseIdx p) at hm
      obtain ⟨_,_,hm'⟩ := gate_pin_misses hm
      have e : m+(p+1)=m+1+p := by omega
      rw [e] at hm'
      have ht' := ih p (by simpa using hp) hm'
      change ForwardDistinct m (g.shift (m+(p+1)) :: (gs.eraseIdx p).map (·.shift (m+(p+1))))
      rw [shift_unchanged g m _ (by omega) hl hr,e]
      exact .cons hl hr hne ht'

theorem erase_gate_wires {m : Nat} {gs : List Gate} (hf : ForwardDistinct m gs)
    (p : Nat) (hp : p < gs.length) (hm : m+p ∉ uses (gs.eraseIdx p))
    (xs : List Bool) (hx : xs.length = m) :
    wires ((gs.eraseIdx p).map (·.shift (m+p))) xs =
      (wires gs xs).eraseIdx (m+p) := by
  induction hf generalizing p xs with
  | nil _ => simp at hp
  | @cons m g gs hl hr hne ht ih =>
    cases p with
    | zero =>
      have hk : m < (xs ++ [g.eval xs]).length := by simp [hx]
      have h := shift_wires gs (xs ++ [g.eval xs]) m hk (by simpa using hm)
      have he : (xs ++ [g.eval xs]).eraseIdx m = xs := by
        rw [←hx,List.eraseIdx_eq_take_drop_succ]
        simp
      rw [he] at h
      exact h
    | succ p =>
      change m+(p+1) ∉ uses (g :: gs.eraseIdx p) at hm
      obtain ⟨_,_,hm'⟩ := gate_pin_misses hm
      have e : m+(p+1)=m+1+p := by omega
      rw [e] at hm'
      have htail := ih p (by simpa using hp) hm' (xs ++ [g.eval xs]) (by simp [hx])
      change wires ((gs.eraseIdx p).map (·.shift (m+(p+1))))
          (xs ++ [(g.shift (m+(p+1))).eval xs]) =
        (wires gs (xs ++ [g.eval xs])).eraseIdx (m+(p+1))
      rw [shift_unchanged g m _ (by omega) hl hr,e]
      exact htail

/-- A projected-away raw that has no remaining reads preserves semantics. -/
theorem erase_raw_eval (gs : List Gate) (xs : List Bool) (k : Nat) (out : Ref)
    (hk : k < xs.length) (hm : k ∉ uses gs) (hne : out.ix ≠ k) :
    (out.shift k).read (wires (gs.map (·.shift k)) (xs.eraseIdx k)) = out.read (wires gs xs) := by
  rw [shift_wires gs xs k hk hm]
  exact ref_shift_eval out (wires gs xs) k hne


theorem erase_gate_eval {m : Nat} {gs : List Gate} (hf : ForwardDistinct m gs)
    (p : Nat) (hp : p < gs.length) (hm : m+p ∉ uses (gs.eraseIdx p))
    (xs : List Bool) (hx : xs.length = m) (out : Ref) (hne : out.ix ≠ m+p) :
    (out.shift (m+p)).read (wires ((gs.eraseIdx p).map (·.shift (m+p))) xs) =
      out.read (wires gs xs) := by
  rw [erase_gate_wires hf p hp hm xs hx]
  exact ref_shift_eval out (wires gs xs) (m+p) hne

private theorem uses_erase_subset (gs : List Gate) (p : Nat) :
    uses (gs.eraseIdx p) ⊆ uses gs := by
  intro r hr
  rcases List.mem_flatMap.mp hr with ⟨g,hg,hpin⟩
  exact List.mem_flatMap.mpr ⟨g,List.mem_of_mem_eraseIdx hg,hpin⟩

/-- Forward circuits can never read their own final output wire. -/
theorem forward_uses_bound {m : Nat} {gs : List Gate} (h : ForwardDistinct m gs) :
    ∀ r ∈ uses gs, r < m + gs.length - 1 := by
  induction h with
  | nil _ => simp [uses]
  | @cons m g gs hL hR hD hF ih =>
    intro r hr
    change r ∈ g.left.ix :: g.right.ix :: uses gs at hr
    simp only [List.mem_cons] at hr
    rcases hr with h | h | h
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · have b := ih r h
      simp only [List.length_cons]
      omega

theorem forward_get {m : Nat} {gs : List Gate} (h : ForwardDistinct m gs) :
    ∀ j (hj : j < gs.length),
      (gs[j]'hj).left.ix < m+j ∧ (gs[j]'hj).right.ix < m+j ∧
      (gs[j]'hj).left.ix ≠ (gs[j]'hj).right.ix := by
  induction h with
  | nil _ =>
    intro j hj
    simp at hj
  | @cons m g gs hl hr hD ht ih =>
    intro j hj
    cases j with
    | zero => simpa using And.intro hl (And.intro hr hD)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have r := ih j hj'
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1] using r

private theorem wires_lookup_raw (gs : List Gate) (xs : List Bool) (i : Nat)
    (hi : i < xs.length) :
    (wires gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (wires gs (xs ++ [g.eval xs])).getD i false = _
    rw [ih (xs ++ [g.eval xs]) (by simp; omega),List.getD_append _ _ _ _ hi]

/-- Every raw input has a pair of assignments witnessing its own essentiality. -/
def Essential (n : Nat) (f : List Bool → Bool) : Prop :=
  ∀ i < n, ∃ x y : List Bool, x.length = n ∧ y.length = n ∧ EqExcept i x y ∧ f x ≠ f y

private def SignedRealizes (n : Nat) (f : List Bool → Bool) (gs : List Gate) (out : Ref) : Prop :=
  ForwardDistinct n gs ∧ out.ix < n+gs.length ∧
  ∀ xs : List Bool, xs.length = n → out.read (wires gs xs) = f xs

/-- Any forward signed computation of a function essential in at least two
raw inputs has a live, output-last representative with no gate increase.
The proof uses minimality and single-dead-node deletion, not an untrusted
pruning oracle. -/
theorem normalize_signed {n : Nat} {f : List Bool → Bool} (hn : 1 < n)
    (he : Essential n f) (gs : List Gate) (out : Ref)
    (hf : ForwardDistinct n gs) (ho : out.ix < n+gs.length)
    (hfun : ∀ xs : List Bool, xs.length = n → out.read (wires gs xs) = f xs) :
    ∃ hs : List Gate, ∃ sgn : Bool, hs.length ≤ gs.length ∧ LiveBinary n hs ∧
      ∀ xs : List Bool, xs.length = n → run hs sgn xs = f xs := by
  classical
  let P (k : Nat) := ∃ hs : List Gate, ∃ o : Ref, hs.length = k ∧ SignedRealizes n f hs o
  have ex : ∃ k, P k := ⟨gs.length,gs,out,rfl,hf,ho,hfun⟩
  obtain ⟨hs,o,hle,hF,hO,hR⟩ := Nat.find_spec ex
  have hmin : ∀ k, P k → Nat.find ex ≤ k := fun _ hk => Nat.find_min' ex hk
  have hbig : n ≤ o.ix := by
    by_contra hm
    have hraw : o.ix < n := by omega
    let j := if o.ix = 0 then 1 else 0
    have hj : j < n := by dsimp [j]; split <;> omega
    have hne : o.ix ≠ j := by dsimp [j]; split <;> omega
    obtain ⟨x,y,hx,hy,heq,hneq⟩ := he j hj
    apply hneq
    rw [← hR x hx,← hR y hy]
    simp only [Ref.read,wires_lookup_raw hs x o.ix (by omega),
      wires_lookup_raw hs y o.ix (by omega),heq o.ix hne]
  have hhs : hs ≠ [] := by
    intro hd
    rw [hd,List.length_nil] at hO
    omega
  have hspos : 0 < hs.length := List.length_pos_iff.mpr hhs
  have hb := forward_uses_bound hF
  have no_erase (p : Nat) (hp : p < hs.length) (hnp : n+p ∉ uses hs) (hno : o.ix ≠ n+p) :
      False := by
    let k := n+p
    let ys := (hs.eraseIdx p).map (·.shift k)
    have hy : ys.length = hs.length-1 := by simp [ys,List.length_eraseIdx_of_lt hp]
    have hm : k ∉ uses (hs.eraseIdx p) :=
      fun ht => hnp (uses_erase_subset hs p ht)
    have hyF := erase_gate_forward hF p hp hm
    have hyO : (o.shift k).ix < n + ys.length := by
      have hh : k < n+hs.length := by dsimp [k]; omega
      have ha := address_small k (n+hs.length) o.ix hh hO hno
      change lowerAddress k o.ix < n+ys.length
      rw [hy]
      omega
    have hyR : ∀ xs : List Bool, xs.length = n → (o.shift k).read (wires ys xs) = f xs := by
      intro xs hxs
      exact (erase_gate_eval hF p hp hm xs hxs o hno).trans (hR xs hxs)
    have ht := hmin ys.length ⟨ys,o.shift k,rfl,hyF,hyO,hyR⟩
    omega
  have hout : o.ix = n+hs.length-1 := by
    by_contra heq
    let p := hs.length-1
    have hp : p < hs.length := by dsimp [p]; omega
    have ha : n+p = n+hs.length-1 := by dsimp [p]; omega
    exact no_erase p hp (fun h => by have q := hb (n+p) h; omega) (by rwa [ha])
  have hlive : ∀ i < n+hs.length-1, i ∈ uses hs := by
    intro i hi
    by_contra hm
    by_cases hsmall : i < n
    · obtain ⟨x,y,hx,hy,heq,hneq⟩ := he i hsmall
      have ht := tail_preserve hs hm heq (hx.trans hy.symm)
      have ho' : o.ix ≠ i := by omega
      apply hneq
      rw [← hR x hx, ← hR y hy]
      simp only [Ref.read,ht o.ix ho']
    · let p := i-n
      have hp : p < hs.length := by dsimp [p]; omega
      have hi' : n+p = i := by dsimp [p]; omega
      exact no_erase p hp (by rwa [hi']) (by rw [hi']; omega)
  refine ⟨hs,o.inverted,?_,⟨hhs,forward_get hF,hb,hlive⟩,?_⟩
  · rw [hle]
    exact hmin gs.length ⟨gs,out,rfl,hf,ho,hfun⟩
  · intro xs hxs
    simpa only [run,hxs,Ref.read,hout] using hR xs hxs

theorem ordinary_signed_realizes (C : OCirc) (n : Nat) (f : List Bool → Bool)
    (hf : FanInTwo C) (hn : 0 < n) (he : Essential n f)
    (hfun : ∀ xs : List Bool, xs.length = n → C.eval xs = f xs) :
    ∃ gs : List Gate, ∃ r : Ref, gs.length ≤ (C.gates.filter binaryOperation).length ∧
      ForwardDistinct n gs ∧ r.ix < n+gs.length ∧
      ∀ xs : List Bool, xs.length = n → r.read (wires gs xs) = f xs := by
  let out := lower C.gates n (identities n)
  obtain ⟨bnd,hR⟩ := lower_official C n hf
  have hR' : ∀ xs : List Bool, xs.length = n →
      (out.2.getD C.output (.constant false)).eval (wires out.1 xs) = f xs :=
    fun xs hxs => (hR xs hxs).trans (hfun xs hxs)
  obtain ⟨x,y,hx,hy,_,hneq⟩ := he 0 hn
  cases e : out.2.getD C.output (.constant false) with
  | constant v =>
    have h1 := hR' x hx
    have h2 := hR' y hy
    rw [e] at h1 h2
    exact False.elim (hneq (h1.symm.trans h2))
  | wire r =>
    have hval : r.ix < n + out.1.length := by
      by_contra hbad
      have h1 := hR' x hx
      have h2 := hR' y hy
      rw [e] at h1 h2
      change ((wires out.1 x).getD r.ix false ^^ r.inverted) = f x at h1
      change ((wires out.1 y).getD r.ix false ^^ r.inverted) = f y at h2
      rw [List.getD_eq_default _ _ (by rw [wires_length,hx]; omega)] at h1
      rw [List.getD_eq_default _ _ (by rw [wires_length,hy]; omega)] at h2
      exact hneq (h1.symm.trans h2)
    refine ⟨out.1,r,bnd,official_lower_forward C n,hval,?_⟩
    intro xs hs
    have h := hR' xs hs
    rwa [e] at h

theorem from_list_fn (n : Nat) (xs : List Bool) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs.getD i.val false) = xs := by
  subst n
  have he : (fun i : Fin xs.length => xs.getD i.val false) =
      (fun i : Fin xs.length => xs[i.val]) := by
    funext i
    exact List.getD_eq_getElem _ _ i.isLt
  rw [he]
  exact List.ofFn_getElem

end PEqualNP.Outside.L_meta_15291_aux.Signed

namespace PEqualNP.Outside.L_meta_15291_aux.Signed
theorem fanout_cons (g : Gate) (gs : List Gate) (i : Nat) :
    Fanout (g :: gs) i = g.pins.count i + Fanout gs i := by
  unfold Fanout
  change (g.pins ++ uses gs).count i = _
  simp [List.count_append]


end PEqualNP.Outside.L_meta_15291_aux.Signed

namespace PEqualNP.Outside.L_meta_15291_aux.Signed

/-- A signed alias does not use a chosen source ID. -/
def Alias.avoids (i : Nat) : Alias → Prop
  | .constant _ => True
  | .wire r => r.ix ≠ i

def EnvAvoids (i : Nat) (as : List Alias) : Prop :=
  ∀ j, (as.getD j (.constant false)).avoids i

private def CommandAvoids (i : Nat) : Sum Alias Gate → Prop
  | .inl a => a.avoids i
  | .inr g => g.left.ix ≠ i ∧ g.right.ix ≠ i

private theorem flip_avoids (a : Alias) (i : Nat) (neg : Bool) (ha : a.avoids i) :
    (a.flip neg).avoids i := by cases a <;> exact ha

private theorem simplify_avoids (isAnd : Bool) (a b : Alias) (i : Nat)
    (ha : a.avoids i) (hb : b.avoids i) : CommandAvoids i (simplify isAnd a b) := by
  cases a with
  | constant u => cases u <;> cases isAnd <;> trivial
  | wire r =>
    cases b with
    | constant v => cases v <;> cases isAnd <;> trivial
    | wire q =>
      by_cases hh : r.ix = q.ix
      · rw [simplify,ite_eq_left hh]
        by_cases hneg : r.inverted = q.inverted
        · rw [ite_eq_left hneg]; exact ha
        · rw [ite_eq_right hneg]; trivial
      · rw [simplify,ite_eq_right hh]; exact ⟨ha,hb⟩

private theorem compact_avoids (g : Gate) (env : List Alias) (i : Nat)
    (h : EnvAvoids i env) : CommandAvoids i (compactGate g env) :=
  simplify_avoids _ _ _ i (flip_avoids _ i _ (h g.left.ix)) (flip_avoids _ i _ (h g.right.ix))

private theorem avoids_append (i : Nat) (a : Alias) (env : List Alias)
    (ha : a.avoids i) (he : EnvAvoids i env) : EnvAvoids i (env ++ [a]) := by
  intro j
  by_cases hj : j < env.length
  · rw [List.getD_append _ _ _ _ hj]
    exact he j
  · rw [List.getD_append_right _ _ _ _ (by omega : env.length ≤ j)]
    cases j-env.length with
    | zero => exact ha
    | succ k => simp [Alias.avoids]

theorem compile_avoids (gs : List Gate) (m i : Nat) (env : List Alias)
    (hm : i < m) (h : EnvAvoids i env) :
    i ∉ uses (compile gs m env).1 ∧ EnvAvoids i (compile gs m env).2 := by
  induction gs generalizing m env with
  | nil => exact ⟨by simp [compile,uses],h⟩
  | cons g gs ih =>
    let cmd := compactGate g env
    have hc : CommandAvoids i cmd := compact_avoids g env i h
    have hselect : (chosen cmd m).avoids i := by
      cases he : cmd with
      | inl a =>
        rw [he] at hc
        exact hc
      | inr k => exact Nat.ne_of_gt hm
    have hd : i ∉ uses (instruction cmd) := by
      cases he : cmd with
      | inl a => simp [instruction,uses]
      | inr k =>
        rw [he] at hc
        have hp : k.left.ix ≠ i ∧ k.right.ix ≠ i := hc
        simp [instruction,uses,Gate.pins,hp.1.symm,hp.2.symm]
    have ht := ih (m + emits cmd) (env ++ [chosen cmd m]) (by omega)
      (avoids_append i (chosen cmd m) env hselect h)
    change i ∉ uses (instruction cmd ++ (compile gs (m+emits cmd) (env ++ [chosen cmd m])).1)
      ∧ EnvAvoids i (compile gs (m+emits cmd) (env ++ [chosen cmd m])).2
    exact ⟨by simpa [uses,List.flatMap_append] using And.intro hd ht.1,ht.2⟩

theorem compile_forward (gs : List Gate) (env : List Alias) (ws : List Bool)
    (hb : EnvBound ws.length env) :
    ForwardDistinct ws.length (compile gs ws.length env).1 := by
  induction gs generalizing env ws with
  | nil => exact .nil ws.length
  | cons op gs ih =>
    let cmd := compactGate op env
    let ws' := wires (instruction cmd) ws
    let env' := env ++ [chosen cmd ws.length]
    have hvalid : CommandBound ws.length cmd := bounded_command op hb
    have hrepr := instruction_represented cmd (instValue cmd ws) (coherent_alias_map env ws) hb rfl hvalid
    have htail := ih env' ws' hrepr.2
    have hlen : ws'.length = ws.length + emits cmd := by simp [ws']
    rw [hlen] at htail
    change ForwardDistinct ws.length (instruction cmd ++ (compile gs (ws.length + emits cmd) env').1)
    cases he : cmd with
    | inl c =>
      simp only [he,instruction,emits,Nat.add_zero,List.nil_append] at htail ⊢
      exact htail
    | inr g =>
      have hne := emitted_distinct op.andGate (Alias.readIn op.left env) (Alias.readIn op.right env) g he
      rw [he] at hvalid
      have hv : g.left.ix < ws.length ∧ g.right.ix < ws.length := hvalid
      simp only [he,instruction,emits,List.singleton_append] at htail ⊢
      exact .cons hv.1 hv.2 hne htail

private theorem fixed_avoids (n i : Nat) (b : Bool) :
    EnvAvoids i (fixedAliases n i b) := by
  intro j
  by_cases hb : j < n
  · rw [fixedAliases,getD_ofFn hb]
    by_cases he : j = i <;> simp [Alias.avoids,he]
  · have he : (fixedAliases n i b).length ≤ j := by simp [fixedAliases]; omega
    rw [List.getD_eq_default _ _ he]
    trivial

def Alias.reindex (a : Alias) (i : Nat) : Alias :=
  match a with
  | .constant b => .constant b
  | .wire r => .wire (r.shift i)

private theorem reindex_alias_eval {gs : List Gate} {ws : List Bool} {i : Nat}
    {a : Alias} (ha : a.avoids i) (hi : i < ws.length) (hm : i ∉ uses gs) :
    (a.reindex i).eval (wires (gs.map (·.shift i)) (ws.eraseIdx i)) =
      a.eval (wires gs ws) := by
  cases a with
  | constant b => rfl
  | wire r => exact erase_raw_eval gs ws i r hi hm ha

private theorem fixedInput_id {n i : Nat} {ws : List Bool} (b : Bool)
    (hl : ws.length = n) (hw : ws.getD i false = b) : fixedInput n i b ws = ws := by
  have hlist := from_list_fn n ws hl
  unfold fixedInput
  trans List.ofFn (fun j : Fin n => ws.getD j.val false)
  · apply congrArg List.ofFn
    funext j
    split
    next h => rw [h,hw]
    next _ => rfl
  · exact hlist

/-- Fixing a raw input then removing its unused slot produces a genuine
width n−1 signed circuit. Its output is a reindexed signed alias. -/
theorem fix_and_project (gs : List Gate) {n i : Nat}
    (hi : i < n) (value sign : Bool) :
    let out := compile gs n (fixedAliases n i value)
    let pg := out.1.map (·.shift i)
    let pa := ((out.2.getD (n+gs.length-1) (.constant false)).reindex i).flip sign
    ForwardDistinct (n-1) pg ∧
    pg.length ≤ (gs.filter (fun g => !(g.pins.contains i))).length ∧
    ∀ xs : List Bool, xs.length = n-1 →
      pa.eval (wires pg xs) = run gs sign (xs.insertIdx i value) := by
  intro out pg pa
  have ha := compile_avoids gs n i (fixedAliases n i value) hi (fixed_avoids n i value)
  have hbound : ForwardDistinct n out.1 := by
    let ws := List.replicate n false
    have hl : ws.length = n := by simp [ws]
    have hv := compile_forward gs (fixedAliases n i value) ws (fixed_aliases_ok value hl).2
    rwa [hl] at hv
  refine ⟨shift_forward hbound i hi ha.1,?_,?_⟩
  · have he : (fixedAliases n i value).getD i (.constant false) = .constant value := by
      rw [fixedAliases,getD_ofFn hi]
      simp
    simpa [pg,out] using compile_emits_le_unread gs n (fixedAliases n i value) i value
      (by simpa [fixedAliases]) he
  · intro xs hxs
    let full := xs.insertIdx i value
    have hw : full.length = n := by
      change (xs.insertIdx i value).length = n
      rw [List.length_insertIdx_of_le_length (by omega) value]
      omega
    have hread : full.getD i false = value := by
      have hl : i < full.length := by omega
      rw [List.getD_eq_getElem _ _ hl]
      exact List.getElem_insertIdx_self hl
    have hfull : fixedInput n i value full = full := fixedInput_id value hw hread
    have ht := (fixed_raw_compile gs hi value sign full hw).2
    rw [hfull] at ht
    have hr := reindex_alias_eval (ha.2 (n+gs.length-1)) (by omega : i < full.length) ha.1
    have hErase : full.eraseIdx i = xs := List.eraseIdx_insertIdx_self value
    rw [hErase] at hr
    change (((out.2.getD (n+gs.length-1) (.constant false)).reindex i).flip sign).eval
        (wires pg xs) = _
    rw [Alias.eval_flip,hr]
    exact ht


private theorem single_pin_count (g : Gate) (i : Nat)
    (hne : g.left.ix ≠ g.right.ix) :
    g.pins.count i = (if g.pins.contains i then 1 else 0) := by
  by_cases hL : g.left.ix = i
  · have hR : g.right.ix ≠ i := fun h => hne (hL.trans h.symm)
    simp [Gate.pins,hL,hR]
  · by_cases hR : g.right.ix = i
    · simp [Gate.pins,hL,hR,Ne.symm hL]
    · simp [Gate.pins,hL,hR,Ne.symm hL,Ne.symm hR]

/-- Distinct pins make the number of consumer gates exactly the fanout count. -/
theorem unread_partition {n : Nat} {gs : List Gate} (h : ForwardDistinct n gs)
    (i : Nat) : (gs.filter (fun g => !(g.pins.contains i))).length + Fanout gs i = gs.length := by
  induction h with
  | nil _ => simp [Fanout,uses]
  | @cons n g gs hl hr hne hnext ih =>
    rw [fanout_cons,single_pin_count g i hne,List.filter_cons]
    cases g.pins.contains i <;> simp only [Bool.not_true,Bool.not_false,
      Bool.false_eq_true,ite_false,ite_true,List.length_cons] <;> omega

/-- Combining actual raw projection with fanout accounting proves elimination
of at least one gate for each distinct direct reader. -/
theorem fix_and_project_count {n : Nat} {gs : List Gate} (h : ForwardDistinct n gs)
    (i : Nat) (hi : i < n) (b : Bool) :
    (compile gs n (fixedAliases n i b)).1.length + Fanout gs i ≤ gs.length := by
  have hf := (fix_and_project gs hi b false).2.1
  have hpart := unread_partition h i
  simp only [List.length_map] at hf
  omega

end PEqualNP.Outside.L_meta_15291_aux.Signed

namespace PEqualNP.Outside.L_meta_15291_aux.Signed

theorem forward_from_get (gs : List Gate) (n : Nat)
    (h : ∀ j (hj : j < gs.length),
      (gs[j]'hj).left.ix < n+j ∧ (gs[j]'hj).right.ix < n+j ∧
      (gs[j]'hj).left.ix ≠ (gs[j]'hj).right.ix) :
    ForwardDistinct n gs := by
  induction gs generalizing n with
  | nil => exact .nil _
  | cons g gs ih =>
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero,Nat.add_zero] at h0
    refine .cons h0.1 h0.2.1 h0.2.2 (ih (n+1) ?_)
    intro j hj
    have ht := h (j+1) (by simpa using hj)
    simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1] using ht

/-- Model-independent shorthand for a signed lower bound after checking the
source numbering; dead gates and arbitrary output locations are allowed. -/
def SignedAtLeast (n : Nat) (f : List Bool → Bool) (min : Nat) : Prop :=
  ∀ gs : List Gate, ∀ out : Ref,
    ForwardDistinct n gs → out.ix < n+gs.length →
    (∀ xs : List Bool, xs.length = n → out.read (wires gs xs) = f xs) →
    min ≤ gs.length

private theorem alias_to_ref (n : Nat) (f : List Bool → Bool) (hn : 0 < n)
    (he : Essential n f) (gs : List Gate) (a : Alias)
    (hfun : ∀ xs : List Bool, xs.length = n → a.eval (wires gs xs) = f xs) :
    ∃ r : Ref, a = .wire r ∧ r.ix < n+gs.length := by
  obtain ⟨x,y,hx,hy,_,hneq⟩ := he 0 hn
  cases a with
  | constant b =>
    exact False.elim (hneq ((hfun x hx).symm.trans (hfun y hy)))
  | wire r =>
    refine ⟨r,rfl,?_⟩
    by_contra hp
    have h1 := hfun x hx
    have h2 := hfun y hy
    change ((wires gs x).getD r.ix false ^^ r.inverted) = f x at h1
    change ((wires gs y).getD r.ix false ^^ r.inverted) = f y at h2
    rw [List.getD_eq_default _ _ (by rw [wires_length,hx]; omega)] at h1
    rw [List.getD_eq_default _ _ (by rw [wires_length,hy]; omega)] at h2
    exact hneq (h1.symm.trans h2)

/-- If a constant restriction has signed complexity at least k, a realization
of the original function must have at least k plus the fixed raw's direct
fanout. This handles repeated inputs, not just the usual one-gate deletion. -/
theorem signed_minor_loss {n k i : Nat} {small : List Bool → Bool} (hn : 1 < n)
    (hi : i < n) (he : Essential (n-1) small)
    (hbelow : SignedAtLeast (n-1) small k)
    (gs : List Gate) (sgn value : Bool) (hfw : ForwardDistinct n gs)
    (heval : ∀ xs : List Bool, xs.length = n-1 →
      run gs sgn (xs.insertIdx i value) = small xs) :
    k + Fanout gs i ≤ gs.length := by
  let cmd := compile gs n (fixedAliases n i value)
  let gs' := cmd.1.map (·.shift i)
  let out := ((cmd.2.getD (n+gs.length-1) (.constant false)).reindex i).flip sgn
  have hs := fix_and_project gs hi value sgn
  have hreal : ∀ xs : List Bool, xs.length = n-1 → out.eval (wires gs' xs) = small xs :=
    fun xs hxs => (hs.2.2 xs hxs).trans (heval xs hxs)
  obtain ⟨r,hr,hrange⟩ := alias_to_ref (n-1) small (by omega) he gs' out hreal
  have hv : ∀ xs : List Bool, xs.length = n-1 → r.read (wires gs' xs) = small xs := by
    intro xs hxs
    have h := hreal xs hxs
    rw [hr] at h
    exact h
  have hk := hbelow gs' r hs.1 hrange hv
  have hct : cmd.1.length + Fanout gs i ≤ gs.length := fix_and_project_count hfw i hi value
  have hc : gs'.length = cmd.1.length := by simp [gs']
  omega

/-- Adding an essential input increases signed complexity by at least one if
a specified constant restriction has the given smaller function. -/
theorem lift_essential_minor {n k i : Nat} {large small : List Bool → Bool}
    (hn : 1 < n) (hi : i < n) (value : Bool) (he : Essential n large)
    (hsmall : Essential (n-1) small) (hbelow : SignedAtLeast (n-1) small k)
    (hident : ∀ xs : List Bool, xs.length = n-1 →
      large (xs.insertIdx i value) = small xs) :
    SignedAtLeast n large (k+1) := by
  intro gs r hfw hrange hR
  obtain ⟨hs,sgn,hsize,hlive,hrel⟩ := normalize_signed hn he gs r hfw hrange hR
  have hf := forward_from_get hs n hlive.forward
  have hseen : 1 ≤ Fanout hs i := fanout_pos hlive i
    (by have hp := List.length_pos_iff.mpr hlive.nonempty; omega)
  have hcount := signed_minor_loss hn hi hsmall hbelow hs sgn value hf (by
    intro xs hx
    have hlen : (xs.insertIdx i value).length = n := by
      rw [List.length_insertIdx_of_le_length (by omega)]
      omega
    exact (hrel _ hlen).trans (hident xs hx))
  omega


private def leafRow (n : Nat) (i : Fin n) (m : Fin (2^n)) (b : Bool) : Fin n → Bool :=
  fun j => if j = i then b else m.val.testBit j.val

private theorem lift_essential_table (n : Nat) (f : List Bool → Bool)
    (table : ∀ i : Fin n, ∃ m : Fin (2^n),
      f (List.ofFn (leafRow n i m false)) ≠ f (List.ofFn (leafRow n i m true))) :
    Essential n f := by
  intro i hi
  obtain ⟨m, hm⟩ := table ⟨i,hi⟩
  refine ⟨_,_,by simp,by simp,?_,hm⟩
  intro j hj
  by_cases hsmall : j < n
  · rw [getD_ofFn hsmall,getD_ofFn hsmall]
    have hNe : (⟨j,hsmall⟩ : Fin n) ≠ ⟨i,hi⟩ := fun h => hj (congrArg Fin.val h)
    simp [leafRow,hNe]
  · repeat rw [List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_15291_aux.Signed

namespace PEqualNP.Outside.L_meta_15291_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3937053354 * 2 ^ 32 + 3903367168)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def upper : Circuit :=
  ⟨[⟨.or,[1,2]⟩, ⟨.and,[1,2]⟩, ⟨.and,[7,3]⟩, ⟨.and,[8,4]⟩,
     ⟨.or,[9,0]⟩, ⟨.or,[3,4]⟩, ⟨.and,[6,11]⟩, ⟨.or,[12,5]⟩,
     ⟨.and,[10,13]⟩],14⟩

def minor (xs : List Bool) : Bool :=
  (xs.getD 0 false || (xs.getD 1 false && xs.getD 2 false &&
    xs.getD 3 false && xs.getD 4 false)) &&
    ((xs.getD 1 false || xs.getD 2 false) && (xs.getD 3 false || xs.getD 4 false))

private def full (xs : List Bool) : Bool := upper.eval xs

private theorem ess5 : Signed.Essential 5 minor := by
  apply Signed.lift_essential_table
  intro i
  fin_cases i
  · exact ⟨10, by decide +kernel⟩
  · exact ⟨9, by decide +kernel⟩
  · exact ⟨9, by decide +kernel⟩
  · exact ⟨3, by decide +kernel⟩
  · exact ⟨3, by decide +kernel⟩

private theorem ess6 : Signed.Essential 6 full := by
  apply Signed.lift_essential_table
  intro i
  fin_cases i
  · exact ⟨10, by decide +kernel⟩
  · exact ⟨9, by decide +kernel⟩
  · exact ⟨9, by decide +kernel⟩
  · exact ⟨3, by decide +kernel⟩
  · exact ⟨3, by decide +kernel⟩
  · exact ⟨1, by decide +kernel⟩

private theorem checkCons {n : Nat} {P : (Fin (n+1) → Bool) → Prop}
    (h0 : ∀ y : Fin n → Bool, P (Fin.cons false y))
    (h1 : ∀ y : Fin n → Bool, P (Fin.cons true y)) :
    ∀ x : Fin (n+1) → Bool, P x := by
  intro x
  rw [← Fin.cons_self_tail x]
  cases h : x 0
  · exact h0 _
  · exact h1 _

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem table_cut_0 : ∀ y : Fin 4 → Bool, full ((List.ofFn (Fin.cons false (y))).insertIdx 5 false) = minor (List.ofFn (Fin.cons false (y))) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem table_cut_1 : ∀ y : Fin 4 → Bool, full ((List.ofFn (Fin.cons true (y))).insertIdx 5 false) = minor (List.ofFn (Fin.cons true (y))) := by
  decide +kernel

private theorem table_cut : ∀ y : Fin 5 → Bool, full ((List.ofFn (y)).insertIdx 5 false) = minor (List.ofFn (y)) :=
  checkCons (P := fun y => full ((List.ofFn (y)).insertIdx 5 false) = minor (List.ofFn (y))) table_cut_0 table_cut_1

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem upper_truth_000 : ∀ y : Fin 3 → Bool, upper.eval (List.ofFn (Fin.cons false (Fin.cons false (Fin.cons false (y))))) = target (Fin.cons false (Fin.cons false (Fin.cons false (y)))) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem upper_truth_001 : ∀ y : Fin 3 → Bool, upper.eval (List.ofFn (Fin.cons false (Fin.cons false (Fin.cons true (y))))) = target (Fin.cons false (Fin.cons false (Fin.cons true (y)))) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem upper_truth_010 : ∀ y : Fin 3 → Bool, upper.eval (List.ofFn (Fin.cons false (Fin.cons true (Fin.cons false (y))))) = target (Fin.cons false (Fin.cons true (Fin.cons false (y)))) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem upper_truth_011 : ∀ y : Fin 3 → Bool, upper.eval (List.ofFn (Fin.cons false (Fin.cons true (Fin.cons true (y))))) = target (Fin.cons false (Fin.cons true (Fin.cons true (y)))) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem upper_truth_100 : ∀ y : Fin 3 → Bool, upper.eval (List.ofFn (Fin.cons true (Fin.cons false (Fin.cons false (y))))) = target (Fin.cons true (Fin.cons false (Fin.cons false (y)))) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem upper_truth_101 : ∀ y : Fin 3 → Bool, upper.eval (List.ofFn (Fin.cons true (Fin.cons false (Fin.cons true (y))))) = target (Fin.cons true (Fin.cons false (Fin.cons true (y)))) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem upper_truth_110 : ∀ y : Fin 3 → Bool, upper.eval (List.ofFn (Fin.cons true (Fin.cons true (Fin.cons false (y))))) = target (Fin.cons true (Fin.cons true (Fin.cons false (y)))) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1500000 in
private theorem upper_truth_111 : ∀ y : Fin 3 → Bool, upper.eval (List.ofFn (Fin.cons true (Fin.cons true (Fin.cons true (y))))) = target (Fin.cons true (Fin.cons true (Fin.cons true (y)))) := by
  decide +kernel

private theorem upper_truth_00 : ∀ y : Fin 4 → Bool, upper.eval (List.ofFn (Fin.cons false (Fin.cons false (y)))) = target (Fin.cons false (Fin.cons false (y))) :=
  checkCons (P := fun y => upper.eval (List.ofFn (Fin.cons false (Fin.cons false (y)))) = target (Fin.cons false (Fin.cons false (y)))) upper_truth_000 upper_truth_001

private theorem upper_truth_01 : ∀ y : Fin 4 → Bool, upper.eval (List.ofFn (Fin.cons false (Fin.cons true (y)))) = target (Fin.cons false (Fin.cons true (y))) :=
  checkCons (P := fun y => upper.eval (List.ofFn (Fin.cons false (Fin.cons true (y)))) = target (Fin.cons false (Fin.cons true (y)))) upper_truth_010 upper_truth_011

private theorem upper_truth_10 : ∀ y : Fin 4 → Bool, upper.eval (List.ofFn (Fin.cons true (Fin.cons false (y)))) = target (Fin.cons true (Fin.cons false (y))) :=
  checkCons (P := fun y => upper.eval (List.ofFn (Fin.cons true (Fin.cons false (y)))) = target (Fin.cons true (Fin.cons false (y)))) upper_truth_100 upper_truth_101

private theorem upper_truth_11 : ∀ y : Fin 4 → Bool, upper.eval (List.ofFn (Fin.cons true (Fin.cons true (y)))) = target (Fin.cons true (Fin.cons true (y))) :=
  checkCons (P := fun y => upper.eval (List.ofFn (Fin.cons true (Fin.cons true (y)))) = target (Fin.cons true (Fin.cons true (y)))) upper_truth_110 upper_truth_111

private theorem upper_truth_0 : ∀ y : Fin 5 → Bool, upper.eval (List.ofFn (Fin.cons false (y))) = target (Fin.cons false (y)) :=
  checkCons (P := fun y => upper.eval (List.ofFn (Fin.cons false (y))) = target (Fin.cons false (y))) upper_truth_00 upper_truth_01

private theorem upper_truth_1 : ∀ y : Fin 5 → Bool, upper.eval (List.ofFn (Fin.cons true (y))) = target (Fin.cons true (y)) :=
  checkCons (P := fun y => upper.eval (List.ofFn (Fin.cons true (y))) = target (Fin.cons true (y))) upper_truth_10 upper_truth_11

private theorem upper_truth : ∀ y : Fin 6 → Bool, upper.eval (List.ofFn (y)) = target (y) :=
  checkCons (P := fun y => upper.eval (List.ofFn (y)) = target (y)) upper_truth_0 upper_truth_1


private theorem cut (xs : List Bool) (h : xs.length = 5) :
    full (xs.insertIdx 5 false) = minor xs := by
  let x : Fin 5 → Bool := fun i => xs.getD i.val false
  have e : List.ofFn x = xs := Signed.from_list_fn 5 xs h
  rw [←e]
  exact table_cut x

private theorem full_ge8 (h5 : Signed.SignedAtLeast 5 minor 7) : Signed.SignedAtLeast 6 full 8 :=
  Signed.lift_essential_minor (i:=5) (by decide) (by decide) false ess6 ess5 h5 cut

private theorem upper_mono : Monotone2 upper := by simp [Monotone2,upper]
private theorem upper_size : upper.size = 9 := rfl

private theorem mixed_ge9 (h5 : Signed.SignedAtLeast 5 minor 7)
    (C : Circuit) (hf : FanInTwo C)
    (hc : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x)
    (hm : ∃ g ∈ C.gates, g.op = .not) : 9 ≤ C.size := by
  have hc' : ∀ xs : List Bool, xs.length = 6 → C.eval xs = full xs := by
    intro xs hx
    let x : Fin 6 → Bool := fun i => xs.getD i.val false
    have e : List.ofFn x = xs := Signed.from_list_fn 6 xs hx
    rw [←e,hc]
    exact (upper_truth x).symm
  obtain ⟨gs,r,hlen,hfw,hrange,hf'⟩ :=
    Signed.ordinary_signed_realizes C 6 full hf (by decide) ess6 hc'
  have hb := full_ge8 h5 gs r hfw hrange hf'
  have hlt : (C.gates.filter Signed.binaryOperation).length < C.gates.length := by
    rcases hm with ⟨g,hg,hop⟩
    have hle := List.length_filter_le Signed.binaryOperation C.gates
    by_contra hc
    have hh : (C.gates.filter Signed.binaryOperation).length = C.gates.length := by omega
    have hi := (List.length_filter_eq_length_iff.mp hh) g hg
    simp [Signed.binaryOperation,hop] at hi
  change 9 ≤ C.gates.length
  omega

theorem exact_from_signed_minor (h5 : Signed.SignedAtLeast 5 minor 7)
    (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C,hf,hs,hc⟩ := h
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · exact ⟨upper,upper_mono,by rw [upper_size]; exact (mixed_ge9 h5 C hf hc hn).trans hs,upper_truth⟩
  · refine ⟨C,?_,hs,hc⟩
    intro g hg
    obtain ⟨hm,hl⟩ := hf g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm ⊢
    rcases hm with e | e | e
    · exact ⟨Or.inl e,hl⟩
    · exact ⟨Or.inr e,hl⟩
    · exact False.elim (hn ⟨g,hg,e⟩)

end PEqualNP.Outside.L_meta_15291_aux


namespace PEqualNP.Outside.L_meta_15291_aux.Threshold

-- Standalone five-input signed frontier, adapted from the four-input threshold verifier.
abbrev Signal := BitVec 32

def flip (n : Bool) (x : Signal) : Signal := if n then ~~~x else x

def canon (x : Signal) : Signal := flip (x.getLsbD 0) x

def gate (p q : Bool) (a b : Signal) : Signal := canon (flip p a &&& flip q b)

def ttGoal : Signal := 0xe8a8a800

def inputs : List Signal := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def careGroups : List (Fin 32 × Signal) := [(30,0x14404000),(11,0x600478e),(13,0x20053a2),(19,0x406000e),(21,0x120022),(15,0x4200),(27,0x4000008)]

def pairs : List (Fin 32 × Fin 32) :=
  careGroups.flatMap fun q => (List.finRange 32).filterMap fun b =>
    if q.2.getLsbD b.val then some (q.1,b) else none

def rowObs (p : Fin 32) (s : Signal) : Signal :=
  if s.getLsbD p.val then ~~~s else s

def rowUnion (p : Fin 32) : List Signal → Signal
  | [] => 0
  | a::v => rowObs p a ||| rowUnion p v

def cover (v : List Signal) : Bool :=
  careGroups.all fun q => (rowUnion q.1 v &&& q.2) == q.2

def bits : List Bool := [false,true]

def retain (a b : Signal) (ka kb : Bool) (x : Signal) : Bool :=
  (x != a || ka) && (x != b || kb)

def Live : (k : Nat) → Finset Signal → Prop
  | 0,S => S = {ttGoal}
  | k+1,S => ∃ (U : Finset Signal) (a b : Signal) (p q : Bool),
      a ≠ b ∧ a ≠ 0 ∧ b ≠ 0 ∧ gate p q a b ≠ 0 ∧ gate p q a b ∉ S ∧
      S = insert a (insert b U) ∧ Live k (insert (gate p q a b) U)

theorem branch_size {k S} (h : Live k S) : S.card ≤ k+1 := by
  induction k generalizing S with
  | zero => simp [Live] at h; simp [h]
  | succ k ih =>
    obtain ⟨U,a,b,p,q,_,_,_,_,hn,rfl,ht⟩ := h
    have hu : gate p q a b ∉ U := by
      intro hm
      exact hn (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have t := ih ht
    rw [Finset.card_insert_of_notMem hu] at t
    have t₁ := Finset.card_insert_le b U
    have t₂ := Finset.card_insert_le a (insert b U)
    omega

theorem flip_obs_eq (p : Bool) (a : Signal) (i j : Fin 32)
    (h : a.getLsbD i = a.getLsbD j) :
    (flip p a).getLsbD i = (flip p a).getLsbD j := by
  cases p
  · exact h
  · simpa [flip,BitVec.getLsbD_not,i.isLt,j.isLt] using congrArg Bool.not h

theorem gate_obs_eq (p q : Bool) (a b : Signal) (i j : Fin 32)
    (ha : a.getLsbD i = a.getLsbD j) (hb : b.getLsbD i = b.getLsbD j) :
    (gate p q a b).getLsbD i = (gate p q a b).getLsbD j := by
  apply flip_obs_eq
  simp only [BitVec.getLsbD_and]
  rw [flip_obs_eq p a i j ha, flip_obs_eq q b i j hb]

private theorem careGroupsValid :
    careGroups.all (fun q => ttGoal.getLsbD q.1.val && ((q.2 &&& ttGoal) == 0)) = true := by
  decide +kernel

private theorem target_covers (i : Fin 32 × Fin 32) (hi : i ∈ pairs) :
    ttGoal.getLsbD i.1 ≠ ttGoal.getLsbD i.2 := by
  unfold pairs at hi
  obtain ⟨p,hp,hh⟩ := List.mem_flatMap.mp hi
  obtain ⟨n,_,hn⟩ := List.mem_filterMap.mp hh
  by_cases h : p.2.getLsbD n.val = true
  · simp only [h,ite_true,Option.some.injEq] at hn
    subst i
    have ok := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp careGroupsValid) p hp)
    have mask : (p.2 &&& ttGoal) = 0 := beq_iff_eq.mp ok.2
    have hf := congrArg (fun s : Signal => s.getLsbD n.val) mask
    change (p.2 &&& ttGoal).getLsbD n.val = (0 : Signal).getLsbD n.val at hf
    rw [BitVec.getLsbD_and,h,Bool.true_and] at hf
    have h0 : (0 : Signal).getLsbD n.val = false := BitVec.getLsbD_zero
    have hn' : ttGoal.getLsbD n.val = false := hf.trans h0
    change ttGoal.getLsbD p.1.val ≠ ttGoal.getLsbD n.val
    rw [ok.1,hn']
    decide
  · simp only [h,ite_false,reduceCtorEq] at hn

theorem liveSeparates {k S} (h : Live k S) (r : Fin 32 × Fin 32) (hr : r ∈ pairs) :
    ∃ a ∈ S, a.getLsbD r.1 ≠ a.getLsbD r.2 := by
  induction k generalizing S with
  | zero =>
    have e : S = {ttGoal} := h
    exact ⟨ttGoal, by simp [e], target_covers r hr⟩
  | succ k ih =>
    obtain ⟨U,a,b,p,q,_,_,_,_,_,rfl,h⟩ := h
    obtain ⟨z,hz,hs⟩ := ih h
    rcases Finset.mem_insert.mp hz with rfl | hz
    · by_cases ha : a.getLsbD r.1 = a.getLsbD r.2
      · by_cases hb : b.getLsbD r.1 = b.getLsbD r.2
        · exact (hs (gate_obs_eq p q a b r.1 r.2 ha hb)).elim
        · exact ⟨b, by simp, hb⟩
      · exact ⟨a, by simp, ha⟩
    · exact ⟨z,by simp [hz],hs⟩

private theorem rowObsOne (p n : Fin 32) (s : Signal)
    (d : s.getLsbD p ≠ s.getLsbD n) : (rowObs p s).getLsbD n = true := by
  cases hp : s.getLsbD p <;> cases hn : s.getLsbD n <;>
    simp only [rowObs,BitVec.getLsbD_not,n.isLt,decide_true,Bool.true_and,
      hp,hn,Bool.false_eq_true,ite_false,ite_true,Bool.not_true,Bool.not_false,
      ne_eq,not_true_eq_false] at d ⊢

private theorem rowUnionOne (p n : Fin 32) (v : List Signal) (s : Signal)
    (h : s ∈ v) (hs : (rowObs p s).getLsbD n = true) :
    (rowUnion p v).getLsbD n = true := by
  induction v with
  | nil => simp at h
  | cons a v ih =>
    rcases List.mem_cons.mp h with rfl | hh
    · simp [rowUnion,hs]
    · simp [rowUnion,ih hh]

theorem live_cover {k S} {v : List Signal} (h : Live k S) (e : v.toFinset = S) :
    cover v = true := by
  apply List.all_eq_true.mpr
  intro q hq
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  rw [BitVec.getLsbD_and]
  cases hneg : q.2.getLsbD n
  · exact Bool.and_false _
  · let i : Fin 32 := ⟨n,hn⟩
    have hpair : (q.1,i) ∈ pairs := by
      apply List.mem_flatMap.mpr
      refine ⟨q,hq,List.mem_filterMap.mpr ⟨i,List.mem_finRange i,?_⟩⟩
      simp [i,hneg]
    obtain ⟨s,hm,hs⟩ := liveSeparates h _ hpair
    rw [←e,List.mem_toFinset] at hm
    rw [Bool.and_true]
    exact rowUnionOne q.1 i v s hm (rowObsOne q.1 i s hs)

def rootMoves (k : Nat) (v : List Signal) : List (List Signal) :=
  v.flatMap fun a => v.flatMap fun b =>
    if ¬ a.toNat < b.toNat then [] else
      bits.flatMap fun p => bits.flatMap fun q =>
        let z := gate p q a b
        if z=0 ∨ z∈v then [] else
          bits.flatMap fun ka => bits.filterMap fun kb =>
            let w := z :: v.filter (retain a b ka kb)
            if decide (w.length ≤ k+1) && cover w then some w else none

private theorem keep_exact {a b : Signal} {U : Finset Signal} {v : List Signal}
    (ab : a ≠ b) (e : v.toFinset = insert a (insert b U)) :
    (v.filter (retain a b (decide (a∈U)) (decide (b∈U)))).toFinset = U := by
  ext x
  simp only [List.mem_toFinset,List.mem_filter,retain,Bool.and_eq_true,Bool.or_eq_true,
    bne_iff_ne,decide_eq_true_eq]
  have hx : x∈v ↔ x=a ∨ x=b ∨ x∈U := by
    rw [←List.mem_toFinset,e]
    simp
  rw [hx]
  constructor
  · intro ⟨hv,⟨ha,hb⟩⟩
    rcases hv with rfl | rfl | hv
    · exact ha.resolve_left (by simp)
    · exact hb.resolve_left (by simp)
    · exact hv
  · intro hU
    exact ⟨Or.inr (Or.inr hU),
      (by by_cases e₁ : x=a; exact Or.inr (e₁ ▸ hU); exact Or.inl e₁),
      (by by_cases e₂ : x=b; exact Or.inr (e₂ ▸ hU); exact Or.inl e₂)⟩

private theorem rootMoveMem
    {k : Nat} {v : List Signal} {a b : Signal} {p q ka kb : Bool}
    (ha : a∈v) (hb : b∈v) (hlt : a.toNat < b.toNat)
    (hn : gate p q a b ≠ 0 ∧ gate p q a b ∉ v)
    (hOK : let w := gate p q a b :: v.filter (retain a b ka kb)
      w.length ≤ k+1 ∧ cover w = true) :
    gate p q a b :: v.filter (retain a b ka kb) ∈ rootMoves k v := by
  have hp (t : Bool) : t ∈ bits := by cases t <;> simp [bits]
  unfold rootMoves
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  simp only [hlt,not_true,ite_false]
  apply List.mem_flatMap.mpr
  refine ⟨p,hp p,List.mem_flatMap.mpr ⟨q,hp q,?_⟩⟩
  rw [if_neg (fun h => h.elim hn.1 hn.2)]
  apply List.mem_flatMap.mpr
  refine ⟨ka,hp ka,?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨kb,hp kb,by simpa only [hOK.1,hOK.2,decide_true,Bool.true_and,ite_true]⟩

def certReachable (k : Nat) (v : List Signal) : Prop := ∃ m ≤ k, Live m v.toFinset

theorem certStop (v : List Signal) (h : certReachable 0 v) : ttGoal ∈ v := by
  obtain ⟨m,hm,hl⟩ := h
  have he : m=0 := by omega
  subst m
  change v.toFinset = {ttGoal} at hl
  exact List.mem_toFinset.mp (by simp [hl])

theorem certAdvance (k : Nat) (v : List Signal) (nd : v.Nodup)
    (h : certReachable (k+1) v) :
    ttGoal ∈ v ∨ ∃ w ∈ rootMoves k v, certReachable k w := by
  obtain ⟨m,hm,hl⟩ := h
  cases m with
  | zero =>
    left
    exact certStop v ⟨0,by decide,hl⟩
  | succ m =>
    right
    obtain ⟨U,a,b,p,q,ab,_,_,nz,notv,e,ht⟩ := hl
    let z := gate p q a b
    let ka : Bool := decide (a∈U)
    let kb : Bool := decide (b∈U)
    let w := z :: v.filter (retain a b ka kb)
    have ha : a∈v := by rw [←List.mem_toFinset,e]; simp
    have hb : b∈v := by rw [←List.mem_toFinset,e]; simp
    have notvv : z∉v := by rw [←List.mem_toFinset]; exact notv
    have wn : w.Nodup := by
      refine List.nodup_cons.mpr ⟨?_,nd.filter _⟩
      intro hv
      exact notvv (List.mem_filter.mp hv).1
    have ew : w.toFinset = insert z U := by
      simp only [w,List.toFinset_cons]
      exact congrArg (insert z) (keep_exact ab e)
    have wm := branch_size ht
    rw [←ew,List.toFinset_card_of_nodup wn] at wm
    have wlen : w.length ≤ k+1 := by omega
    have keepGood := live_cover ht ew
    refine ⟨w,?_,⟨m,by omega,ew.symm ▸ ht⟩⟩
    by_cases lt : a.toNat < b.toNat
    · exact rootMoveMem ha hb lt ⟨nz,notvv⟩ ⟨wlen,keepGood⟩
    · have gt : b.toNat < a.toNat := by
        have he : a.toNat ≠ b.toNat := fun hh => ab (BitVec.eq_of_toNat_eq hh)
        omega
      have gc : gate q p b a = gate p q a b := by simp [gate,BitVec.and_comm]
      have ret : retain b a kb ka = retain a b ka kb := by
        funext x
        simp [retain,Bool.and_comm]
      have eq : gate q p b a :: v.filter (retain b a kb ka) = w := by simp [gc,ret,w,z]
      have good : gate q p b a :: v.filter (retain b a kb ka) ∈ rootMoves k v := by
        apply rootMoveMem hb ha gt
        · simpa only [gc] using And.intro nz notvv
        · rw [eq]
          exact ⟨wlen,keepGood⟩
      exact eq ▸ good
theorem live_nonzero {k S} (h : Live k S) : ∀ z ∈ S, z ≠ 0 := by
  induction k generalizing S with
  | zero =>
    have e : S = {ttGoal} := h
    intro z hz
    have q : z=ttGoal := by simpa only [e,Finset.mem_singleton] using hz
    rw [q]
    decide
  | succ k ih =>
    obtain ⟨U,a,b,p,q,_,ha,hb,_,_,rfl,ht⟩ := h
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ha
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hb
    exact ih ht _ (Finset.mem_insert_of_mem hz)

theorem flip_flip (p q : Bool) (x : Signal) :
    flip p (flip q x) = flip (p ^^ q) x := by
  cases p <;> cases q <;> simp [flip,BitVec.not_not]

theorem canon_not (a : Signal) : canon (~~~a) = canon a := by
  have h : (~~~a).getLsbD 0 = !(a.getLsbD 0) := by simp
  rw [canon,h]
  unfold canon
  cases ha : a.getLsbD 0 <;> simp [flip,BitVec.not_not]

theorem canon_flip (p : Bool) (a : Signal) : canon (flip p a) = canon a := by
  cases p
  · rfl
  · exact canon_not a

theorem canon_idempotent (a : Signal) : canon (canon a) = canon a :=
  canon_flip _ _

theorem uncanon_flip (p : Bool) (a : Signal) :
    flip p a = flip (p ^^ a.getLsbD 0) (canon a) := by
  rw [canon,flip_flip]
  cases p <;> cases a.getLsbD 0 <;> rfl

theorem canon_zero : canon (0 : Signal) = 0 := by decide
theorem canon_one : canon (~~~(0 : Signal)) = 0 := by rw [canon_not,canon_zero]

theorem signed_gates_same (p q : Bool) (a : Signal) :
    gate p q a a = 0 ∨ gate p q a a = canon a := by
  cases p <;> cases q
  · right
    change canon (a &&& a) = canon a
    rw [BitVec.and_self]
  · left
    change canon (a &&& ~~~a) = 0
    rw [BitVec.and_not_self]
    exact canon_zero
  · left
    change canon (~~~a &&& a) = 0
    rw [BitVec.not_and_self]
    exact canon_zero
  · right
    change canon (~~~a &&& ~~~a) = canon a
    rw [BitVec.and_self,canon_not]

theorem signed_gates_zero_l (p q : Bool) (a : Signal) :
    gate p q 0 a = 0 ∨ gate p q 0 a = canon a := by
  have aa (x : Signal) : ((~~~(0 : Signal)) &&& x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hz : (0 : Signal).getLsbD i = false := BitVec.getLsbD_zero
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,hz]
    simp [hi]
  have hz (x : Signal) : (0 : Signal) &&& x = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_and]
    have h0 : (0 : Signal).getLsbD j = false := BitVec.getLsbD_zero
    rw [h0, Bool.false_and]
  cases p <;> cases q
  · left
    change canon ((0 : Signal) &&& a) = 0
    rw [hz]
    exact canon_zero
  · left
    change canon ((0 : Signal) &&& ~~~a) = 0
    rw [hz]
    exact canon_zero
  · right
    change canon (~~~(0 : Signal) &&& a) = canon a
    rw [aa]
  · right
    change canon (~~~(0 : Signal) &&& ~~~a) = canon a
    rw [aa,canon_not]

theorem signed_gates_zero_r (p q : Bool) (a : Signal) :
    gate p q a 0 = 0 ∨ gate p q a 0 = canon a := by
  simpa [gate,BitVec.and_comm] using signed_gates_zero_l q p a


-- Small, literal closure checked by the kernel. Each node is independent.
private def AllRuledOut (k : Nat) : List (List Signal) → Prop
  | [] => True
  | v :: vs => (¬ certReachable k v) ∧ AllRuledOut k vs

private theorem ruledOutMember {k : Nat} {vs : List (List Signal)}
    (h : AllRuledOut k vs) : ∀ v ∈ vs, ¬ certReachable k v := by
  induction vs with
  | nil => simp
  | cons a vs ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.1
    · exact ih h.2 v hv

private theorem proveMinorNode (k : Nat) (v : List Signal) (ws : List (List Signal))
    (nd : v.Nodup) (bad : ttGoal ∉ v)
    (generated : rootMoves k v = ws) (ruled : AllRuledOut k ws) :
    ¬ certReachable (k+1) v := by
  intro h
  rcases certAdvance k v nd h with g | ⟨w,hw,hR⟩
  · exact bad g
  · exact ruledOutMember ruled _ (generated ▸ hw) hR

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_3_0 : ¬ certReachable 3 [0xa8a8a8a8,0xc0c0c0c0,0xff00ff00,0xffff0000] :=
  proveMinorNode 2 [0xa8a8a8a8,0xc0c0c0c0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_3_1 : ¬ certReachable 3 [0xaaaaaa00,0xff000000,0xcccccccc,0xf0f0f0f0] :=
  proveMinorNode 2 [0xaaaaaa00,0xff000000,0xcccccccc,0xf0f0f0f0] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_3_2 : ¬ certReachable 3 [0xc0c0c0c0,0xa8a8a8a8,0xff00ff00,0xffff0000] :=
  proveMinorNode 2 [0xc0c0c0c0,0xa8a8a8a8,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_3_3 : ¬ certReachable 3 [0xff000000,0xaaaaaa00,0xcccccccc,0xf0f0f0f0] :=
  proveMinorNode 2 [0xff000000,0xaaaaaa00,0xcccccccc,0xf0f0f0f0] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_0 : ¬ certReachable 4 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_1 : ¬ certReachable 4 [0xfafa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xfafa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_2 : ¬ certReachable 4 [0xfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_3 : ¬ certReachable 4 [0xffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_4 : ¬ certReachable 4 [0xee00ee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xee00ee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_5 : ¬ certReachable 4 [0xfa00fa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xfa00fa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_6 : ¬ certReachable 4 [0xfc00fc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xfc00fc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_7 : ¬ certReachable 4 [0xff00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xff00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_8 : ¬ certReachable 4 [0xe0e0e0e,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xe0e0e0e,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_9 : ¬ certReachable 4 [0xf0a0f0a,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf0a0f0a,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_10 : ¬ certReachable 4 [0xf0f0a0a,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf0f0a0a,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_11 : ¬ certReachable 4 [0xf0f0f00,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf0f0f00,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_12 : ¬ certReachable 4 [0x32323232,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0x32323232,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_13 : ¬ certReachable 4 [0x33223322,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0x33223322,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_14 : ¬ certReachable 4 [0x33332222,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0x33332222,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_15 : ¬ certReachable 4 [0x33333300,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0x33333300,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_16 : ¬ certReachable 4 [0x4c4c4c4c,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0x4c4c4c4c,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_17 : ¬ certReachable 4 [0x54545454,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0x54545454,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_18 : ¬ certReachable 4 [0x5500ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0x5500ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_19 : ¬ certReachable 4 [0x55555500,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0x55555500,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_20 : ¬ certReachable 4 [0x55ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0x55ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_21 : ¬ certReachable 4 [0x70707070,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0x70707070,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_22 : ¬ certReachable 4 [0xa8a8a8a8,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xa8a8a8a8,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xc0c0c0c0,0xa8a8a8a8,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_3_2,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_23 : ¬ certReachable 4 [0xaaaaaa00,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xaaaaaa00,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xff000000,0xaaaaaa00,0xcccccccc,0xf0f0f0f0]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_3_3,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_24 : ¬ certReachable 4 [0xc0c0c0c0,0xfcfcfcfc,0xaaaaaaaa,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xc0c0c0c0,0xfcfcfcfc,0xaaaaaaaa,0xff00ff00,0xffff0000] [[0xa8a8a8a8,0xc0c0c0c0,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_3_0,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_25 : ¬ certReachable 4 [0xc8c8c8c8,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xc8c8c8c8,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_26 : ¬ certReachable 4 [0xcc00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xcc00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_27 : ¬ certReachable 4 [0xcc0ccc0c,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xcc0ccc0c,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_28 : ¬ certReachable 4 [0xcc88cc88,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xcc88cc88,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_29 : ¬ certReachable 4 [0xcccc0c0c,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xcccc0c0c,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_30 : ¬ certReachable 4 [0xcccc8888,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xcccc8888,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_31 : ¬ certReachable 4 [0xcccccc00,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xcccccc00,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_32 : ¬ certReachable 4 [0xccccfcfc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xccccfcfc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_33 : ¬ certReachable 4 [0xccfcccfc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xccfcccfc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_34 : ¬ certReachable 4 [0xccff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xccff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_35 : ¬ certReachable 4 [0xe0e0e0e0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xe0e0e0e0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_36 : ¬ certReachable 4 [0xecececec,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xecececec,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_37 : ¬ certReachable 4 [0xee00ee00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xee00ee00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_38 : ¬ certReachable 4 [0xeeee0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xeeee0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_39 : ¬ certReachable 4 [0xf000ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xf000ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_40 : ¬ certReachable 4 [0xf030f030,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf030f030,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_41 : ¬ certReachable 4 [0xf0a0f0a0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf0a0f0a0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_42 : ¬ certReachable 4 [0xf0f03030,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf0f03030,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_43 : ¬ certReachable 4 [0xf0f0a0a0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf0f0a0a0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_44 : ¬ certReachable 4 [0xf0f0f000,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf0f0f000,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_45 : ¬ certReachable 4 [0xf0f0fcfc,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf0f0fcfc,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_46 : ¬ certReachable 4 [0xf0fcf0fc,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf0fcf0fc,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_47 : ¬ certReachable 4 [0xf0ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xf0ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_48 : ¬ certReachable 4 [0xf8f8f8f8,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xf8f8f8f8,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_49 : ¬ certReachable 4 [0xfa00fa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xfa00fa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_50 : ¬ certReachable 4 [0xfafa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xfafa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_51 : ¬ certReachable 4 [0xfc00fc00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xfc00fc00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_52 : ¬ certReachable 4 [0xfcfc0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xfcfc0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_53 : ¬ certReachable 4 [0xfcfcfcfc,0xc0c0c0c0,0xaaaaaaaa,0xff00ff00,0xffff0000] :=
  proveMinorNode 3 [0xfcfcfcfc,0xc0c0c0c0,0xaaaaaaaa,0xff00ff00,0xffff0000] [[0xa8a8a8a8,0xc0c0c0c0,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_3_0,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_54 : ¬ certReachable 4 [0xff000000,0xffffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0] :=
  proveMinorNode 3 [0xff000000,0xffffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0] [[0xaaaaaa00,0xff000000,0xcccccccc,0xf0f0f0f0]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_3_1,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_55 : ¬ certReachable 4 [0xff00aa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xff00aa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_56 : ¬ certReachable 4 [0xff0fff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xff0fff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_57 : ¬ certReachable 4 [0xff33ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xff33ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_58 : ¬ certReachable 4 [0xffaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xffaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_59 : ¬ certReachable 4 [0xffaaff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] :=
  proveMinorNode 3 [0xffaaff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_60 : ¬ certReachable 4 [0xffff0f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xffff0f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_61 : ¬ certReachable 4 [0xffff3300,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xffff3300,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_62 : ¬ certReachable 4 [0xffffaa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] :=
  proveMinorNode 3 [0xffffaa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_4_63 : ¬ certReachable 4 [0xffffff00,0xff000000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0] :=
  proveMinorNode 3 [0xffffff00,0xff000000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0] [[0xaaaaaa00,0xff000000,0xcccccccc,0xf0f0f0f0]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_3_1,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_0 : ¬ certReachable 5 [0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_1 : ¬ certReachable 5 [0xcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xf0f03030,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xf0f0fcfc,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_42,certNode_4_45,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_2 : ¬ certReachable 5 [0xf0f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xf0f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xcccc0c0c,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xccccfcfc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_29,certNode_4_32,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_3 : ¬ certReachable 5 [0xff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_4 : ¬ certReachable 5 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_5 : ¬ certReachable 5 [0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xf030f030,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xf0fcf0fc,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_40,certNode_4_46,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_6 : ¬ certReachable 5 [0xf000f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xf000f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xcc0ccc0c,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xccfcccfc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_27,certNode_4_33,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_7 : ¬ certReachable 5 [0xff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_8 : ¬ certReachable 5 [0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_9 : ¬ certReachable 5 [0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_10 : ¬ certReachable 5 [0xf000f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xf000f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xf0ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xffff0f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_47,certNode_4_60,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_11 : ¬ certReachable 5 [0xf0f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xf0f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xf000ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xff0fff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_39,certNode_4_56,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_12 : ¬ certReachable 5 [0x22222222,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0x22222222,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_13 : ¬ certReachable 5 [0x30303030,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0x30303030,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_14 : ¬ certReachable 5 [0x33003300,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0x33003300,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xccff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xffff3300,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_34,certNode_4_61,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_15 : ¬ certReachable 5 [0x33330000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0x33330000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xcc00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xff33ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_26,certNode_4_57,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_16 : ¬ certReachable 5 [0x44444444,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0x44444444,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_17 : ¬ certReachable 5 [0x50505050,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0x50505050,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_18 : ¬ certReachable 5 [0x55005500,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0x55005500,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_19 : ¬ certReachable 5 [0x55550000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0x55550000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_20 : ¬ certReachable 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0x70707070,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xf8f8f8f8,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_21,certNode_4_48,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_21 : ¬ certReachable 5 [0xa0a0a0a0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xa0a0a0a0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0x4c4c4c4c,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xecececec,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_16,certNode_4_36,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_22 : ¬ certReachable 5 [0xaa00aa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xaa00aa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0x55ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xffffaa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_20,certNode_4_62,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_23 : ¬ certReachable 5 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0x5500ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xffaaff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_18,certNode_4_59,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_24 : ¬ certReachable 5 [0xc0c0c0c0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xc0c0c0c0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xfcfcfcfc,0xc0c0c0c0,0xaaaaaaaa,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_53,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_25 : ¬ certReachable 5 [0xcc00cc00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xcc00cc00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_26 : ¬ certReachable 5 [0xcccc0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xcccc0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_27 : ¬ certReachable 5 [0xeeeeeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xeeeeeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xe0e0e0e0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xe0e0e0e,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xee00ee00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xee00ee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xeeee0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_35,certNode_4_8,certNode_4_37,certNode_4_4,certNode_4_38,certNode_4_0,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_28 : ¬ certReachable 5 [0xf000f000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xf000f000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_29 : ¬ certReachable 5 [0xf0f00000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xf0f00000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_30 : ¬ certReachable 5 [0xfafafafa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xfafafafa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xfa00fa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xfa00fa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xfafa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xfafa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xc8c8c8c8,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x32323232,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_49,certNode_4_5,certNode_4_50,certNode_4_1,certNode_4_25,certNode_4_12,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_31 : ¬ certReachable 5 [0xfcfcfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xfcfcfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xfc00fc00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xfc00fc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xfcfc0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xa8a8a8a8,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x54545454,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xc0c0c0c0,0xfcfcfcfc,0xaaaaaaaa,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_51,certNode_4_6,certNode_4_52,certNode_4_2,certNode_4_22,certNode_4_17,certNode_4_24,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_32 : ¬ certReachable 5 [0xff000000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xff000000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xffffff00,0xff000000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_63,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_33 : ¬ certReachable 5 [0xffaaffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xffaaffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xffaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[0xcc88cc88,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x33223322,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xf0a0f0a0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xf0a0f0a,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_58,certNode_4_3,certNode_4_28,certNode_4_13,certNode_4_41,certNode_4_9,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_34 : ¬ certReachable 5 [0xffccffcc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xffccffcc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_35 : ¬ certReachable 5 [0xfff0fff0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xfff0fff0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_36 : ¬ certReachable 5 [0xffffaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xffffaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xcccc8888,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x33332222,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xf0f0a0a0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xf0f0a0a,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xff00aa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[0xff00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_30,certNode_4_14,certNode_4_43,certNode_4_10,certNode_4_55,certNode_4_7,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_37 : ¬ certReachable 5 [0xffffcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xffffcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_38 : ¬ certReachable 5 [0xfffff0f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xfffff0f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) True.intro

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem certNode_5_39 : ¬ certReachable 5 [0xffffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] :=
  proveMinorNode 4 [0xffffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] [[0xaaaaaa00,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x55555500,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xcccccc00,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x33333300,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xf0f0f000,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xf0f0f00,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[0xff000000,0xffffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_4_23,certNode_4_19,certNode_4_31,certNode_4_15,certNode_4_44,certNode_4_11,certNode_4_54,True.intro⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem signedMinorBlocked : ¬ certReachable 6 inputs :=
  proveMinorNode 5 inputs [[0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x22222222,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x44444444,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xeeeeeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xa0a0a0a0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x50505050,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xfafafafa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xaa00aa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x55005500,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xffaaffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x55550000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xffffaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xc0c0c0c0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x30303030,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xfcfcfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xcc00cc00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x33003300,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xffccffcc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xcccc0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0x33330000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xffffcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xf000f000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xf000f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xf000f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xfff0fff0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xf0f00000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xf0f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xf0f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xfffff0f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xff000000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[0xffffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨certNode_5_20,certNode_5_12,certNode_5_16,certNode_5_27,certNode_5_21,certNode_5_8,certNode_5_17,certNode_5_30,certNode_5_22,certNode_5_4,certNode_5_18,certNode_5_33,certNode_5_23,certNode_5_0,certNode_5_19,certNode_5_36,certNode_5_24,certNode_5_9,certNode_5_13,certNode_5_31,certNode_5_25,certNode_5_5,certNode_5_14,certNode_5_34,certNode_5_26,certNode_5_1,certNode_5_15,certNode_5_37,certNode_5_28,certNode_5_6,certNode_5_10,certNode_5_35,certNode_5_29,certNode_5_2,certNode_5_11,certNode_5_38,certNode_5_32,certNode_5_3,certNode_5_7,certNode_5_39,True.intro⟩



open PEqualNP.Outside.L_meta_15291_aux.Signed

def yGate (g : Signed.Gate) (w : List Signal) : Signal :=
  let a := flip g.left.inverted (w.getD g.left.ix 0)
  let b := flip g.right.inverted (w.getD g.right.ix 0)
  if g.andGate then a &&& b else a ||| b

def yRun (gs : List Signed.Gate) (w : List Signal) : List Signal :=
  gs.foldl (fun w g => w ++ [yGate g w]) w

theorem yRun_cons (g : Signed.Gate) (gs : List Signed.Gate) (w : List Signal) :
    yRun (g::gs) w = yRun gs (w ++ [yGate g w]) := rfl

theorem yRun_length (gs : List Signed.Gate) (w : List Signal) :
    (yRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [yRun]
  | cons g gs ih =>
    rw [yRun_cons,ih]
    simp
    omega

def read (i : Fin 32) (u : Signal) : Bool := u.getLsbD i.val

theorem bv_read (i : Fin 32) (w : List Signal) (j : Nat) :
    (w.map (read i)).getD j false = read i (w.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? <;> simp [read]

theorem read_flip (i : Fin 32) (p : Bool) (a : Signal) :
    read i (flip p a) = (read i a ^^ p) := by
  cases p <;> simp [read,flip,i.isLt]

theorem yStep (i : Fin 32) (g : Signed.Gate) (w : List Signal) :
    read i (yGate g w) = g.eval (w.map (read i)) := by
  have ha (a b : Signal) : read i (a &&& b) = (read i a && read i b) := BitVec.getLsbD_and
  have ho (a b : Signal) : read i (a ||| b) = (read i a || read i b) := BitVec.getLsbD_or
  obtain ⟨kind,l,r⟩ := g
  cases kind <;> simp only [yGate,Signed.Gate.eval,Signed.Ref.read,reduceCtorEq,
    ite_false,ite_true,ha,ho,read_flip,bv_read]

theorem yRun_eval (i : Fin 32) (gs : List Signed.Gate) (w : List Signal) :
    (yRun gs w).map (read i) = Signed.wires gs (w.map (read i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [yRun_cons,ih,List.map_append]
    simp only [List.map_cons,List.map_nil,yStep]
    rfl

theorem signedGate_repr (g : Signed.Gate) (w : List Signal) :
    ∃ p q, canon (yGate g w) =
      gate p q (canon (w.getD g.left.ix 0)) (canon (w.getD g.right.ix 0)) := by
  let a := w.getD g.left.ix 0
  let b := w.getD g.right.ix 0
  let p := g.left.inverted ^^ a.getLsbD 0
  let q := g.right.inverted ^^ b.getLsbD 0
  have hA : flip g.left.inverted a = flip p (canon a) := uncanon_flip _ _
  have hB : flip g.right.inverted b = flip q (canon b) := uncanon_flip _ _
  cases op : g.andGate
  · refine ⟨!p,!q,?_⟩
    change canon (if g.andGate then (flip g.left.inverted a &&& flip g.right.inverted b)
      else (flip g.left.inverted a ||| flip g.right.inverted b)) =
      canon (flip (!p) (canon a) &&& flip (!q) (canon b))
    rw [hA,hB,op]
    simp only [Bool.false_eq_true,ite_false]
    have hf (c : Bool) (x : Signal) : flip (!c) x = ~~~(flip c x) := by
      cases c <;> simp [flip,BitVec.not_not]
    rw [hf,hf,← BitVec.not_or,canon_not]
  · refine ⟨p,q,?_⟩
    change canon (if g.andGate then (flip g.left.inverted a &&& flip g.right.inverted b)
      else (flip g.left.inverted a ||| flip g.right.inverted b)) =
      canon (flip p (canon a) &&& flip q (canon b))
    rw [hA,hB,op]
    rfl

theorem get_canon (w : List Signal) (i : ℕ) :
    canon (w.getD i 0) = 0 ∨ canon (w.getD i 0) ∈ w.map canon := by
  by_cases h : i<w.length
  · right
    rw [List.getD_eq_getElem w 0 h]
    exact List.mem_map.mpr ⟨w[i],List.getElem_mem _,rfl⟩
  · left
    rw [List.getD_eq_default w 0 (by omega),canon_zero]

theorem signedGate_fresh (g : Signed.Gate) (w : List Signal)
    (hnz : canon (yGate g w) ≠ 0) (hn : canon (yGate g w) ∉ w.map canon) :
    ∃ a∈w.map canon, ∃ b∈w.map canon, ∃ p q,
      a≠b ∧ a≠0 ∧ b≠0 ∧ canon (yGate g w) = gate p q a b := by
  obtain ⟨p,q,h⟩ := signedGate_repr g w
  let a := canon (w.getD g.left.ix 0)
  let b := canon (w.getD g.right.ix 0)
  have ia : canon a = a := canon_idempotent _
  have ib : canon b = b := canon_idempotent _
  change canon (yGate g w)=gate p q a b at h
  have ha : a ≠ 0 := by
    intro ha
    rw [h,ha] at hnz hn
    rcases signed_gates_zero_l p q b with h0 | hb
    · exact hnz h0
    · rcases get_canon w g.right.ix with hz | hmem
      · exact hnz (hb.trans (ib.trans hz))
      · rw [hb,ib] at hn
        exact hn hmem
  have hb : b ≠ 0 := by
    intro hb
    rw [h,hb] at hnz hn
    rcases signed_gates_zero_r p q a with h0 | ha'
    · exact hnz h0
    · rcases get_canon w g.left.ix with hz | hmem
      · exact hnz (ha'.trans (ia.trans hz))
      · rw [ha',ia] at hn
        exact hn hmem
  have am : a ∈ w.map canon := (get_canon w g.left.ix).resolve_left ha
  have bm : b ∈ w.map canon := (get_canon w g.right.ix).resolve_left hb
  refine ⟨a,am,b,bm,p,q,?_,ha,hb,h⟩
  intro ab
  rw [h,ab] at hnz hn
  rcases signed_gates_same p q b with hz | hv
  · exact hnz hz
  · exact hn (by simpa [hv,ib] using bm)

theorem signed_extract (gs : List Signed.Gate) (w : List Signal)
    (h : ttGoal ∈ (yRun gs w).map canon) :
    ∃ k S, k≤gs.length ∧ Live k S ∧ ∀ a∈S, a∈w.map canon := by
  induction gs generalizing w with
  | nil =>
    exact ⟨0,{ttGoal},by simp, rfl,by simpa [yRun] using h⟩
  | cons g gs ih =>
    rw [yRun_cons] at h
    obtain ⟨k,S,hle,hl,sub⟩ := ih _ h
    simp only [List.map_append,List.map_cons,List.map_nil,List.mem_append,
      List.mem_singleton] at sub
    let z := canon (yGate g w)
    by_cases hz : z∈S
    · by_cases havez : z∈w.map canon
      · exact ⟨k,S,by simp; omega, hl, fun a ha => (sub a ha).elim id (fun eq => eq ▸ havez)⟩
      · have nge := live_nonzero hl z hz
        obtain ⟨a,am,b,bm,p,q,ab,na,nb,eq⟩ := signedGate_fresh g w nge havez
        have e : z=gate p q a b := eq
        let U := S.erase z
        have hm : insert z U=S := Finset.insert_erase hz
        have old : ∀ a∈U, a∈w.map canon := by
          intro a ha
          rcases Finset.mem_erase.mp ha with ⟨ne,mem⟩
          exact (sub a mem).resolve_right ne
        have nmem : gate p q a b∉insert a (insert b U) := by
          rw [←e]
          intro h
          rcases Finset.mem_insert.mp h with h1 | h
          · exact havez (h1 ▸ am)
          rcases Finset.mem_insert.mp h with h2 | h
          · exact havez (h2 ▸ bm)
          exact havez (old _ h)
        refine ⟨k+1,insert a (insert b U),by simp; omega,?_,?_⟩
        · exact ⟨U,a,b,p,q,ab,na,nb,e ▸ nge,nmem,rfl,e ▸ (hm.symm ▸ hl)⟩
        · intro a' h
          rcases Finset.mem_insert.mp h with rfl | h
          · exact am
          rcases Finset.mem_insert.mp h with rfl | h
          · exact bm
          exact old _ h
    · refine ⟨k,S,by simp; omega,hl,?_⟩
      intro a ha
      apply (sub a ha).resolve_right
      intro eq
      have az : a = z := eq
      apply hz
      rw [←az]
      exact ha

def ofRow (i : Fin 32) : List Bool := List.ofFn fun j : Fin 5 => i.val.testBit j.val
theorem inputs_row : ∀ i : Fin 32, inputs.map (read i) = ofRow i := by decide +kernel
theorem goal_row : ∀ i : Fin 32, read i ttGoal = minor (ofRow i) := by decide +kernel
theorem inputs_Nodup : inputs.Nodup := by decide +kernel
theorem inputs_canon : inputs.map canon = inputs := by decide +kernel
theorem goal_canon : canon ttGoal = ttGoal := by decide +kernel

theorem root_live_signals {gs : List Signed.Gate} (out : Signed.Ref)
    (o : out.ix < 5+gs.length)
    (h : ∀ xs : List Bool, xs.length = 5 → out.read (Signed.wires gs xs) = minor xs) :
    ∃ k S, k≤gs.length ∧ Live k S ∧ ∀ a∈S, a∈inputs := by
  let w := yRun gs inputs
  let z := w.getD out.ix 0
  have e : flip out.inverted z = ttGoal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 32 := ⟨j,hj⟩
    have hh := h (ofRow i) (by simp [ofRow])
    change read i (flip out.inverted z) = read i ttGoal
    rw [read_flip,←bv_read,show w.map (read i)=Signed.wires gs (inputs.map (read i)) from yRun_eval i gs inputs,
      inputs_row,goal_row]
    exact hh
  have zm : z ∈ w := by
    have ol : out.ix<w.length := by rw [show w.length=inputs.length+gs.length from yRun_length gs inputs]; exact o
    change w.getD out.ix 0 ∈ w
    rw [List.getD_eq_getElem w 0 ol]
    exact List.getElem_mem _
  have gz : canon z = ttGoal := by rw [←canon_flip out.inverted z,e,goal_canon]
  have gm : ttGoal∈w.map canon := gz ▸ (List.mem_map.mpr ⟨z,zm,rfl⟩ : canon z∈w.map canon)
  simpa only [inputs_canon] using signed_extract gs inputs gm

private def pivotPairs : List (Fin 32 × Fin 32) := [(11,10),(11,9),(13,9),(11,3),(19,3)]

private theorem raw_has_pivot (x : Signal) (hm : x ∈ inputs) :
    ∃ q ∈ pairs, ∀ z ∈ inputs.erase x, read q.1 z = read q.2 z := by
  have bRequired : inputs.all (fun x => pivotPairs.any (fun q =>
      (inputs.erase x).all (fun z => read q.1 z == read q.2 z))) = true := by
      decide +kernel
  obtain ⟨q,qm,hq⟩ := List.any_eq_true.mp (List.all_eq_true.mp bRequired x hm)
  have inside : pivotPairs.all (fun q => decide (q∈pairs)) = true := by decide +kernel
  exact ⟨q,of_decide_eq_true (List.all_eq_true.mp inside q qm),
    fun z hz => beq_iff_eq.mp (List.all_eq_true.mp hq z hz)⟩

private theorem root_has_all_raw {k S} (hl : Live k S) (sub : ∀ a∈S, a∈inputs) :
    inputs.toFinset = S := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hm : x ∈ inputs := List.mem_toFinset.mp hx
    by_contra hn
    obtain ⟨q,hq,hqu⟩ := raw_has_pivot x hm
    obtain ⟨z,hz,hsep⟩ := liveSeparates hl q hq
    have ne : z≠x := fun he => hn (he ▸ hz)
    exact hsep (hqu z ((List.mem_erase_of_ne ne).mpr (sub _ hz)))
  · intro x hx
    exact List.mem_toFinset.mpr (sub x hx)


theorem signed_minor_bound (blocked : ¬ certReachable 6 inputs) : Signed.SignedAtLeast 5 minor 7 := by
  intro gs out hd ho h
  by_contra small
  obtain ⟨k,S,hle,hl,sub⟩ := root_live_signals out ho h
  have eq : inputs.toFinset = S := root_has_all_raw hl sub
  have hk : k ≤ 6 := by omega
  exact blocked ⟨k,hk,eq.symm ▸ hl⟩


end PEqualNP.Outside.L_meta_15291_aux.Threshold


-- Exact assigned theorem.
theorem PEqualNP.Outside.L_meta_15291 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937053354 * 2 ^ 32 + 3903367168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937053354 * 2 ^ 32 + 3903367168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_15291_aux.exact_from_signed_minor
    (PEqualNP.Outside.L_meta_15291_aux.Threshold.signed_minor_bound
      PEqualNP.Outside.L_meta_15291_aux.Threshold.signedMinorBlocked)
