import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12339_aux.Signed

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

end PEqualNP.Outside.L_meta_12339_aux.Signed

namespace PEqualNP.Outside.L_meta_12339_aux.Signed

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

end PEqualNP.Outside.L_meta_12339_aux.Signed

namespace PEqualNP.Outside.L_meta_12339_aux.Signed

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

end PEqualNP.Outside.L_meta_12339_aux.Signed

namespace PEqualNP.Outside.L_meta_12339_aux.Signed
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

end PEqualNP.Outside.L_meta_12339_aux.Signed

namespace PEqualNP.Outside.L_meta_12339_aux.Signed
theorem fanout_cons (g : Gate) (gs : List Gate) (i : Nat) :
    Fanout (g :: gs) i = g.pins.count i + Fanout gs i := by
  unfold Fanout
  change (g.pins ++ uses gs).count i = _
  simp [List.count_append]


end PEqualNP.Outside.L_meta_12339_aux.Signed

namespace PEqualNP.Outside.L_meta_12339_aux.Signed

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

end PEqualNP.Outside.L_meta_12339_aux.Signed

namespace PEqualNP.Outside.L_meta_12339_aux.Signed

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

end PEqualNP.Outside.L_meta_12339_aux.Signed
namespace PEqualNP.Outside.L_meta_12339_aux.Threshold

abbrev Signal := BitVec 16
def flip (n : Bool) (x : Signal) := if n then ~~~x else x
def canon (x : Signal) := flip (x.getLsbD 0) x
def gate (p q : Bool) (a b : Signal) := canon (flip p a &&& flip q b)

def ttGoal : Signal := 0xfee8
def inputs : List Signal := [0xaaaa,0xcccc,0xf0f0,0xff00]
def pairs : List (Fin 16 × Fin 16) := [(3, 2), (5, 4), (9, 8), (3, 1), (6, 4), (10, 8), (5, 1), (6, 2), (12, 8), (9, 1), (10, 2), (12, 4)]

def sep (v : List Signal) (r : Fin 16 × Fin 16) : Bool :=
  v.any (fun u => u.getLsbD r.1.val != u.getLsbD r.2.val)


def maskAt (d : Fin 4) : Signal :=
  ([0x114,0x112,0x106,0x16] : List Signal).getD d.val 0

def shift (d : Fin 4) := 2 ^ (d.val)

def oneCover (d : Fin 4) (x : Signal) : Signal :=
  (x ^^^ (x >>> shift d)) &&& maskAt d

def unionAt (d : Fin 4) : List Signal → Signal
  | [] => 0
  | a::v => oneCover d a ||| unionAt d v

def cover (v : List Signal) : Bool :=
  (List.finRange 4).all (fun d => unionAt d v == maskAt d)


def bits : List Bool := [false,true]

def retain (a b : Signal) (ka kb : Bool) (x : Signal) :=
  (x != a || ka) && (x != b || kb)

def search : ℕ → List Signal → Bool
  | 0,v => v == [ttGoal]
  | k+1,v =>
    if v.length > k+2 then false else
      (v == [ttGoal]) || (v.any fun a => v.any fun b =>
        if ¬ a.toNat < b.toNat then false else
          bits.any fun p => bits.any fun q =>
            let z := gate p q a b
            if z=0 ∨ z∈v then false else
              bits.any fun ka => bits.any fun kb =>
                let w := z :: v.filter (retain a b ka kb)
                decide (w.length ≤ k+1) && cover w && search k w)

def Live : Nat → Finset Signal → Prop
  | 0,S => S = {ttGoal}
  | k+1,S => ∃ (U : Finset Signal) (a b : Signal) (p q : Bool),
      a.toNat < b.toNat ∧ a ≠ 0 ∧ b ≠ 0 ∧ gate p q a b ≠ 0 ∧ gate p q a b ∉ S ∧
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

theorem flip_obs_eq (p : Bool) (a : Signal) (i j : Fin 16)
    (h : a.getLsbD i = a.getLsbD j) :
    (flip p a).getLsbD i = (flip p a).getLsbD j := by
  cases p
  · exact h
  · simpa [flip,BitVec.getLsbD_not,i.isLt,j.isLt] using congrArg Bool.not h

theorem gate_obs_eq (p q : Bool) (a b : Signal) (i j : Fin 16)
    (ha : a.getLsbD i = a.getLsbD j) (hb : b.getLsbD i = b.getLsbD j) :
    (gate p q a b).getLsbD i = (gate p q a b).getLsbD j := by
  apply flip_obs_eq
  simp only [BitVec.getLsbD_and]
  rw [flip_obs_eq p a i j ha, flip_obs_eq q b i j hb]

theorem target_covers : ∀ r ∈ pairs, ttGoal.getLsbD r.1 ≠ ttGoal.getLsbD r.2 := by
  decide +kernel

theorem liveSeparates {k S} (h : Live k S) (r : Fin 16 × Fin 16) (hr : r ∈ pairs) :
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


theorem pair_mask : ∀ (d : Fin 4) (j : Fin 16),
    (maskAt d).getLsbD j.val = true →
    j.val + shift d < 16 ∧ (Fin.ofNat 16 (j.val+shift d),j) ∈ pairs := by
  decide +kernel

theorem oneCover_bit (d : Fin 4) (x : Signal) (j : ℕ) :
    (oneCover d x).getLsbD j =
      ((x.getLsbD j ^^ x.getLsbD (j+shift d)) && (maskAt d).getLsbD j) := by
  simp [oneCover,BitVec.getLsbD_ushiftRight,Nat.add_comm]

theorem at_false (d : Fin 4) (j : ℕ) (v : List Signal)
    (h : (maskAt d).getLsbD j = false) : (unionAt d v).getLsbD j = false := by
  induction v with
  | nil => simp [unionAt]
  | cons a v ih => simp [unionAt,oneCover_bit,h,ih]

theorem at_true (d : Fin 4) (j : ℕ) (v : List Signal)
    (h : (maskAt d).getLsbD j = true) (x : Signal) (hm : x∈v)
    (hn : x.getLsbD (j+shift d) ≠ x.getLsbD j) :
    (unionAt d v).getLsbD j = true := by
  induction v with
  | nil => simp at hm
  | cons a v ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · have hxor : x.getLsbD j ^^ x.getLsbD (j+shift d) = true := by
        generalize x.getLsbD j = p at hn ⊢
        generalize x.getLsbD (j+shift d) = q at hn ⊢
        cases p <;> cases q <;> simp_all
      have he : (oneCover d x).getLsbD j = true := by
        rw [oneCover_bit,h,Bool.and_true]
        exact hxor
      change ((oneCover d x ||| unionAt d v).getLsbD j) = true
      rw [BitVec.getLsbD_or,he,Bool.true_or]
    · simp [unionAt,ih hm]

theorem live_cover {k S} {v : List Signal} (h : Live k S) (e : v.toFinset = S) :
    cover v = true := by
  apply List.all_eq_true.mpr
  intro d hd
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases hh : (maskAt d).getLsbD j = true
  · let i : Fin 16 := ⟨j,hj⟩
    obtain ⟨b,m⟩ := pair_mask d i hh
    obtain ⟨x,xm,xd⟩ := liveSeparates h _ m
    rw [←e,List.mem_toFinset] at xm
    have o : (Fin.ofNat 16 (i.val+shift d)).val = j+shift d := by
      simp [Fin.ofNat,Nat.mod_eq_of_lt b,i]
    rw [o] at xd
    rw [hh,at_true d j v hh x xm xd]
  · have hf : (maskAt d).getLsbD j = false := by simpa using hh
    exact (at_false d j v hf).trans hf.symm

theorem keep_exact {a b : Signal} {U : Finset Signal} {v : List Signal}
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

theorem search_complete {m S} (h : Live m S) (k : Nat) (hk : m ≤ k)
    (v : List Signal) (nd : v.Nodup) (e : v.toFinset = S) : search k v = true := by
  induction k generalizing m S v with
  | zero =>
    have hm : m=0 := by omega
    subst m
    have eq : S = {ttGoal} := h
    have hvl : v.length=1 := by
      rw [←List.toFinset_card_of_nodup nd,e,eq]
      simp
    obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hvl
    have ee : a=ttGoal := by simpa [eq] using e
    simp [search,ee]
  | succ k ih =>
    have sz := branch_size h
    rw [←e,List.toFinset_card_of_nodup nd] at sz
    have bound : ¬ v.length > k+2 := by omega
    cases m with
    | zero =>
      have eq : S = {ttGoal} := h
      have hvl : v.length=1 := by
        rw [←List.toFinset_card_of_nodup nd,e,eq]
        simp
      obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hvl
      have ee : a=ttGoal := by simpa [eq] using e
      simp [search,ee]
    | succ m =>
      obtain ⟨U,a,b,p,q,hlt,_,_,nz,notv,he,ht⟩ := h
      have ab : a ≠ b := fun hh => (Nat.lt_irrefl a.toNat) (hh ▸ hlt)
      let z := gate p q a b
      let ka : Bool := decide (a∈U)
      let kb : Bool := decide (b∈U)
      let w := z :: v.filter (retain a b ka kb)
      have ev := e.trans he
      have ha : a∈v := by rw [←List.mem_toFinset,ev]; simp
      have hb : b∈v := by rw [←List.mem_toFinset,ev]; simp
      have notvv : z∉v := by rw [←List.mem_toFinset,e]; exact notv
      have wn : w.Nodup := by
        refine List.nodup_cons.mpr ⟨?_,nd.filter _⟩
        intro wmem
        exact notvv (List.mem_filter.mp wmem).1
      have ew : w.toFinset = insert z U := by
        simp only [w,List.toFinset_cons]
        exact congrArg (insert z) (keep_exact ab ev)
      have wm := branch_size ht
      rw [←ew,List.toFinset_card_of_nodup wn] at wm
      have wlen : w.length ≤ k+1 := by omega
      have keepGood := live_cover ht ew
      have nextGood := ih ht (by omega) w wn ew
      have hbts : ∀ c : Bool, c∈bits := by intro c; cases c <;> simp [bits]
      simp only [search,bound,ite_false,Bool.or_eq_true]
      right
      refine List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
      simp only [hlt,not_true_eq_false,ite_false]
      refine List.any_eq_true.mpr ⟨p,hbts p,List.any_eq_true.mpr ⟨q,hbts q,?_⟩⟩
      have ndrop : ¬ (gate p q a b = 0 ∨ gate p q a b∈v) := not_or.mpr ⟨nz,notvv⟩
      simp only [ndrop,ite_false]
      refine List.any_eq_true.mpr ⟨ka,hbts ka,List.any_eq_true.mpr ⟨kb,hbts kb,?_⟩⟩
      change (decide (w.length ≤ k+1) && cover w && search k w) = true
      simp [wlen,keepGood,nextGood]


open PEqualNP.Outside.L_meta_12339_aux.Signed

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

def read (i : Fin 16) (u : Signal) : Bool := u.getLsbD i.val

theorem bv_read (i : Fin 16) (w : List Signal) (j : Nat) :
    (w.map (read i)).getD j false = read i (w.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? <;> simp [read]

theorem read_flip (i : Fin 16) (p : Bool) (a : Signal) :
    read i (flip p a) = (read i a ^^ p) := by
  cases p <;> simp [read,flip,i.isLt]

theorem yStep (i : Fin 16) (g : Signed.Gate) (w : List Signal) :
    read i (yGate g w) = g.eval (w.map (read i)) := by
  have ha (a b : Signal) : read i (a &&& b) = (read i a && read i b) := BitVec.getLsbD_and
  have ho (a b : Signal) : read i (a ||| b) = (read i a || read i b) := BitVec.getLsbD_or
  obtain ⟨kind,l,r⟩ := g
  cases kind <;> simp only [yGate,Signed.Gate.eval,Signed.Ref.read,reduceCtorEq,
    ite_false,ite_true,ha,ho,read_flip,bv_read]

theorem yRun_eval (i : Fin 16) (gs : List Signed.Gate) (w : List Signal) :
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
        · have nc : a.toNat ≠ b.toNat := fun ff => ab (BitVec.eq_of_toNat_eq ff)
          rcases lt_or_gt_of_ne nc with hlt | hgt
          · exact ⟨U,a,b,p,q,hlt,na,nb,e ▸ nge,nmem,rfl,e ▸ (hm.symm ▸ hl)⟩
          · have eg : gate p q a b = gate q p b a := by simp [gate,BitVec.and_comm]
            have ez := e.trans eg
            have hc : insert a (insert b U) = insert b (insert a U) := Finset.insert_comm _ _ _
            refine ⟨U,b,a,q,p,hgt,nb,na,ez ▸ nge,?_,hc,ez ▸ (hm.symm ▸ hl)⟩
            simpa only [←eg,←hc] using nmem
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

def ofRow (i : Fin 16) : List Bool := List.ofFn fun j : Fin 4 => i.val.testBit j.val
def thresholdTwo (xs : List Bool) :=
  let a := xs.getD 0 false
  let b := xs.getD 1 false
  let c := xs.getD 2 false
  let d := xs.getD 3 false
  (a && b) || (a && c) || (a && d) || (b && c) || (b && d) || (c && d)

theorem inputs_row : ∀ i : Fin 16, inputs.map (read i) = ofRow i := by decide +kernel
theorem goal_row : ∀ i : Fin 16, read i ttGoal = thresholdTwo (ofRow i) := by decide +kernel
theorem inputs_Nodup : inputs.Nodup := by decide +kernel
theorem inputs_canon : inputs.map canon = inputs := by decide +kernel
theorem goal_canon : canon ttGoal = ttGoal := by decide +kernel

theorem root_live_signals {gs : List Signed.Gate} (out : Signed.Ref)
    (o : out.ix < 4+gs.length)
    (h : ∀ xs : List Bool, xs.length = 4 → out.read (Signed.wires gs xs) = thresholdTwo xs) :
    ∃ k S, k≤gs.length ∧ Live k S ∧ ∀ a∈S, a∈inputs := by
  let w := yRun gs inputs
  let z := w.getD out.ix 0
  have e : flip out.inverted z = ttGoal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 16 := ⟨j,hj⟩
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

private theorem raw_has_pivot (x : Signal) (hm : x ∈ inputs) :
    ∃ q ∈ pairs, ∀ z ∈ inputs.erase x, read q.1 z = read q.2 z := by
  have bRequired : inputs.all (fun x => pairs.any (fun q =>
      (inputs.erase x).all (fun z => read q.1 z == read q.2 z))) = true := by
      decide +kernel
  obtain ⟨q,qm,hq⟩ := List.any_eq_true.mp (List.all_eq_true.mp bRequired x hm)
  exact ⟨q,qm,fun z hz => beq_iff_eq.mp (List.all_eq_true.mp hq z hz)⟩

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

set_option maxHeartbeats 4000000 in
theorem root_signed_bound (root_negative : search 6 inputs = false) : Signed.SignedAtLeast 4 thresholdTwo 7 := by
  intro gs out hd ho h
  by_contra small
  obtain ⟨k,S,hle,hl,sub⟩ := root_live_signals out ho h
  have eq : inputs.toFinset = S := root_has_all_raw hl sub
  have hk : k ≤ 6 := by omega
  have ht : search 6 inputs = true := search_complete hl 6 hk inputs inputs_Nodup eq
  exact Bool.noConfusion (root_negative.symm.trans ht)

end PEqualNP.Outside.L_meta_12339_aux.Threshold

namespace PEqualNP.Outside.L_meta_12339_aux

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276682472 * 2 ^ 32 + 4276650112)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def core5 (xs : List Bool) : Bool :=
  ((xs.getD 0 false && xs.getD 1 false) && xs.getD 2 false) ||
  (xs.getD 4 false && Threshold.thresholdTwo xs)

private def full6 (xs : List Bool) : Bool :=
  ((xs.getD 0 false && xs.getD 1 false) && xs.getD 2 false) ||
  ((xs.getD 4 false || xs.getD 5 false) && Threshold.thresholdTwo xs)

private theorem threshold_essential : Signed.Essential 4 Threshold.thresholdTwo := by
  apply Signed.lift_essential_table
  decide +kernel

private theorem core_essential : Signed.Essential 5 core5 := by
  apply Signed.lift_essential_table
  decide +kernel

private theorem full_essential : Signed.Essential 6 full6 := by
  apply Signed.lift_essential_table
  decide +kernel

private theorem threshold_append (xs : List Bool) (val : Bool) (hi : 4 ≤ xs.length) :
    Threshold.thresholdTwo (xs ++ [val]) = Threshold.thresholdTwo xs := by
  dsimp only [Threshold.thresholdTwo]
  rw [List.getD_append _ _ _ _ (by omega : 0 < xs.length),
      List.getD_append _ _ _ _ (by omega : 1 < xs.length),
      List.getD_append _ _ _ _ (by omega : 2 < xs.length),
      List.getD_append _ _ _ _ (by omega : 3 < xs.length)]

private theorem core_cofactor (xs : List Bool) (hi : xs.length = 4) :
    core5 (xs.insertIdx 4 true) = Threshold.thresholdTwo xs := by
  have h : xs.insertIdx 4 true = xs ++ [true] := by rw [←hi,List.insertIdx_length_self]
  rw [h,core5,threshold_append _ _ (by omega),
    List.getD_append _ _ _ _ (by omega : 0 < xs.length),
    List.getD_append _ _ _ _ (by omega : 1 < xs.length),
    List.getD_append _ _ _ _ (by omega : 2 < xs.length),
    List.getD_append_right _ _ _ _ (by omega : xs.length ≤ 4)]
  simp only [hi,Nat.sub_self,List.getD_cons_zero,Bool.true_and]
  dsimp only [Threshold.thresholdTwo]
  generalize xs.getD 0 false = a
  generalize xs.getD 1 false = b
  generalize xs.getD 2 false = c
  generalize xs.getD 3 false = d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem full_cofactor (xs : List Bool) (hi : xs.length = 5) :
    full6 (xs.insertIdx 5 false) = core5 xs := by
  have h : xs.insertIdx 5 false = xs ++ [false] := by rw [←hi,List.insertIdx_length_self]
  rw [h,full6,core5,threshold_append _ _ (by omega),
    List.getD_append _ _ _ _ (by omega : 0 < xs.length),
    List.getD_append _ _ _ _ (by omega : 1 < xs.length),
    List.getD_append _ _ _ _ (by omega : 2 < xs.length),
    List.getD_append _ _ _ _ (by omega : 4 < xs.length),
    List.getD_append_right _ _ _ _ (by omega : xs.length ≤ 5)]
  simp [hi]

private theorem signed_full_ge9
    (cert : Threshold.search 6 Threshold.inputs = false) :
    Signed.SignedAtLeast 6 full6 9 := by
  have h4 := Threshold.root_signed_bound cert
  have h5 : Signed.SignedAtLeast 5 core5 8 :=
    Signed.lift_essential_minor (i:=4) (value:=true) (by decide) (by decide)
      core_essential threshold_essential h4 core_cofactor
  exact Signed.lift_essential_minor (i:=5) (value:=false) (by decide) (by decide)
    full_essential core_essential h5 full_cofactor

set_option maxHeartbeats 2000000 in
private theorem full_truth : ∀ x : Fin 6 → Bool, full6 (List.ofFn x) = target x := by
  decide +kernel

private def upper : Circuit :=
  ⟨[⟨.or,[4,5]⟩, ⟨.or,[0,1]⟩, ⟨.and,[0,1]⟩,
    ⟨.and,[7,2]⟩, ⟨.or,[9,3]⟩, ⟨.and,[7,6]⟩,
    ⟨.or,[11,2]⟩, ⟨.and,[10,6]⟩, ⟨.or,[8,13]⟩, ⟨.and,[12,14]⟩], 15⟩

private theorem upper_mono : Monotone2 upper := by simp [Monotone2,upper]
private theorem upper_size : upper.size = 10 := rfl

set_option maxHeartbeats 3000000 in
private theorem upper_truth : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) = target x := by
  decide +kernel

private theorem mixed_atLeast10 (cert : Threshold.search 6 Threshold.inputs = false)
    (C : Circuit) (hf : FanInTwo C)
    (hc : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x)
    (hm : ∃ g ∈ C.gates, g.op = .not) : 10 ≤ C.size := by
  have hc' : ∀ xs : List Bool, xs.length = 6 → C.eval xs = full6 xs := by
    intro xs hx
    let x : Fin 6 → Bool := fun i => xs.getD i.val false
    have he : List.ofFn x = xs := Signed.from_list_fn 6 xs hx
    rw [←he, hc,full_truth]
  obtain ⟨gs,r,hlen,hfw,hrange,hf'⟩ :=
    Signed.ordinary_signed_realizes C 6 full6 hf (by decide) full_essential hc'
  have h9 := signed_full_ge9 cert gs r hfw hrange hf'
  have hlt : (C.gates.filter Signed.binaryOperation).length < C.gates.length := by
    rcases hm with ⟨g,hg,hop⟩
    have hle := List.length_filter_le Signed.binaryOperation C.gates
    by_contra hc
    have hh : (C.gates.filter Signed.binaryOperation).length = C.gates.length := by omega
    have hi := (List.length_filter_eq_length_iff.mp hh) g hg
    simp [Signed.binaryOperation,hop] at hi
  change 10 ≤ C.gates.length
  omega

theorem exact_from_small_certificate
    (cert : Threshold.search 6 Threshold.inputs = false)
    (s : Nat) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C,hfan,hsize,he⟩ := h
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hc := mixed_atLeast10 cert C hfan he hn
    exact ⟨upper,upper_mono,by rw [upper_size];omega,upper_truth⟩
  · refine ⟨C, ?_, hsize, he⟩
    intro g hg
    obtain ⟨hm,hl⟩ := hfan g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm ⊢
    rcases hm with e | e | e
    · exact ⟨Or.inl e,hl⟩
    · exact ⟨Or.inr e,hl⟩
    · exact False.elim (hn ⟨g,hg,e⟩)

end PEqualNP.Outside.L_meta_12339_aux

namespace PEqualNP.Outside.L_meta_12339_aux.Threshold

/-- The first-step list makes ground kernel certificates independently
checkable branch by branch. -/
def rootMoves (k : Nat) (v : List Signal) : List (List Signal) :=
  v.flatMap fun a => v.flatMap fun b =>
    if ¬ a.toNat<b.toNat then [] else
      bits.flatMap fun p => bits.flatMap fun q =>
        let z := gate p q a b
        if z=0 ∨ z∈v then [] else
          bits.flatMap fun ka => bits.filterMap fun kb =>
            let w := z :: v.filter (retain a b ka kb)
            if decide (w.length ≤ k+1) && cover w then some w else none

private theorem search_split (k : Nat) (v : List Signal) :
    search (k+1) v =
      (if v.length > k+2 then false
       else (v == [ttGoal]) || (rootMoves k v).any (search k)) := by
  simp only [search,rootMoves,List.any_flatMap]
  by_cases hlen : v.length > k+2
  · simp [hlen]
  · simp only [hlen,ite_false]
    congr 1
    apply List.any_congr rfl
    intro a
    apply List.any_congr rfl
    intro b
    by_cases he : ¬ a.toNat<b.toNat
    · simp [he]
    · simp only [he,ite_false,List.any_flatMap]
      apply List.any_congr rfl
      intro p
      apply List.any_congr rfl
      intro q
      let z := gate p q a b
      by_cases hf : z=0 ∨ z∈v
      · have ht : gate p q a b = 0 ∨ gate p q a b ∈ v := hf
        simp only [ht,ite_true,List.any_nil]
      · have ht : ¬ (gate p q a b = 0 ∨ gate p q a b ∈ v) := hf
        simp only [ht,ite_false,List.any_flatMap,List.any_filterMap]
        apply List.any_congr rfl
        intro ka
        apply List.any_congr rfl
        intro kb
        let w := gate p q a b :: v.filter (retain a b ka kb)
        by_cases hc : (decide (w.length ≤ k+1) && cover w) = true
        · have ht : (decide ((gate p q a b :: v.filter (retain a b ka kb)).length ≤ k+1) &&
              cover (gate p q a b :: v.filter (retain a b ka kb))) = true := hc
          simp only [ht,ite_true,Bool.true_and]
        · have ht : (decide ((gate p q a b :: v.filter (retain a b ka kb)).length ≤ k+1) &&
              cover (gate p q a b :: v.filter (retain a b ka kb))) = false :=
            Bool.eq_false_iff.mpr hc
          simp only [ht,Bool.false_and,Bool.false_eq_true,ite_false]

private inductive AllBlocked (k : Nat) : List (List Signal) → Prop
  | nil : AllBlocked k []
  | cons {a : List Signal} {as : List (List Signal)} :
      search k a = false → AllBlocked k as → AllBlocked k (a :: as)

private theorem AllBlocked.any_eq_false {k : Nat} {v : List (List Signal)}
    (h : AllBlocked k v) : v.any (search k) = false := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.any_cons, h, ih, Bool.false_or]

private theorem noNode (k : Nat) (v : List Signal) (kids : List (List Signal))
    (notGoal : v ≠ [ttGoal])
    (generated : rootMoves k v = kids)
    (proved : AllBlocked k kids) : search (k+1) v = false := by
  rw [search_split,generated,proved.any_eq_false]
  simp [notGoal]

private theorem no_2_0 : search 2 [0xaaa,0xff0,0xcccc] = false :=
  noNode 1 [0xaaa,0xff0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_1 : search 2 [0xaaa,0xfccc,0xfff0] = false :=
  noNode 1 [0xaaa,0xfccc,0xfff0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_2 : search 2 [0xaaa,0xfff0,0xfccc] = false :=
  noNode 1 [0xaaa,0xfff0,0xfccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_3 : search 2 [0xccc,0xff0,0xaaaa] = false :=
  noNode 1 [0xccc,0xff0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_4 : search 2 [0xccc,0xfaaa,0xfff0] = false :=
  noNode 1 [0xccc,0xfaaa,0xfff0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_5 : search 2 [0xccc,0xfff0,0xfaaa] = false :=
  noNode 1 [0xccc,0xfff0,0xfaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_6 : search 2 [0xff0,0xaaa,0xcccc] = false :=
  noNode 1 [0xff0,0xaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_7 : search 2 [0xff0,0xccc,0xaaaa] = false :=
  noNode 1 [0xff0,0xccc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_8 : search 2 [0xff0,0xaaaa,0xcccc] = false :=
  noNode 1 [0xff0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_9 : search 2 [0xff0,0xfaaa,0xcccc] = false :=
  noNode 1 [0xff0,0xfaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_10 : search 2 [0xff0,0xfccc,0xaaaa] = false :=
  noNode 1 [0xff0,0xfccc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_11 : search 2 [0x22aa,0x33cc,0xf0f0] = false :=
  noNode 1 [0x22aa,0x33cc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_12 : search 2 [0x22aa,0xfcf0,0xffcc] = false :=
  noNode 1 [0x22aa,0xfcf0,0xffcc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_13 : search 2 [0x22aa,0xffcc,0xfcf0] = false :=
  noNode 1 [0x22aa,0xffcc,0xfcf0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_14 : search 2 [0x2a2a,0x3c3c,0xff00] = false :=
  noNode 1 [0x2a2a,0x3c3c,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_15 : search 2 [0x2a2a,0xfcfc,0xffc0] = false :=
  noNode 1 [0x2a2a,0xfcfc,0xffc0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_16 : search 2 [0x2a2a,0xffc0,0xfcfc] = false :=
  noNode 1 [0x2a2a,0xffc0,0xfcfc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_17 : search 2 [0x30f0,0x33cc,0xaaaa] = false :=
  noNode 1 [0x30f0,0x33cc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_18 : search 2 [0x30f0,0xeeaa,0xffcc] = false :=
  noNode 1 [0x30f0,0xeeaa,0xffcc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_19 : search 2 [0x30f0,0xffcc,0xeeaa] = false :=
  noNode 1 [0x30f0,0xffcc,0xeeaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_20 : search 2 [0x33cc,0x22aa,0xf0f0] = false :=
  noNode 1 [0x33cc,0x22aa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_21 : search 2 [0x33cc,0x30f0,0xaaaa] = false :=
  noNode 1 [0x33cc,0x30f0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_22 : search 2 [0x33cc,0xaaaa,0xf0f0] = false :=
  noNode 1 [0x33cc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_23 : search 2 [0x33cc,0xeeaa,0xf0f0] = false :=
  noNode 1 [0x33cc,0xeeaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_24 : search 2 [0x33cc,0xfcf0,0xaaaa] = false :=
  noNode 1 [0x33cc,0xfcf0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_25 : search 2 [0x3c3c,0x2a2a,0xff00] = false :=
  noNode 1 [0x3c3c,0x2a2a,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_26 : search 2 [0x3c3c,0x3f00,0xaaaa] = false :=
  noNode 1 [0x3c3c,0x3f00,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_27 : search 2 [0x3c3c,0xaaaa,0xff00] = false :=
  noNode 1 [0x3c3c,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_28 : search 2 [0x3c3c,0xeaea,0xff00] = false :=
  noNode 1 [0x3c3c,0xeaea,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_29 : search 2 [0x3c3c,0xffc0,0xaaaa] = false :=
  noNode 1 [0x3c3c,0xffc0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_30 : search 2 [0x3f00,0x3c3c,0xaaaa] = false :=
  noNode 1 [0x3f00,0x3c3c,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_31 : search 2 [0x3f00,0xeaea,0xfcfc] = false :=
  noNode 1 [0x3f00,0xeaea,0xfcfc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_32 : search 2 [0x3f00,0xfcfc,0xeaea] = false :=
  noNode 1 [0x3f00,0xfcfc,0xeaea] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_33 : search 2 [0x44cc,0x55aa,0xf0f0] = false :=
  noNode 1 [0x44cc,0x55aa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_34 : search 2 [0x44cc,0xfaf0,0xffaa] = false :=
  noNode 1 [0x44cc,0xfaf0,0xffaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_35 : search 2 [0x44cc,0xffaa,0xfaf0] = false :=
  noNode 1 [0x44cc,0xffaa,0xfaf0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_36 : search 2 [0x4c4c,0x5a5a,0xff00] = false :=
  noNode 1 [0x4c4c,0x5a5a,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_37 : search 2 [0x4c4c,0xfafa,0xffa0] = false :=
  noNode 1 [0x4c4c,0xfafa,0xffa0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_38 : search 2 [0x4c4c,0xffa0,0xfafa] = false :=
  noNode 1 [0x4c4c,0xffa0,0xfafa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_39 : search 2 [0x50f0,0x55aa,0xcccc] = false :=
  noNode 1 [0x50f0,0x55aa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_40 : search 2 [0x50f0,0xeecc,0xffaa] = false :=
  noNode 1 [0x50f0,0xeecc,0xffaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_41 : search 2 [0x50f0,0xffaa,0xeecc] = false :=
  noNode 1 [0x50f0,0xffaa,0xeecc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_42 : search 2 [0x55aa,0x44cc,0xf0f0] = false :=
  noNode 1 [0x55aa,0x44cc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_43 : search 2 [0x55aa,0x50f0,0xcccc] = false :=
  noNode 1 [0x55aa,0x50f0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_44 : search 2 [0x55aa,0xcccc,0xf0f0] = false :=
  noNode 1 [0x55aa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_45 : search 2 [0x55aa,0xeecc,0xf0f0] = false :=
  noNode 1 [0x55aa,0xeecc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_46 : search 2 [0x55aa,0xfaf0,0xcccc] = false :=
  noNode 1 [0x55aa,0xfaf0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_47 : search 2 [0x5a5a,0x4c4c,0xff00] = false :=
  noNode 1 [0x5a5a,0x4c4c,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_48 : search 2 [0x5a5a,0x5f00,0xcccc] = false :=
  noNode 1 [0x5a5a,0x5f00,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_49 : search 2 [0x5a5a,0xcccc,0xff00] = false :=
  noNode 1 [0x5a5a,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_50 : search 2 [0x5a5a,0xecec,0xff00] = false :=
  noNode 1 [0x5a5a,0xecec,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_51 : search 2 [0x5a5a,0xffa0,0xcccc] = false :=
  noNode 1 [0x5a5a,0xffa0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_52 : search 2 [0x5f00,0x5a5a,0xcccc] = false :=
  noNode 1 [0x5f00,0x5a5a,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_53 : search 2 [0x5f00,0xecec,0xfafa] = false :=
  noNode 1 [0x5f00,0xecec,0xfafa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_54 : search 2 [0x5f00,0xfafa,0xecec] = false :=
  noNode 1 [0x5f00,0xfafa,0xecec] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_55 : search 2 [0x6666,0x7070,0xff00] = false :=
  noNode 1 [0x6666,0x7070,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_56 : search 2 [0x6666,0x7700,0xf0f0] = false :=
  noNode 1 [0x6666,0x7700,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_57 : search 2 [0x6666,0xf0f0,0xff00] = false :=
  noNode 1 [0x6666,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_58 : search 2 [0x6666,0xf8f8,0xff00] = false :=
  noNode 1 [0x6666,0xf8f8,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_59 : search 2 [0x6666,0xff88,0xf0f0] = false :=
  noNode 1 [0x6666,0xff88,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_60 : search 2 [0x7070,0x6666,0xff00] = false :=
  noNode 1 [0x7070,0x6666,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_61 : search 2 [0x7070,0xeeee,0xff88] = false :=
  noNode 1 [0x7070,0xeeee,0xff88] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_62 : search 2 [0x7070,0xff88,0xeeee] = false :=
  noNode 1 [0x7070,0xff88,0xeeee] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_63 : search 2 [0x7700,0x6666,0xf0f0] = false :=
  noNode 1 [0x7700,0x6666,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_64 : search 2 [0x7700,0xeeee,0xf8f8] = false :=
  noNode 1 [0x7700,0xeeee,0xf8f8] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_65 : search 2 [0x7700,0xf8f8,0xeeee] = false :=
  noNode 1 [0x7700,0xf8f8,0xeeee] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_66 : search 2 [0xaaea,0xfcfc,0xff00] = false :=
  noNode 1 [0xaaea,0xfcfc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_67 : search 2 [0xaeaa,0xffcc,0xf0f0] = false :=
  noNode 1 [0xaeaa,0xffcc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_68 : search 2 [0xaff0,0xaaaa,0xcccc] = false :=
  noNode 1 [0xaff0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_69 : search 2 [0xbaaa,0xfff0,0xcccc] = false :=
  noNode 1 [0xbaaa,0xfff0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_70 : search 2 [0xbbcc,0xaaaa,0xf0f0] = false :=
  noNode 1 [0xbbcc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_71 : search 2 [0xbcbc,0xaaaa,0xff00] = false :=
  noNode 1 [0xbcbc,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_72 : search 2 [0xccec,0xfafa,0xff00] = false :=
  noNode 1 [0xccec,0xfafa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_73 : search 2 [0xcecc,0xffaa,0xf0f0] = false :=
  noNode 1 [0xcecc,0xffaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_74 : search 2 [0xcff0,0xaaaa,0xcccc] = false :=
  noNode 1 [0xcff0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_75 : search 2 [0xdada,0xcccc,0xff00] = false :=
  noNode 1 [0xdada,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_76 : search 2 [0xdccc,0xfff0,0xaaaa] = false :=
  noNode 1 [0xdccc,0xfff0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_77 : search 2 [0xddaa,0xcccc,0xf0f0] = false :=
  noNode 1 [0xddaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_78 : search 2 [0xe6e6,0xf0f0,0xff00] = false :=
  noNode 1 [0xe6e6,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_79 : search 2 [0xeaea,0x3c3c,0xff00] = false :=
  noNode 1 [0xeaea,0x3c3c,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_80 : search 2 [0xeaea,0x3f00,0xfcfc] = false :=
  noNode 1 [0xeaea,0x3f00,0xfcfc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_81 : search 2 [0xeaea,0xfcfc,0x3f00] = false :=
  noNode 1 [0xeaea,0xfcfc,0x3f00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_82 : search 2 [0xeaea,0xfcfc,0xff00] = false :=
  noNode 1 [0xeaea,0xfcfc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_83 : search 2 [0xeaea,0xfcfc,0xffc0] = false :=
  noNode 1 [0xeaea,0xfcfc,0xffc0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_84 : search 2 [0xeaea,0xffc0,0xfcfc] = false :=
  noNode 1 [0xeaea,0xffc0,0xfcfc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_85 : search 2 [0xecec,0x5a5a,0xff00] = false :=
  noNode 1 [0xecec,0x5a5a,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_86 : search 2 [0xecec,0x5f00,0xfafa] = false :=
  noNode 1 [0xecec,0x5f00,0xfafa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_87 : search 2 [0xecec,0xfafa,0x5f00] = false :=
  noNode 1 [0xecec,0xfafa,0x5f00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_88 : search 2 [0xecec,0xfafa,0xff00] = false :=
  noNode 1 [0xecec,0xfafa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_89 : search 2 [0xecec,0xfafa,0xffa0] = false :=
  noNode 1 [0xecec,0xfafa,0xffa0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_90 : search 2 [0xecec,0xffa0,0xfafa] = false :=
  noNode 1 [0xecec,0xffa0,0xfafa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_91 : search 2 [0xee66,0xf0f0,0xff00] = false :=
  noNode 1 [0xee66,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_92 : search 2 [0xeeaa,0x30f0,0xffcc] = false :=
  noNode 1 [0xeeaa,0x30f0,0xffcc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_93 : search 2 [0xeeaa,0x33cc,0xf0f0] = false :=
  noNode 1 [0xeeaa,0x33cc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_94 : search 2 [0xeeaa,0xfcf0,0xffcc] = false :=
  noNode 1 [0xeeaa,0xfcf0,0xffcc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_95 : search 2 [0xeeaa,0xffcc,0x30f0] = false :=
  noNode 1 [0xeeaa,0xffcc,0x30f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_96 : search 2 [0xeeaa,0xffcc,0xf0f0] = false :=
  noNode 1 [0xeeaa,0xffcc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_97 : search 2 [0xeeaa,0xffcc,0xfcf0] = false :=
  noNode 1 [0xeeaa,0xffcc,0xfcf0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_98 : search 2 [0xeecc,0x50f0,0xffaa] = false :=
  noNode 1 [0xeecc,0x50f0,0xffaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_99 : search 2 [0xeecc,0x55aa,0xf0f0] = false :=
  noNode 1 [0xeecc,0x55aa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_100 : search 2 [0xeecc,0xfaf0,0xffaa] = false :=
  noNode 1 [0xeecc,0xfaf0,0xffaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_101 : search 2 [0xeecc,0xffaa,0x50f0] = false :=
  noNode 1 [0xeecc,0xffaa,0x50f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_102 : search 2 [0xeecc,0xffaa,0xf0f0] = false :=
  noNode 1 [0xeecc,0xffaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_103 : search 2 [0xeecc,0xffaa,0xfaf0] = false :=
  noNode 1 [0xeecc,0xffaa,0xfaf0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_104 : search 2 [0xeeea,0xfcfc,0xff00] = false :=
  noNode 1 [0xeeea,0xfcfc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_105 : search 2 [0xeeea,0xffcc,0xf0f0] = false :=
  noNode 1 [0xeeea,0xffcc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_106 : search 2 [0xeeec,0xfafa,0xff00] = false :=
  noNode 1 [0xeeec,0xfafa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_107 : search 2 [0xeeec,0xffaa,0xf0f0] = false :=
  noNode 1 [0xeeec,0xffaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_108 : search 2 [0xeeee,0x7070,0xff88] = false :=
  noNode 1 [0xeeee,0x7070,0xff88] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_109 : search 2 [0xeeee,0x7700,0xf8f8] = false :=
  noNode 1 [0xeeee,0x7700,0xf8f8] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_110 : search 2 [0xeeee,0xf0f8,0xff00] = false :=
  noNode 1 [0xeeee,0xf0f8,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_111 : search 2 [0xeeee,0xf8f8,0x7700] = false :=
  noNode 1 [0xeeee,0xf8f8,0x7700] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_112 : search 2 [0xeeee,0xf8f8,0xff00] = false :=
  noNode 1 [0xeeee,0xf8f8,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_113 : search 2 [0xeeee,0xf8f8,0xff88] = false :=
  noNode 1 [0xeeee,0xf8f8,0xff88] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_114 : search 2 [0xeeee,0xfaf8,0xff00] = false :=
  noNode 1 [0xeeee,0xfaf8,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_115 : search 2 [0xeeee,0xfcf8,0xff00] = false :=
  noNode 1 [0xeeee,0xfcf8,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_116 : search 2 [0xeeee,0xff08,0xf0f0] = false :=
  noNode 1 [0xeeee,0xff08,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_117 : search 2 [0xeeee,0xff88,0x7070] = false :=
  noNode 1 [0xeeee,0xff88,0x7070] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_118 : search 2 [0xeeee,0xff88,0xf0f0] = false :=
  noNode 1 [0xeeee,0xff88,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_119 : search 2 [0xeeee,0xff88,0xf8f8] = false :=
  noNode 1 [0xeeee,0xff88,0xf8f8] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_120 : search 2 [0xeeee,0xffa8,0xf0f0] = false :=
  noNode 1 [0xeeee,0xffa8,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_121 : search 2 [0xeeee,0xffc8,0xf0f0] = false :=
  noNode 1 [0xeeee,0xffc8,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_122 : search 2 [0xf0f8,0xeeee,0xff00] = false :=
  noNode 1 [0xf0f8,0xeeee,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_123 : search 2 [0xf2f0,0xffaa,0xcccc] = false :=
  noNode 1 [0xf2f0,0xffaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_124 : search 2 [0xf3cc,0xaaaa,0xf0f0] = false :=
  noNode 1 [0xf3cc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_125 : search 2 [0xf4f0,0xffcc,0xaaaa] = false :=
  noNode 1 [0xf4f0,0xffcc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_126 : search 2 [0xf5aa,0xcccc,0xf0f0] = false :=
  noNode 1 [0xf5aa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_127 : search 2 [0xf8f8,0x6666,0xff00] = false :=
  noNode 1 [0xf8f8,0x6666,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_128 : search 2 [0xf8f8,0x7700,0xeeee] = false :=
  noNode 1 [0xf8f8,0x7700,0xeeee] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_129 : search 2 [0xf8f8,0xeeee,0x7700] = false :=
  noNode 1 [0xf8f8,0xeeee,0x7700] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_130 : search 2 [0xf8f8,0xeeee,0xff00] = false :=
  noNode 1 [0xf8f8,0xeeee,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_131 : search 2 [0xf8f8,0xeeee,0xff88] = false :=
  noNode 1 [0xf8f8,0xeeee,0xff88] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_132 : search 2 [0xf8f8,0xff88,0xeeee] = false :=
  noNode 1 [0xf8f8,0xff88,0xeeee] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_133 : search 2 [0xfa5a,0xcccc,0xff00] = false :=
  noNode 1 [0xfa5a,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_134 : search 2 [0xfaaa,0xccc,0xfff0] = false :=
  noNode 1 [0xfaaa,0xccc,0xfff0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_135 : search 2 [0xfaaa,0xff0,0xcccc] = false :=
  noNode 1 [0xfaaa,0xff0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_136 : search 2 [0xfaaa,0xfccc,0xfff0] = false :=
  noNode 1 [0xfaaa,0xfccc,0xfff0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_137 : search 2 [0xfaaa,0xfff0,0xccc] = false :=
  noNode 1 [0xfaaa,0xfff0,0xccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_138 : search 2 [0xfaaa,0xfff0,0xcccc] = false :=
  noNode 1 [0xfaaa,0xfff0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_139 : search 2 [0xfaaa,0xfff0,0xfccc] = false :=
  noNode 1 [0xfaaa,0xfff0,0xfccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_140 : search 2 [0xfaea,0xfcfc,0xff00] = false :=
  noNode 1 [0xfaea,0xfcfc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_141 : search 2 [0xfaea,0xfff0,0xcccc] = false :=
  noNode 1 [0xfaea,0xfff0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_142 : search 2 [0xfaf0,0x44cc,0xffaa] = false :=
  noNode 1 [0xfaf0,0x44cc,0xffaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_143 : search 2 [0xfaf0,0x55aa,0xcccc] = false :=
  noNode 1 [0xfaf0,0x55aa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_144 : search 2 [0xfaf0,0xeecc,0xffaa] = false :=
  noNode 1 [0xfaf0,0xeecc,0xffaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_145 : search 2 [0xfaf0,0xffaa,0x44cc] = false :=
  noNode 1 [0xfaf0,0xffaa,0x44cc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_146 : search 2 [0xfaf0,0xffaa,0xcccc] = false :=
  noNode 1 [0xfaf0,0xffaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_147 : search 2 [0xfaf0,0xffaa,0xeecc] = false :=
  noNode 1 [0xfaf0,0xffaa,0xeecc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_148 : search 2 [0xfaf8,0xeeee,0xff00] = false :=
  noNode 1 [0xfaf8,0xeeee,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_149 : search 2 [0xfaf8,0xffaa,0xcccc] = false :=
  noNode 1 [0xfaf8,0xffaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_150 : search 2 [0xfafa,0x4c4c,0xffa0] = false :=
  noNode 1 [0xfafa,0x4c4c,0xffa0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_151 : search 2 [0xfafa,0x5f00,0xecec] = false :=
  noNode 1 [0xfafa,0x5f00,0xecec] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_152 : search 2 [0xfafa,0xccec,0xff00] = false :=
  noNode 1 [0xfafa,0xccec,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_153 : search 2 [0xfafa,0xecec,0x5f00] = false :=
  noNode 1 [0xfafa,0xecec,0x5f00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_154 : search 2 [0xfafa,0xecec,0xff00] = false :=
  noNode 1 [0xfafa,0xecec,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_155 : search 2 [0xfafa,0xecec,0xffa0] = false :=
  noNode 1 [0xfafa,0xecec,0xffa0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_156 : search 2 [0xfafa,0xeeec,0xff00] = false :=
  noNode 1 [0xfafa,0xeeec,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_157 : search 2 [0xfafa,0xfcec,0xff00] = false :=
  noNode 1 [0xfafa,0xfcec,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_158 : search 2 [0xfafa,0xff20,0xcccc] = false :=
  noNode 1 [0xfafa,0xff20,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_159 : search 2 [0xfafa,0xffa0,0x4c4c] = false :=
  noNode 1 [0xfafa,0xffa0,0x4c4c] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_160 : search 2 [0xfafa,0xffa0,0xcccc] = false :=
  noNode 1 [0xfafa,0xffa0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_161 : search 2 [0xfafa,0xffa0,0xecec] = false :=
  noNode 1 [0xfafa,0xffa0,0xecec] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_162 : search 2 [0xfafa,0xffa8,0xcccc] = false :=
  noNode 1 [0xfafa,0xffa8,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_163 : search 2 [0xfafa,0xffe0,0xcccc] = false :=
  noNode 1 [0xfafa,0xffe0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_164 : search 2 [0xfc3c,0xaaaa,0xff00] = false :=
  noNode 1 [0xfc3c,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_165 : search 2 [0xfccc,0xaaa,0xfff0] = false :=
  noNode 1 [0xfccc,0xaaa,0xfff0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_166 : search 2 [0xfccc,0xff0,0xaaaa] = false :=
  noNode 1 [0xfccc,0xff0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_167 : search 2 [0xfccc,0xfaaa,0xfff0] = false :=
  noNode 1 [0xfccc,0xfaaa,0xfff0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_168 : search 2 [0xfccc,0xfff0,0xaaa] = false :=
  noNode 1 [0xfccc,0xfff0,0xaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_169 : search 2 [0xfccc,0xfff0,0xaaaa] = false :=
  noNode 1 [0xfccc,0xfff0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_170 : search 2 [0xfccc,0xfff0,0xfaaa] = false :=
  noNode 1 [0xfccc,0xfff0,0xfaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_171 : search 2 [0xfcec,0xfafa,0xff00] = false :=
  noNode 1 [0xfcec,0xfafa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_172 : search 2 [0xfcec,0xfff0,0xaaaa] = false :=
  noNode 1 [0xfcec,0xfff0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_173 : search 2 [0xfcf0,0x22aa,0xffcc] = false :=
  noNode 1 [0xfcf0,0x22aa,0xffcc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_174 : search 2 [0xfcf0,0x33cc,0xaaaa] = false :=
  noNode 1 [0xfcf0,0x33cc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_175 : search 2 [0xfcf0,0xeeaa,0xffcc] = false :=
  noNode 1 [0xfcf0,0xeeaa,0xffcc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_176 : search 2 [0xfcf0,0xffcc,0x22aa] = false :=
  noNode 1 [0xfcf0,0xffcc,0x22aa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_177 : search 2 [0xfcf0,0xffcc,0xaaaa] = false :=
  noNode 1 [0xfcf0,0xffcc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_178 : search 2 [0xfcf0,0xffcc,0xeeaa] = false :=
  noNode 1 [0xfcf0,0xffcc,0xeeaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_179 : search 2 [0xfcf8,0xeeee,0xff00] = false :=
  noNode 1 [0xfcf8,0xeeee,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_180 : search 2 [0xfcf8,0xffcc,0xaaaa] = false :=
  noNode 1 [0xfcf8,0xffcc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_181 : search 2 [0xfcfc,0x2a2a,0xffc0] = false :=
  noNode 1 [0xfcfc,0x2a2a,0xffc0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_182 : search 2 [0xfcfc,0x3f00,0xeaea] = false :=
  noNode 1 [0xfcfc,0x3f00,0xeaea] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_183 : search 2 [0xfcfc,0xaaea,0xff00] = false :=
  noNode 1 [0xfcfc,0xaaea,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_184 : search 2 [0xfcfc,0xeaea,0x3f00] = false :=
  noNode 1 [0xfcfc,0xeaea,0x3f00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_185 : search 2 [0xfcfc,0xeaea,0xff00] = false :=
  noNode 1 [0xfcfc,0xeaea,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_186 : search 2 [0xfcfc,0xeaea,0xffc0] = false :=
  noNode 1 [0xfcfc,0xeaea,0xffc0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_187 : search 2 [0xfcfc,0xeeea,0xff00] = false :=
  noNode 1 [0xfcfc,0xeeea,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_188 : search 2 [0xfcfc,0xfaea,0xff00] = false :=
  noNode 1 [0xfcfc,0xfaea,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_189 : search 2 [0xfcfc,0xff40,0xaaaa] = false :=
  noNode 1 [0xfcfc,0xff40,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_190 : search 2 [0xfcfc,0xffc0,0x2a2a] = false :=
  noNode 1 [0xfcfc,0xffc0,0x2a2a] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_191 : search 2 [0xfcfc,0xffc0,0xaaaa] = false :=
  noNode 1 [0xfcfc,0xffc0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_192 : search 2 [0xfcfc,0xffc0,0xeaea] = false :=
  noNode 1 [0xfcfc,0xffc0,0xeaea] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_193 : search 2 [0xfcfc,0xffc8,0xaaaa] = false :=
  noNode 1 [0xfcfc,0xffc8,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_194 : search 2 [0xfcfc,0xffe0,0xaaaa] = false :=
  noNode 1 [0xfcfc,0xffe0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_195 : search 2 [0xfeaa,0xffcc,0xf0f0] = false :=
  noNode 1 [0xfeaa,0xffcc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_196 : search 2 [0xfeaa,0xfff0,0xcccc] = false :=
  noNode 1 [0xfeaa,0xfff0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_197 : search 2 [0xfecc,0xffaa,0xf0f0] = false :=
  noNode 1 [0xfecc,0xffaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_198 : search 2 [0xfecc,0xfff0,0xaaaa] = false :=
  noNode 1 [0xfecc,0xfff0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_199 : search 2 [0xfef0,0xffaa,0xcccc] = false :=
  noNode 1 [0xfef0,0xffaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_200 : search 2 [0xfef0,0xffcc,0xaaaa] = false :=
  noNode 1 [0xfef0,0xffcc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_201 : search 2 [0xff08,0xeeee,0xf0f0] = false :=
  noNode 1 [0xff08,0xeeee,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_202 : search 2 [0xff20,0xfafa,0xcccc] = false :=
  noNode 1 [0xff20,0xfafa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_203 : search 2 [0xff40,0xfcfc,0xaaaa] = false :=
  noNode 1 [0xff40,0xfcfc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_204 : search 2 [0xff88,0x6666,0xf0f0] = false :=
  noNode 1 [0xff88,0x6666,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_205 : search 2 [0xff88,0x7070,0xeeee] = false :=
  noNode 1 [0xff88,0x7070,0xeeee] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_206 : search 2 [0xff88,0xeeee,0x7070] = false :=
  noNode 1 [0xff88,0xeeee,0x7070] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_207 : search 2 [0xff88,0xeeee,0xf0f0] = false :=
  noNode 1 [0xff88,0xeeee,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_208 : search 2 [0xff88,0xeeee,0xf8f8] = false :=
  noNode 1 [0xff88,0xeeee,0xf8f8] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_209 : search 2 [0xff88,0xf8f8,0xeeee] = false :=
  noNode 1 [0xff88,0xf8f8,0xeeee] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_210 : search 2 [0xffa0,0x4c4c,0xfafa] = false :=
  noNode 1 [0xffa0,0x4c4c,0xfafa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_211 : search 2 [0xffa0,0x5a5a,0xcccc] = false :=
  noNode 1 [0xffa0,0x5a5a,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_212 : search 2 [0xffa0,0xecec,0xfafa] = false :=
  noNode 1 [0xffa0,0xecec,0xfafa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_213 : search 2 [0xffa0,0xfafa,0x4c4c] = false :=
  noNode 1 [0xffa0,0xfafa,0x4c4c] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_214 : search 2 [0xffa0,0xfafa,0xcccc] = false :=
  noNode 1 [0xffa0,0xfafa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_215 : search 2 [0xffa0,0xfafa,0xecec] = false :=
  noNode 1 [0xffa0,0xfafa,0xecec] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_216 : search 2 [0xffa8,0xeeee,0xf0f0] = false :=
  noNode 1 [0xffa8,0xeeee,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_217 : search 2 [0xffa8,0xfafa,0xcccc] = false :=
  noNode 1 [0xffa8,0xfafa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_218 : search 2 [0xffaa,0x44cc,0xfaf0] = false :=
  noNode 1 [0xffaa,0x44cc,0xfaf0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_219 : search 2 [0xffaa,0x50f0,0xeecc] = false :=
  noNode 1 [0xffaa,0x50f0,0xeecc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_220 : search 2 [0xffaa,0xcecc,0xf0f0] = false :=
  noNode 1 [0xffaa,0xcecc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_221 : search 2 [0xffaa,0xeecc,0x50f0] = false :=
  noNode 1 [0xffaa,0xeecc,0x50f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_222 : search 2 [0xffaa,0xeecc,0xf0f0] = false :=
  noNode 1 [0xffaa,0xeecc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_223 : search 2 [0xffaa,0xeecc,0xfaf0] = false :=
  noNode 1 [0xffaa,0xeecc,0xfaf0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_224 : search 2 [0xffaa,0xeeec,0xf0f0] = false :=
  noNode 1 [0xffaa,0xeeec,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_225 : search 2 [0xffaa,0xf2f0,0xcccc] = false :=
  noNode 1 [0xffaa,0xf2f0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_226 : search 2 [0xffaa,0xfaf0,0x44cc] = false :=
  noNode 1 [0xffaa,0xfaf0,0x44cc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_227 : search 2 [0xffaa,0xfaf0,0xcccc] = false :=
  noNode 1 [0xffaa,0xfaf0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_228 : search 2 [0xffaa,0xfaf0,0xeecc] = false :=
  noNode 1 [0xffaa,0xfaf0,0xeecc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_229 : search 2 [0xffaa,0xfaf8,0xcccc] = false :=
  noNode 1 [0xffaa,0xfaf8,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_230 : search 2 [0xffaa,0xfecc,0xf0f0] = false :=
  noNode 1 [0xffaa,0xfecc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_231 : search 2 [0xffaa,0xfef0,0xcccc] = false :=
  noNode 1 [0xffaa,0xfef0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_232 : search 2 [0xffc0,0x2a2a,0xfcfc] = false :=
  noNode 1 [0xffc0,0x2a2a,0xfcfc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_233 : search 2 [0xffc0,0x3c3c,0xaaaa] = false :=
  noNode 1 [0xffc0,0x3c3c,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_234 : search 2 [0xffc0,0xeaea,0xfcfc] = false :=
  noNode 1 [0xffc0,0xeaea,0xfcfc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_235 : search 2 [0xffc0,0xfcfc,0x2a2a] = false :=
  noNode 1 [0xffc0,0xfcfc,0x2a2a] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_236 : search 2 [0xffc0,0xfcfc,0xaaaa] = false :=
  noNode 1 [0xffc0,0xfcfc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_237 : search 2 [0xffc0,0xfcfc,0xeaea] = false :=
  noNode 1 [0xffc0,0xfcfc,0xeaea] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_238 : search 2 [0xffc8,0xeeee,0xf0f0] = false :=
  noNode 1 [0xffc8,0xeeee,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_239 : search 2 [0xffc8,0xfcfc,0xaaaa] = false :=
  noNode 1 [0xffc8,0xfcfc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_240 : search 2 [0xffcc,0x22aa,0xfcf0] = false :=
  noNode 1 [0xffcc,0x22aa,0xfcf0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_241 : search 2 [0xffcc,0x30f0,0xeeaa] = false :=
  noNode 1 [0xffcc,0x30f0,0xeeaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_242 : search 2 [0xffcc,0xaeaa,0xf0f0] = false :=
  noNode 1 [0xffcc,0xaeaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_243 : search 2 [0xffcc,0xeeaa,0x30f0] = false :=
  noNode 1 [0xffcc,0xeeaa,0x30f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_244 : search 2 [0xffcc,0xeeaa,0xf0f0] = false :=
  noNode 1 [0xffcc,0xeeaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_245 : search 2 [0xffcc,0xeeaa,0xfcf0] = false :=
  noNode 1 [0xffcc,0xeeaa,0xfcf0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_246 : search 2 [0xffcc,0xeeea,0xf0f0] = false :=
  noNode 1 [0xffcc,0xeeea,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_247 : search 2 [0xffcc,0xf4f0,0xaaaa] = false :=
  noNode 1 [0xffcc,0xf4f0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_248 : search 2 [0xffcc,0xfcf0,0x22aa] = false :=
  noNode 1 [0xffcc,0xfcf0,0x22aa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_249 : search 2 [0xffcc,0xfcf0,0xaaaa] = false :=
  noNode 1 [0xffcc,0xfcf0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_250 : search 2 [0xffcc,0xfcf0,0xeeaa] = false :=
  noNode 1 [0xffcc,0xfcf0,0xeeaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_251 : search 2 [0xffcc,0xfcf8,0xaaaa] = false :=
  noNode 1 [0xffcc,0xfcf8,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_252 : search 2 [0xffcc,0xfeaa,0xf0f0] = false :=
  noNode 1 [0xffcc,0xfeaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_253 : search 2 [0xffcc,0xfef0,0xaaaa] = false :=
  noNode 1 [0xffcc,0xfef0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_254 : search 2 [0xffe0,0xfafa,0xcccc] = false :=
  noNode 1 [0xffe0,0xfafa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_255 : search 2 [0xffe0,0xfcfc,0xaaaa] = false :=
  noNode 1 [0xffe0,0xfcfc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_256 : search 2 [0xfff0,0xaaa,0xfccc] = false :=
  noNode 1 [0xfff0,0xaaa,0xfccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_257 : search 2 [0xfff0,0xccc,0xfaaa] = false :=
  noNode 1 [0xfff0,0xccc,0xfaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_258 : search 2 [0xfff0,0xbaaa,0xcccc] = false :=
  noNode 1 [0xfff0,0xbaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_259 : search 2 [0xfff0,0xdccc,0xaaaa] = false :=
  noNode 1 [0xfff0,0xdccc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_260 : search 2 [0xfff0,0xfaaa,0xccc] = false :=
  noNode 1 [0xfff0,0xfaaa,0xccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_261 : search 2 [0xfff0,0xfaaa,0xcccc] = false :=
  noNode 1 [0xfff0,0xfaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_262 : search 2 [0xfff0,0xfaaa,0xfccc] = false :=
  noNode 1 [0xfff0,0xfaaa,0xfccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_263 : search 2 [0xfff0,0xfaea,0xcccc] = false :=
  noNode 1 [0xfff0,0xfaea,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_264 : search 2 [0xfff0,0xfccc,0xaaa] = false :=
  noNode 1 [0xfff0,0xfccc,0xaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_265 : search 2 [0xfff0,0xfccc,0xaaaa] = false :=
  noNode 1 [0xfff0,0xfccc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_266 : search 2 [0xfff0,0xfccc,0xfaaa] = false :=
  noNode 1 [0xfff0,0xfccc,0xfaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_267 : search 2 [0xfff0,0xfcec,0xaaaa] = false :=
  noNode 1 [0xfff0,0xfcec,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_268 : search 2 [0xfff0,0xfeaa,0xcccc] = false :=
  noNode 1 [0xfff0,0xfeaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_2_269 : search 2 [0xfff0,0xfecc,0xaaaa] = false :=
  noNode 1 [0xfff0,0xfecc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_0 : search 3 [0x88,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0x88,0xeeee,0xf0f0,0xff00] [[0xee66,0xf0f0,0xff00],[0xf0f8,0xeeee,0xff00],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_91 (AllBlocked.cons no_2_122 (AllBlocked.cons no_2_207 (AllBlocked.nil))))
private theorem no_3_1 : search 3 [0xa0,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0xa0,0xfafa,0xcccc,0xff00] [[0xfa5a,0xcccc,0xff00],[0xccec,0xfafa,0xff00],[0xffa0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_133 (AllBlocked.cons no_2_72 (AllBlocked.cons no_2_214 (AllBlocked.nil))))
private theorem no_3_2 : search 3 [0xaa,0x5500,0xcccc,0xf0f0] = false :=
  noNode 2 [0xaa,0x5500,0xcccc,0xf0f0] [[0x55aa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_44 (AllBlocked.nil))
private theorem no_3_3 : search 3 [0xaa,0xdd00,0xcccc,0xf0f0] = false :=
  noNode 2 [0xaa,0xdd00,0xcccc,0xf0f0] [[0xddaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_77 (AllBlocked.nil))
private theorem no_3_4 : search 3 [0xaa,0xeecc,0xf0f0,0xff00] = false :=
  noNode 2 [0xaa,0xeecc,0xf0f0,0xff00] [[0xffaa,0xeecc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_222 (AllBlocked.nil))
private theorem no_3_5 : search 3 [0xaa,0xf500,0xcccc,0xf0f0] = false :=
  noNode 2 [0xaa,0xf500,0xcccc,0xf0f0] [[0xf5aa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_126 (AllBlocked.nil))
private theorem no_3_6 : search 3 [0xaa,0xfaf0,0xcccc,0xff00] = false :=
  noNode 2 [0xaa,0xfaf0,0xcccc,0xff00] [[0xffaa,0xfaf0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_227 (AllBlocked.nil))
private theorem no_3_7 : search 3 [0xc0,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0xc0,0xfcfc,0xaaaa,0xff00] [[0xfc3c,0xaaaa,0xff00],[0xaaea,0xfcfc,0xff00],[0xffc0,0xfcfc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_164 (AllBlocked.cons no_2_66 (AllBlocked.cons no_2_236 (AllBlocked.nil))))
private theorem no_3_8 : search 3 [0xcc,0x3300,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xcc,0x3300,0xaaaa,0xf0f0] [[0x33cc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_22 (AllBlocked.nil))
private theorem no_3_9 : search 3 [0xcc,0xbb00,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xcc,0xbb00,0xaaaa,0xf0f0] [[0xbbcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_70 (AllBlocked.nil))
private theorem no_3_10 : search 3 [0xcc,0xeeaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xcc,0xeeaa,0xf0f0,0xff00] [[0xffcc,0xeeaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_244 (AllBlocked.nil))
private theorem no_3_11 : search 3 [0xcc,0xf300,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xcc,0xf300,0xaaaa,0xf0f0] [[0xf3cc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_124 (AllBlocked.nil))
private theorem no_3_12 : search 3 [0xcc,0xfcf0,0xaaaa,0xff00] = false :=
  noNode 2 [0xcc,0xfcf0,0xaaaa,0xff00] [[0xffcc,0xfcf0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_249 (AllBlocked.nil))
private theorem no_3_13 : search 3 [0xf0,0xf00,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf0,0xf00,0xaaaa,0xcccc] [[0xff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_8 (AllBlocked.nil))
private theorem no_3_14 : search 3 [0xf0,0xaf00,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf0,0xaf00,0xaaaa,0xcccc] [[0xaff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_68 (AllBlocked.nil))
private theorem no_3_15 : search 3 [0xf0,0xcf00,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf0,0xcf00,0xaaaa,0xcccc] [[0xcff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_74 (AllBlocked.nil))
private theorem no_3_16 : search 3 [0xf0,0xfaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf0,0xfaaa,0xcccc,0xff00] [[0xfff0,0xfaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_261 (AllBlocked.nil))
private theorem no_3_17 : search 3 [0xf0,0xfccc,0xaaaa,0xff00] = false :=
  noNode 2 [0xf0,0xfccc,0xaaaa,0xff00] [[0xfff0,0xfccc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_265 (AllBlocked.nil))
private theorem no_3_18 : search 3 [0xfe,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xfe,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_19 : search 3 [0x2aa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x2aa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_20 : search 3 [0x4cc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x4cc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_21 : search 3 [0x808,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0x808,0xeeee,0xf0f0,0xff00] [[0xe6e6,0xf0f0,0xff00],[0xf8f8,0xeeee,0xff00],[0xff08,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_78 (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_201 (AllBlocked.nil))))
private theorem no_3_22 : search 3 [0xa00,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xa00,0xffaa,0xcccc,0xf0f0] [[0xf5aa,0xcccc,0xf0f0],[0xcecc,0xffaa,0xf0f0],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_126 (AllBlocked.cons no_2_73 (AllBlocked.cons no_2_146 (AllBlocked.nil))))
private theorem no_3_23 : search 3 [0xa0a,0x5050,0xcccc,0xff00] = false :=
  noNode 2 [0xa0a,0x5050,0xcccc,0xff00] [[0x5a5a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_49 (AllBlocked.nil))
private theorem no_3_24 : search 3 [0xa0a,0xd0d0,0xcccc,0xff00] = false :=
  noNode 2 [0xa0a,0xd0d0,0xcccc,0xff00] [[0xdada,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_75 (AllBlocked.nil))
private theorem no_3_25 : search 3 [0xa0a,0xecec,0xf0f0,0xff00] = false :=
  noNode 2 [0xa0a,0xecec,0xf0f0,0xff00] [[0xfafa,0xecec,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_154 (AllBlocked.nil))
private theorem no_3_26 : search 3 [0xa0a,0xf050,0xcccc,0xff00] = false :=
  noNode 2 [0xa0a,0xf050,0xcccc,0xff00] [[0xfa5a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_133 (AllBlocked.nil))
private theorem no_3_27 : search 3 [0xa0a,0xffa0,0xcccc,0xf0f0] = false :=
  noNode 2 [0xa0a,0xffa0,0xcccc,0xf0f0] [[0xfafa,0xffa0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_160 (AllBlocked.nil))
private theorem no_3_28 : search 3 [0xa2a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xa2a,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_29 : search 3 [0xaaa,0xccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xaaa,0xccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_30 : search 3 [0xaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_31 : search 3 [0xaaa,0xf000,0xfff0,0xcccc] = false :=
  noNode 2 [0xaaa,0xf000,0xfff0,0xcccc] [[0xfaaa,0xfff0,0xcccc],[0xff0,0xaaa,0xcccc],[0xfccc,0xaaa,0xfff0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_6 (AllBlocked.cons no_2_165 (AllBlocked.nil))))
private theorem no_3_32 : search 3 [0xaaa,0xfccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xaaa,0xfccc,0xf0f0,0xff00] [[0xfff0,0xaaa,0xfccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_256 (AllBlocked.nil))
private theorem no_3_33 : search 3 [0xaaa,0xfff0,0xf000,0xcccc] = false :=
  noNode 2 [0xaaa,0xfff0,0xf000,0xcccc] [[0xfaaa,0xfff0,0xcccc],[0xff0,0xaaa,0xcccc],[0xfccc,0xaaa,0xfff0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_6 (AllBlocked.cons no_2_165 (AllBlocked.nil))))
private theorem no_3_34 : search 3 [0xc00,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xc00,0xffcc,0xaaaa,0xf0f0] [[0xf3cc,0xaaaa,0xf0f0],[0xaeaa,0xffcc,0xf0f0],[0xfcf0,0xffcc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_124 (AllBlocked.cons no_2_67 (AllBlocked.cons no_2_177 (AllBlocked.nil))))
private theorem no_3_35 : search 3 [0xc0c,0x3030,0xaaaa,0xff00] = false :=
  noNode 2 [0xc0c,0x3030,0xaaaa,0xff00] [[0x3c3c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_27 (AllBlocked.nil))
private theorem no_3_36 : search 3 [0xc0c,0xb0b0,0xaaaa,0xff00] = false :=
  noNode 2 [0xc0c,0xb0b0,0xaaaa,0xff00] [[0xbcbc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_71 (AllBlocked.nil))
private theorem no_3_37 : search 3 [0xc0c,0xeaea,0xf0f0,0xff00] = false :=
  noNode 2 [0xc0c,0xeaea,0xf0f0,0xff00] [[0xfcfc,0xeaea,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_185 (AllBlocked.nil))
private theorem no_3_38 : search 3 [0xc0c,0xf030,0xaaaa,0xff00] = false :=
  noNode 2 [0xc0c,0xf030,0xaaaa,0xff00] [[0xfc3c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_164 (AllBlocked.nil))
private theorem no_3_39 : search 3 [0xc0c,0xffc0,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xc0c,0xffc0,0xaaaa,0xf0f0] [[0xfcfc,0xffc0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_191 (AllBlocked.nil))
private theorem no_3_40 : search 3 [0xc4c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xc4c,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_41 : search 3 [0xccc,0xaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xccc,0xaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_42 : search 3 [0xccc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xccc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_43 : search 3 [0xccc,0xf000,0xfff0,0xaaaa] = false :=
  noNode 2 [0xccc,0xf000,0xfff0,0xaaaa] [[0xfccc,0xfff0,0xaaaa],[0xff0,0xccc,0xaaaa],[0xfaaa,0xccc,0xfff0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_169 (AllBlocked.cons no_2_7 (AllBlocked.cons no_2_134 (AllBlocked.nil))))
private theorem no_3_44 : search 3 [0xccc,0xfaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xccc,0xfaaa,0xf0f0,0xff00] [[0xfff0,0xccc,0xfaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_257 (AllBlocked.nil))
private theorem no_3_45 : search 3 [0xccc,0xfff0,0xf000,0xaaaa] = false :=
  noNode 2 [0xccc,0xfff0,0xf000,0xaaaa] [[0xfccc,0xfff0,0xaaaa],[0xff0,0xccc,0xaaaa],[0xfaaa,0xccc,0xfff0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_169 (AllBlocked.cons no_2_7 (AllBlocked.cons no_2_134 (AllBlocked.nil))))
private theorem no_3_46 : search 3 [0xf00,0xf0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf00,0xf0,0xaaaa,0xcccc] [[0xff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_8 (AllBlocked.nil))
private theorem no_3_47 : search 3 [0xf00,0xa0f0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf00,0xa0f0,0xaaaa,0xcccc] [[0xaff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_68 (AllBlocked.nil))
private theorem no_3_48 : search 3 [0xf00,0xc0f0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf00,0xc0f0,0xaaaa,0xcccc] [[0xcff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_74 (AllBlocked.nil))
private theorem no_3_49 : search 3 [0xf00,0xfaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xf00,0xfaaa,0xcccc,0xf0f0] [[0xfff0,0xfaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_261 (AllBlocked.nil))
private theorem no_3_50 : search 3 [0xf00,0xfccc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xf00,0xfccc,0xaaaa,0xf0f0] [[0xfff0,0xfccc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_265 (AllBlocked.nil))
private theorem no_3_51 : search 3 [0xf0e,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf0e,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_52 : search 3 [0xff0,0xf0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xff0,0xf0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_53 : search 3 [0xff0,0xf00,0xaaaa,0xcccc] = false :=
  noNode 2 [0xff0,0xf00,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_54 : search 3 [0xff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xff0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_55 : search 3 [0xff0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xff0,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_56 : search 3 [0xff0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xff0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_57 : search 3 [0xff0,0xf000,0xaaaa,0xcccc] = false :=
  noNode 2 [0xff0,0xf000,0xaaaa,0xcccc] [[0xaaa,0xff0,0xcccc],[0xfaaa,0xff0,0xcccc],[0xccc,0xff0,0xaaaa],[0xfccc,0xff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_0 (AllBlocked.cons no_2_135 (AllBlocked.cons no_2_3 (AllBlocked.cons no_2_166 (AllBlocked.nil)))))
private theorem no_3_58 : search 3 [0xff0,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xff0,0xfff0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_59 : search 3 [0x10f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0x10f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_60 : search 3 [0x1f00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x1f00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_61 : search 3 [0x2020,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0x2020,0xfafa,0xcccc,0xff00] [[0xdada,0xcccc,0xff00],[0xecec,0xfafa,0xff00],[0xff20,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_75 (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_202 (AllBlocked.nil))))
private theorem no_3_62 : search 3 [0x2200,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x2200,0xffaa,0xcccc,0xf0f0] [[0xddaa,0xcccc,0xf0f0],[0xeecc,0xffaa,0xf0f0],[0xf2f0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_77 (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_123 (AllBlocked.nil))))
private theorem no_3_63 : search 3 [0x2222,0x4444,0xf0f0,0xff00] = false :=
  noNode 2 [0x2222,0x4444,0xf0f0,0xff00] [[0x6666,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_57 (AllBlocked.nil))
private theorem no_3_64 : search 3 [0x2222,0xc4c4,0xf0f0,0xff00] = false :=
  noNode 2 [0x2222,0xc4c4,0xf0f0,0xff00] [[0xe6e6,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_78 (AllBlocked.nil))
private theorem no_3_65 : search 3 [0x2222,0xcc44,0xf0f0,0xff00] = false :=
  noNode 2 [0x2222,0xcc44,0xf0f0,0xff00] [[0xee66,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_91 (AllBlocked.nil))
private theorem no_3_66 : search 3 [0x2222,0xf8f8,0xcccc,0xff00] = false :=
  noNode 2 [0x2222,0xf8f8,0xcccc,0xff00] [[0xeeee,0xf8f8,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_112 (AllBlocked.nil))
private theorem no_3_67 : search 3 [0x2222,0xff88,0xcccc,0xf0f0] = false :=
  noNode 2 [0x2222,0xff88,0xcccc,0xf0f0] [[0xeeee,0xff88,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_118 (AllBlocked.nil))
private theorem no_3_68 : search 3 [0x222a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x222a,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_69 : search 3 [0x22aa,0x30f0,0xcccc,0xff00] = false :=
  noNode 2 [0x22aa,0x30f0,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_70 : search 3 [0x22aa,0xcc00,0xffcc,0xf0f0] = false :=
  noNode 2 [0x22aa,0xcc00,0xffcc,0xf0f0] [[0xeeaa,0xffcc,0xf0f0],[0x33cc,0x22aa,0xf0f0],[0xfcf0,0x22aa,0xffcc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_20 (AllBlocked.cons no_2_173 (AllBlocked.nil))))
private theorem no_3_71 : search 3 [0x22aa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x22aa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_72 : search 3 [0x22aa,0xfcf0,0xcccc,0xff00] = false :=
  noNode 2 [0x22aa,0xfcf0,0xcccc,0xff00] [[0xffcc,0x22aa,0xfcf0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_240 (AllBlocked.nil))
private theorem no_3_73 : search 3 [0x22aa,0xffcc,0xcc00,0xf0f0] = false :=
  noNode 2 [0x22aa,0xffcc,0xcc00,0xf0f0] [[0xeeaa,0xffcc,0xf0f0],[0x33cc,0x22aa,0xf0f0],[0xfcf0,0x22aa,0xffcc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_20 (AllBlocked.cons no_2_173 (AllBlocked.nil))))
private theorem no_3_74 : search 3 [0x2a2a,0x3f00,0xcccc,0xf0f0] = false :=
  noNode 2 [0x2a2a,0x3f00,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_75 : search 3 [0x2a2a,0xc0c0,0xfcfc,0xff00] = false :=
  noNode 2 [0x2a2a,0xc0c0,0xfcfc,0xff00] [[0xeaea,0xfcfc,0xff00],[0x3c3c,0x2a2a,0xff00],[0xffc0,0x2a2a,0xfcfc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_25 (AllBlocked.cons no_2_232 (AllBlocked.nil))))
private theorem no_3_76 : search 3 [0x2a2a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x2a2a,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_77 : search 3 [0x2a2a,0xfcfc,0xc0c0,0xff00] = false :=
  noNode 2 [0x2a2a,0xfcfc,0xc0c0,0xff00] [[0xeaea,0xfcfc,0xff00],[0x3c3c,0x2a2a,0xff00],[0xffc0,0x2a2a,0xfcfc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_25 (AllBlocked.cons no_2_232 (AllBlocked.nil))))
private theorem no_3_78 : search 3 [0x2a2a,0xffc0,0xcccc,0xf0f0] = false :=
  noNode 2 [0x2a2a,0xffc0,0xcccc,0xf0f0] [[0xfcfc,0x2a2a,0xffc0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_181 (AllBlocked.nil))
private theorem no_3_79 : search 3 [0x2aaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x2aaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_80 : search 3 [0x3000,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0x3000,0xfff0,0xaaaa,0xcccc] [[0xcff0,0xaaaa,0xcccc],[0xbaaa,0xfff0,0xcccc],[0xfccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_74 (AllBlocked.cons no_2_69 (AllBlocked.cons no_2_169 (AllBlocked.nil))))
private theorem no_3_81 : search 3 [0x3030,0xc0c,0xaaaa,0xff00] = false :=
  noNode 2 [0x3030,0xc0c,0xaaaa,0xff00] [[0x3c3c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_27 (AllBlocked.nil))
private theorem no_3_82 : search 3 [0x3030,0x8c8c,0xaaaa,0xff00] = false :=
  noNode 2 [0x3030,0x8c8c,0xaaaa,0xff00] [[0xbcbc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_71 (AllBlocked.nil))
private theorem no_3_83 : search 3 [0x3030,0xcc0c,0xaaaa,0xff00] = false :=
  noNode 2 [0x3030,0xcc0c,0xaaaa,0xff00] [[0xfc3c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_164 (AllBlocked.nil))
private theorem no_3_84 : search 3 [0x3030,0xeaea,0xcccc,0xff00] = false :=
  noNode 2 [0x3030,0xeaea,0xcccc,0xff00] [[0xfcfc,0xeaea,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_185 (AllBlocked.nil))
private theorem no_3_85 : search 3 [0x3030,0xffc0,0xaaaa,0xcccc] = false :=
  noNode 2 [0x3030,0xffc0,0xaaaa,0xcccc] [[0xfcfc,0xffc0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_191 (AllBlocked.nil))
private theorem no_3_86 : search 3 [0x3070,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0x3070,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_87 : search 3 [0x30f0,0x22aa,0xcccc,0xff00] = false :=
  noNode 2 [0x30f0,0x22aa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_88 : search 3 [0x30f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0x30f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_89 : search 3 [0x30f0,0xcc00,0xffcc,0xaaaa] = false :=
  noNode 2 [0x30f0,0xcc00,0xffcc,0xaaaa] [[0xfcf0,0xffcc,0xaaaa],[0x33cc,0x30f0,0xaaaa],[0xeeaa,0x30f0,0xffcc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_21 (AllBlocked.cons no_2_92 (AllBlocked.nil))))
private theorem no_3_90 : search 3 [0x30f0,0xeeaa,0xcccc,0xff00] = false :=
  noNode 2 [0x30f0,0xeeaa,0xcccc,0xff00] [[0xffcc,0x30f0,0xeeaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_241 (AllBlocked.nil))
private theorem no_3_91 : search 3 [0x30f0,0xffcc,0xcc00,0xaaaa] = false :=
  noNode 2 [0x30f0,0xffcc,0xcc00,0xaaaa] [[0xfcf0,0xffcc,0xaaaa],[0x33cc,0x30f0,0xaaaa],[0xeeaa,0x30f0,0xffcc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_21 (AllBlocked.cons no_2_92 (AllBlocked.nil))))
private theorem no_3_92 : search 3 [0x3300,0xcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x3300,0xcc,0xaaaa,0xf0f0] [[0x33cc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_22 (AllBlocked.nil))
private theorem no_3_93 : search 3 [0x3300,0x88cc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x3300,0x88cc,0xaaaa,0xf0f0] [[0xbbcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_70 (AllBlocked.nil))
private theorem no_3_94 : search 3 [0x3300,0xc0cc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x3300,0xc0cc,0xaaaa,0xf0f0] [[0xf3cc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_124 (AllBlocked.nil))
private theorem no_3_95 : search 3 [0x3300,0xeeaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x3300,0xeeaa,0xcccc,0xf0f0] [[0xffcc,0xeeaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_244 (AllBlocked.nil))
private theorem no_3_96 : search 3 [0x3300,0xfcf0,0xaaaa,0xcccc] = false :=
  noNode 2 [0x3300,0xfcf0,0xaaaa,0xcccc] [[0xffcc,0xfcf0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_249 (AllBlocked.nil))
private theorem no_3_97 : search 3 [0x3332,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x3332,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_98 : search 3 [0x33cc,0xcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x33cc,0xcc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_99 : search 3 [0x33cc,0x3300,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x33cc,0x3300,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_100 : search 3 [0x33cc,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x33cc,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_101 : search 3 [0x33cc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x33cc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_102 : search 3 [0x33cc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x33cc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_103 : search 3 [0x33cc,0xcc00,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x33cc,0xcc00,0xaaaa,0xf0f0] [[0x30f0,0x33cc,0xaaaa],[0xfcf0,0x33cc,0xaaaa],[0x22aa,0x33cc,0xf0f0],[0xeeaa,0x33cc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_17 (AllBlocked.cons no_2_174 (AllBlocked.cons no_2_11 (AllBlocked.cons no_2_93 (AllBlocked.nil)))))
private theorem no_3_104 : search 3 [0x33cc,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x33cc,0xffcc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_105 : search 3 [0x3700,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x3700,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_106 : search 3 [0x3c3c,0xc0c,0xaaaa,0xff00] = false :=
  noNode 2 [0x3c3c,0xc0c,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_107 : search 3 [0x3c3c,0x3030,0xaaaa,0xff00] = false :=
  noNode 2 [0x3c3c,0x3030,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_108 : search 3 [0x3c3c,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0x3c3c,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_109 : search 3 [0x3c3c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x3c3c,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_110 : search 3 [0x3c3c,0xaaaa,0xff00] = false :=
  noNode 2 [0x3c3c,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_111 : search 3 [0x3c3c,0xc0c0,0xaaaa,0xff00] = false :=
  noNode 2 [0x3c3c,0xc0c0,0xaaaa,0xff00] [[0x3f00,0x3c3c,0xaaaa],[0xffc0,0x3c3c,0xaaaa],[0x2a2a,0x3c3c,0xff00],[0xeaea,0x3c3c,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_30 (AllBlocked.cons no_2_233 (AllBlocked.cons no_2_14 (AllBlocked.cons no_2_79 (AllBlocked.nil)))))
private theorem no_3_112 : search 3 [0x3c3c,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0x3c3c,0xfcfc,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_113 : search 3 [0x3f00,0x2a2a,0xcccc,0xf0f0] = false :=
  noNode 2 [0x3f00,0x2a2a,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_114 : search 3 [0x3f00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x3f00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_115 : search 3 [0x3f00,0xc0c0,0xfcfc,0xaaaa] = false :=
  noNode 2 [0x3f00,0xc0c0,0xfcfc,0xaaaa] [[0xffc0,0xfcfc,0xaaaa],[0x3c3c,0x3f00,0xaaaa],[0xeaea,0x3f00,0xfcfc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_26 (AllBlocked.cons no_2_80 (AllBlocked.nil))))
private theorem no_3_116 : search 3 [0x3f00,0xeaea,0xcccc,0xf0f0] = false :=
  noNode 2 [0x3f00,0xeaea,0xcccc,0xf0f0] [[0xfcfc,0x3f00,0xeaea]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_182 (AllBlocked.nil))
private theorem no_3_117 : search 3 [0x3f00,0xfcfc,0xc0c0,0xaaaa] = false :=
  noNode 2 [0x3f00,0xfcfc,0xc0c0,0xaaaa] [[0xffc0,0xfcfc,0xaaaa],[0x3c3c,0x3f00,0xaaaa],[0xeaea,0x3f00,0xfcfc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_26 (AllBlocked.cons no_2_80 (AllBlocked.nil))))
private theorem no_3_118 : search 3 [0x4040,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0x4040,0xfcfc,0xaaaa,0xff00] [[0xbcbc,0xaaaa,0xff00],[0xeaea,0xfcfc,0xff00],[0xff40,0xfcfc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_71 (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_203 (AllBlocked.nil))))
private theorem no_3_119 : search 3 [0x4400,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x4400,0xffcc,0xaaaa,0xf0f0] [[0xbbcc,0xaaaa,0xf0f0],[0xeeaa,0xffcc,0xf0f0],[0xf4f0,0xffcc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_70 (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_125 (AllBlocked.nil))))
private theorem no_3_120 : search 3 [0x4444,0x2222,0xf0f0,0xff00] = false :=
  noNode 2 [0x4444,0x2222,0xf0f0,0xff00] [[0x6666,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_57 (AllBlocked.nil))
private theorem no_3_121 : search 3 [0x4444,0xa2a2,0xf0f0,0xff00] = false :=
  noNode 2 [0x4444,0xa2a2,0xf0f0,0xff00] [[0xe6e6,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_78 (AllBlocked.nil))
private theorem no_3_122 : search 3 [0x4444,0xaa22,0xf0f0,0xff00] = false :=
  noNode 2 [0x4444,0xaa22,0xf0f0,0xff00] [[0xee66,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_91 (AllBlocked.nil))
private theorem no_3_123 : search 3 [0x4444,0xf8f8,0xaaaa,0xff00] = false :=
  noNode 2 [0x4444,0xf8f8,0xaaaa,0xff00] [[0xeeee,0xf8f8,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_112 (AllBlocked.nil))
private theorem no_3_124 : search 3 [0x4444,0xff88,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x4444,0xff88,0xaaaa,0xf0f0] [[0xeeee,0xff88,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_118 (AllBlocked.nil))
private theorem no_3_125 : search 3 [0x444c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x444c,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_126 : search 3 [0x44cc,0x50f0,0xaaaa,0xff00] = false :=
  noNode 2 [0x44cc,0x50f0,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_127 : search 3 [0x44cc,0xaa00,0xffaa,0xf0f0] = false :=
  noNode 2 [0x44cc,0xaa00,0xffaa,0xf0f0] [[0xeecc,0xffaa,0xf0f0],[0x55aa,0x44cc,0xf0f0],[0xfaf0,0x44cc,0xffaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_42 (AllBlocked.cons no_2_142 (AllBlocked.nil))))
private theorem no_3_128 : search 3 [0x44cc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x44cc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_129 : search 3 [0x44cc,0xfaf0,0xaaaa,0xff00] = false :=
  noNode 2 [0x44cc,0xfaf0,0xaaaa,0xff00] [[0xffaa,0x44cc,0xfaf0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_218 (AllBlocked.nil))
private theorem no_3_130 : search 3 [0x44cc,0xffaa,0xaa00,0xf0f0] = false :=
  noNode 2 [0x44cc,0xffaa,0xaa00,0xf0f0] [[0xeecc,0xffaa,0xf0f0],[0x55aa,0x44cc,0xf0f0],[0xfaf0,0x44cc,0xffaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_42 (AllBlocked.cons no_2_142 (AllBlocked.nil))))
private theorem no_3_131 : search 3 [0x4c4c,0x5f00,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x4c4c,0x5f00,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_132 : search 3 [0x4c4c,0xa0a0,0xfafa,0xff00] = false :=
  noNode 2 [0x4c4c,0xa0a0,0xfafa,0xff00] [[0xecec,0xfafa,0xff00],[0x5a5a,0x4c4c,0xff00],[0xffa0,0x4c4c,0xfafa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_47 (AllBlocked.cons no_2_210 (AllBlocked.nil))))
private theorem no_3_133 : search 3 [0x4c4c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x4c4c,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_134 : search 3 [0x4c4c,0xfafa,0xa0a0,0xff00] = false :=
  noNode 2 [0x4c4c,0xfafa,0xa0a0,0xff00] [[0xecec,0xfafa,0xff00],[0x5a5a,0x4c4c,0xff00],[0xffa0,0x4c4c,0xfafa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_47 (AllBlocked.cons no_2_210 (AllBlocked.nil))))
private theorem no_3_135 : search 3 [0x4c4c,0xffa0,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x4c4c,0xffa0,0xaaaa,0xf0f0] [[0xfafa,0x4c4c,0xffa0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_150 (AllBlocked.nil))
private theorem no_3_136 : search 3 [0x4ccc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x4ccc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_137 : search 3 [0x5000,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0x5000,0xfff0,0xaaaa,0xcccc] [[0xaff0,0xaaaa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xdccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_68 (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_76 (AllBlocked.nil))))
private theorem no_3_138 : search 3 [0x5050,0xa0a,0xcccc,0xff00] = false :=
  noNode 2 [0x5050,0xa0a,0xcccc,0xff00] [[0x5a5a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_49 (AllBlocked.nil))
private theorem no_3_139 : search 3 [0x5050,0x8a8a,0xcccc,0xff00] = false :=
  noNode 2 [0x5050,0x8a8a,0xcccc,0xff00] [[0xdada,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_75 (AllBlocked.nil))
private theorem no_3_140 : search 3 [0x5050,0xaa0a,0xcccc,0xff00] = false :=
  noNode 2 [0x5050,0xaa0a,0xcccc,0xff00] [[0xfa5a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_133 (AllBlocked.nil))
private theorem no_3_141 : search 3 [0x5050,0xecec,0xaaaa,0xff00] = false :=
  noNode 2 [0x5050,0xecec,0xaaaa,0xff00] [[0xfafa,0xecec,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_154 (AllBlocked.nil))
private theorem no_3_142 : search 3 [0x5050,0xffa0,0xaaaa,0xcccc] = false :=
  noNode 2 [0x5050,0xffa0,0xaaaa,0xcccc] [[0xfafa,0xffa0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_160 (AllBlocked.nil))
private theorem no_3_143 : search 3 [0x5070,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0x5070,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_144 : search 3 [0x50f0,0x44cc,0xaaaa,0xff00] = false :=
  noNode 2 [0x50f0,0x44cc,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_145 : search 3 [0x50f0,0xaa00,0xffaa,0xcccc] = false :=
  noNode 2 [0x50f0,0xaa00,0xffaa,0xcccc] [[0xfaf0,0xffaa,0xcccc],[0x55aa,0x50f0,0xcccc],[0xeecc,0x50f0,0xffaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_146 (AllBlocked.cons no_2_43 (AllBlocked.cons no_2_98 (AllBlocked.nil))))
private theorem no_3_146 : search 3 [0x50f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0x50f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_147 : search 3 [0x50f0,0xeecc,0xaaaa,0xff00] = false :=
  noNode 2 [0x50f0,0xeecc,0xaaaa,0xff00] [[0xffaa,0x50f0,0xeecc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_219 (AllBlocked.nil))
private theorem no_3_148 : search 3 [0x50f0,0xffaa,0xaa00,0xcccc] = false :=
  noNode 2 [0x50f0,0xffaa,0xaa00,0xcccc] [[0xfaf0,0xffaa,0xcccc],[0x55aa,0x50f0,0xcccc],[0xeecc,0x50f0,0xffaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_146 (AllBlocked.cons no_2_43 (AllBlocked.cons no_2_98 (AllBlocked.nil))))
private theorem no_3_149 : search 3 [0x5500,0xaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x5500,0xaa,0xcccc,0xf0f0] [[0x55aa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_44 (AllBlocked.nil))
private theorem no_3_150 : search 3 [0x5500,0x88aa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x5500,0x88aa,0xcccc,0xf0f0] [[0xddaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_77 (AllBlocked.nil))
private theorem no_3_151 : search 3 [0x5500,0xa0aa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x5500,0xa0aa,0xcccc,0xf0f0] [[0xf5aa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_126 (AllBlocked.nil))
private theorem no_3_152 : search 3 [0x5500,0xeecc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x5500,0xeecc,0xaaaa,0xf0f0] [[0xffaa,0xeecc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_222 (AllBlocked.nil))
private theorem no_3_153 : search 3 [0x5500,0xfaf0,0xaaaa,0xcccc] = false :=
  noNode 2 [0x5500,0xfaf0,0xaaaa,0xcccc] [[0xffaa,0xfaf0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_227 (AllBlocked.nil))
private theorem no_3_154 : search 3 [0x5554,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x5554,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_155 : search 3 [0x55aa,0xaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x55aa,0xaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_156 : search 3 [0x55aa,0x5500,0xcccc,0xf0f0] = false :=
  noNode 2 [0x55aa,0x5500,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_157 : search 3 [0x55aa,0xaa00,0xcccc,0xf0f0] = false :=
  noNode 2 [0x55aa,0xaa00,0xcccc,0xf0f0] [[0x44cc,0x55aa,0xf0f0],[0xeecc,0x55aa,0xf0f0],[0x50f0,0x55aa,0xcccc],[0xfaf0,0x55aa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_33 (AllBlocked.cons no_2_99 (AllBlocked.cons no_2_39 (AllBlocked.cons no_2_143 (AllBlocked.nil)))))
private theorem no_3_158 : search 3 [0x55aa,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x55aa,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_159 : search 3 [0x55aa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x55aa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_160 : search 3 [0x55aa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x55aa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_161 : search 3 [0x55aa,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x55aa,0xffaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_162 : search 3 [0x5700,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x5700,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_163 : search 3 [0x5a5a,0xa0a,0xcccc,0xff00] = false :=
  noNode 2 [0x5a5a,0xa0a,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_164 : search 3 [0x5a5a,0x5050,0xcccc,0xff00] = false :=
  noNode 2 [0x5a5a,0x5050,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_165 : search 3 [0x5a5a,0xa0a0,0xcccc,0xff00] = false :=
  noNode 2 [0x5a5a,0xa0a0,0xcccc,0xff00] [[0x4c4c,0x5a5a,0xff00],[0xecec,0x5a5a,0xff00],[0x5f00,0x5a5a,0xcccc],[0xffa0,0x5a5a,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_36 (AllBlocked.cons no_2_85 (AllBlocked.cons no_2_52 (AllBlocked.cons no_2_211 (AllBlocked.nil)))))
private theorem no_3_166 : search 3 [0x5a5a,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0x5a5a,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_167 : search 3 [0x5a5a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x5a5a,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_168 : search 3 [0x5a5a,0xcccc,0xff00] = false :=
  noNode 2 [0x5a5a,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_169 : search 3 [0x5a5a,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0x5a5a,0xfafa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_170 : search 3 [0x5f00,0x4c4c,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x5f00,0x4c4c,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_171 : search 3 [0x5f00,0xa0a0,0xfafa,0xcccc] = false :=
  noNode 2 [0x5f00,0xa0a0,0xfafa,0xcccc] [[0xffa0,0xfafa,0xcccc],[0x5a5a,0x5f00,0xcccc],[0xecec,0x5f00,0xfafa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_214 (AllBlocked.cons no_2_48 (AllBlocked.cons no_2_86 (AllBlocked.nil))))
private theorem no_3_172 : search 3 [0x5f00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x5f00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_173 : search 3 [0x5f00,0xecec,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x5f00,0xecec,0xaaaa,0xf0f0] [[0xfafa,0x5f00,0xecec]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_151 (AllBlocked.nil))
private theorem no_3_174 : search 3 [0x5f00,0xfafa,0xa0a0,0xcccc] = false :=
  noNode 2 [0x5f00,0xfafa,0xa0a0,0xcccc] [[0xffa0,0xfafa,0xcccc],[0x5a5a,0x5f00,0xcccc],[0xecec,0x5f00,0xfafa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_214 (AllBlocked.cons no_2_48 (AllBlocked.cons no_2_86 (AllBlocked.nil))))
private theorem no_3_175 : search 3 [0x6666,0x2222,0xf0f0,0xff00] = false :=
  noNode 2 [0x6666,0x2222,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_176 : search 3 [0x6666,0x4444,0xf0f0,0xff00] = false :=
  noNode 2 [0x6666,0x4444,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_177 : search 3 [0x6666,0x8888,0xf0f0,0xff00] = false :=
  noNode 2 [0x6666,0x8888,0xf0f0,0xff00] [[0x7070,0x6666,0xff00],[0xf8f8,0x6666,0xff00],[0x7700,0x6666,0xf0f0],[0xff88,0x6666,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_60 (AllBlocked.cons no_2_127 (AllBlocked.cons no_2_63 (AllBlocked.cons no_2_204 (AllBlocked.nil)))))
private theorem no_3_178 : search 3 [0x6666,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x6666,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_179 : search 3 [0x6666,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x6666,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_180 : search 3 [0x6666,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0x6666,0xeeee,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_181 : search 3 [0x6666,0xf0f0,0xff00] = false :=
  noNode 2 [0x6666,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_182 : search 3 [0x7070,0x7700,0xaaaa,0xcccc] = false :=
  noNode 2 [0x7070,0x7700,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_183 : search 3 [0x7070,0x8888,0xeeee,0xff00] = false :=
  noNode 2 [0x7070,0x8888,0xeeee,0xff00] [[0xf8f8,0xeeee,0xff00],[0x6666,0x7070,0xff00],[0xff88,0x7070,0xeeee]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_55 (AllBlocked.cons no_2_205 (AllBlocked.nil))))
private theorem no_3_184 : search 3 [0x7070,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0x7070,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_185 : search 3 [0x7070,0xeeee,0x8888,0xff00] = false :=
  noNode 2 [0x7070,0xeeee,0x8888,0xff00] [[0xf8f8,0xeeee,0xff00],[0x6666,0x7070,0xff00],[0xff88,0x7070,0xeeee]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_55 (AllBlocked.cons no_2_205 (AllBlocked.nil))))
private theorem no_3_186 : search 3 [0x7070,0xff88,0xaaaa,0xcccc] = false :=
  noNode 2 [0x7070,0xff88,0xaaaa,0xcccc] [[0xeeee,0x7070,0xff88]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_108 (AllBlocked.nil))
private theorem no_3_187 : search 3 [0x70f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0x70f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_188 : search 3 [0x7700,0x7070,0xaaaa,0xcccc] = false :=
  noNode 2 [0x7700,0x7070,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_189 : search 3 [0x7700,0x8888,0xeeee,0xf0f0] = false :=
  noNode 2 [0x7700,0x8888,0xeeee,0xf0f0] [[0xff88,0xeeee,0xf0f0],[0x6666,0x7700,0xf0f0],[0xf8f8,0x7700,0xeeee]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_207 (AllBlocked.cons no_2_56 (AllBlocked.cons no_2_128 (AllBlocked.nil))))
private theorem no_3_190 : search 3 [0x7700,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x7700,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_191 : search 3 [0x7700,0xeeee,0x8888,0xf0f0] = false :=
  noNode 2 [0x7700,0xeeee,0x8888,0xf0f0] [[0xff88,0xeeee,0xf0f0],[0x6666,0x7700,0xf0f0],[0xf8f8,0x7700,0xeeee]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_207 (AllBlocked.cons no_2_56 (AllBlocked.cons no_2_128 (AllBlocked.nil))))
private theorem no_3_192 : search 3 [0x7700,0xf8f8,0xaaaa,0xcccc] = false :=
  noNode 2 [0x7700,0xf8f8,0xaaaa,0xcccc] [[0xeeee,0x7700,0xf8f8]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_109 (AllBlocked.nil))
private theorem no_3_193 : search 3 [0x7f00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0x7f00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_194 : search 3 [0x8888,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0x8888,0xeeee,0xf0f0,0xff00] [[0x6666,0xf0f0,0xff00],[0xf8f8,0xeeee,0xff00],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_57 (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_207 (AllBlocked.nil))))
private theorem no_3_195 : search 3 [0x88aa,0x5500,0xcccc,0xf0f0] = false :=
  noNode 2 [0x88aa,0x5500,0xcccc,0xf0f0] [[0xddaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_77 (AllBlocked.nil))
private theorem no_3_196 : search 3 [0x88cc,0x3300,0xaaaa,0xf0f0] = false :=
  noNode 2 [0x88cc,0x3300,0xaaaa,0xf0f0] [[0xbbcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_70 (AllBlocked.nil))
private theorem no_3_197 : search 3 [0x8a8a,0x5050,0xcccc,0xff00] = false :=
  noNode 2 [0x8a8a,0x5050,0xcccc,0xff00] [[0xdada,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_75 (AllBlocked.nil))
private theorem no_3_198 : search 3 [0x8aaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0x8aaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_199 : search 3 [0x8c8c,0x3030,0xaaaa,0xff00] = false :=
  noNode 2 [0x8c8c,0x3030,0xaaaa,0xff00] [[0xbcbc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_71 (AllBlocked.nil))
private theorem no_3_200 : search 3 [0x8ccc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0x8ccc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_201 : search 3 [0xa0a0,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0xa0a0,0xfafa,0xcccc,0xff00] [[0x5a5a,0xcccc,0xff00],[0xecec,0xfafa,0xff00],[0xffa0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_49 (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_214 (AllBlocked.nil))))
private theorem no_3_202 : search 3 [0xa0aa,0x5500,0xcccc,0xf0f0] = false :=
  noNode 2 [0xa0aa,0x5500,0xcccc,0xf0f0] [[0xf5aa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_126 (AllBlocked.nil))
private theorem no_3_203 : search 3 [0xa0f0,0xf00,0xaaaa,0xcccc] = false :=
  noNode 2 [0xa0f0,0xf00,0xaaaa,0xcccc] [[0xaff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_68 (AllBlocked.nil))
private theorem no_3_204 : search 3 [0xa2a2,0x4444,0xf0f0,0xff00] = false :=
  noNode 2 [0xa2a2,0x4444,0xf0f0,0xff00] [[0xe6e6,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_78 (AllBlocked.nil))
private theorem no_3_205 : search 3 [0xa2aa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xa2aa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_206 : search 3 [0xa8a8,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0xa8a8,0xeeee,0xf0f0,0xff00] [[0xf8f8,0xeeee,0xff00],[0xffa8,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_216 (AllBlocked.nil)))
private theorem no_3_207 : search 3 [0xa8a8,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0xa8a8,0xfafa,0xcccc,0xff00] [[0xecec,0xfafa,0xff00],[0xffa8,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_217 (AllBlocked.nil)))
private theorem no_3_208 : search 3 [0xaa00,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xaa00,0xffaa,0xcccc,0xf0f0] [[0x55aa,0xcccc,0xf0f0],[0xeecc,0xffaa,0xf0f0],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_44 (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_146 (AllBlocked.nil))))
private theorem no_3_209 : search 3 [0xaa0a,0x5050,0xcccc,0xff00] = false :=
  noNode 2 [0xaa0a,0x5050,0xcccc,0xff00] [[0xfa5a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_133 (AllBlocked.nil))
private theorem no_3_210 : search 3 [0xaa22,0x4444,0xf0f0,0xff00] = false :=
  noNode 2 [0xaa22,0x4444,0xf0f0,0xff00] [[0xee66,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_91 (AllBlocked.nil))
private theorem no_3_211 : search 3 [0xaa2a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xaa2a,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_212 : search 3 [0xaa88,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0xaa88,0xeeee,0xf0f0,0xff00] [[0xfaf8,0xeeee,0xff00],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_148 (AllBlocked.cons no_2_207 (AllBlocked.nil)))
private theorem no_3_213 : search 3 [0xaa88,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xaa88,0xffaa,0xcccc,0xf0f0] [[0xeecc,0xffaa,0xf0f0],[0xfaf8,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_149 (AllBlocked.nil)))
private theorem no_3_214 : search 3 [0xaaa0,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0xaaa0,0xfafa,0xcccc,0xff00] [[0xeeec,0xfafa,0xff00],[0xffa0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_106 (AllBlocked.cons no_2_214 (AllBlocked.nil)))
private theorem no_3_215 : search 3 [0xaaa0,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xaaa0,0xffaa,0xcccc,0xf0f0] [[0xeeec,0xffaa,0xf0f0],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_107 (AllBlocked.cons no_2_146 (AllBlocked.nil)))
private theorem no_3_216 : search 3 [0xaaa8,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xaaa8,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_217 : search 3 [0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_218 : search 3 [0xaaea,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xaaea,0xcccc,0xf0f0,0xff00] [[0xfcfc,0xaaea,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_183 (AllBlocked.nil))
private theorem no_3_219 : search 3 [0xaeaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xaeaa,0xcccc,0xf0f0,0xff00] [[0xffcc,0xaeaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_242 (AllBlocked.nil))
private theorem no_3_220 : search 3 [0xaf00,0xf0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xaf00,0xf0,0xaaaa,0xcccc] [[0xaff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_68 (AllBlocked.nil))
private theorem no_3_221 : search 3 [0xb0b0,0xc0c,0xaaaa,0xff00] = false :=
  noNode 2 [0xb0b0,0xc0c,0xaaaa,0xff00] [[0xbcbc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_71 (AllBlocked.nil))
private theorem no_3_222 : search 3 [0xb0f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xb0f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_223 : search 3 [0xbaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xbaaa,0xcccc,0xf0f0,0xff00] [[0xfff0,0xbaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_258 (AllBlocked.nil))
private theorem no_3_224 : search 3 [0xbb00,0xcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xbb00,0xcc,0xaaaa,0xf0f0] [[0xbbcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_70 (AllBlocked.nil))
private theorem no_3_225 : search 3 [0xbf00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xbf00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_226 : search 3 [0xc0c0,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0xc0c0,0xfcfc,0xaaaa,0xff00] [[0x3c3c,0xaaaa,0xff00],[0xffc0,0xfcfc,0xaaaa],[0xeaea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_27 (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_82 (AllBlocked.nil))))
private theorem no_3_227 : search 3 [0xc0cc,0x3300,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xc0cc,0x3300,0xaaaa,0xf0f0] [[0xf3cc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_124 (AllBlocked.nil))
private theorem no_3_228 : search 3 [0xc0f0,0xf00,0xaaaa,0xcccc] = false :=
  noNode 2 [0xc0f0,0xf00,0xaaaa,0xcccc] [[0xcff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_74 (AllBlocked.nil))
private theorem no_3_229 : search 3 [0xc4c4,0x2222,0xf0f0,0xff00] = false :=
  noNode 2 [0xc4c4,0x2222,0xf0f0,0xff00] [[0xe6e6,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_78 (AllBlocked.nil))
private theorem no_3_230 : search 3 [0xc4cc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xc4cc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_231 : search 3 [0xc8c8,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0xc8c8,0xeeee,0xf0f0,0xff00] [[0xf8f8,0xeeee,0xff00],[0xffc8,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_238 (AllBlocked.nil)))
private theorem no_3_232 : search 3 [0xc8c8,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0xc8c8,0xfcfc,0xaaaa,0xff00] [[0xffc8,0xfcfc,0xaaaa],[0xeaea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_239 (AllBlocked.cons no_2_82 (AllBlocked.nil)))
private theorem no_3_233 : search 3 [0xcc00,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xcc00,0xffcc,0xaaaa,0xf0f0] [[0x33cc,0xaaaa,0xf0f0],[0xfcf0,0xffcc,0xaaaa],[0xeeaa,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_22 (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_96 (AllBlocked.nil))))
private theorem no_3_234 : search 3 [0xcc0c,0x3030,0xaaaa,0xff00] = false :=
  noNode 2 [0xcc0c,0x3030,0xaaaa,0xff00] [[0xfc3c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_164 (AllBlocked.nil))
private theorem no_3_235 : search 3 [0xcc44,0x2222,0xf0f0,0xff00] = false :=
  noNode 2 [0xcc44,0x2222,0xf0f0,0xff00] [[0xee66,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_91 (AllBlocked.nil))
private theorem no_3_236 : search 3 [0xcc4c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xcc4c,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_237 : search 3 [0xcc88,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0xcc88,0xeeee,0xf0f0,0xff00] [[0xfcf8,0xeeee,0xff00],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_179 (AllBlocked.cons no_2_207 (AllBlocked.nil)))
private theorem no_3_238 : search 3 [0xcc88,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xcc88,0xffcc,0xaaaa,0xf0f0] [[0xfcf8,0xffcc,0xaaaa],[0xeeaa,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_180 (AllBlocked.cons no_2_96 (AllBlocked.nil)))
private theorem no_3_239 : search 3 [0xccc0,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0xccc0,0xfcfc,0xaaaa,0xff00] [[0xffc0,0xfcfc,0xaaaa],[0xeeea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_104 (AllBlocked.nil)))
private theorem no_3_240 : search 3 [0xccc0,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xccc0,0xffcc,0xaaaa,0xf0f0] [[0xfcf0,0xffcc,0xaaaa],[0xeeea,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_105 (AllBlocked.nil)))
private theorem no_3_241 : search 3 [0xccc8,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xccc8,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_242 : search 3 [0xcccc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xcccc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_243 : search 3 [0xccec,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xccec,0xaaaa,0xf0f0,0xff00] [[0xfafa,0xccec,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_152 (AllBlocked.nil))
private theorem no_3_244 : search 3 [0xcecc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xcecc,0xaaaa,0xf0f0,0xff00] [[0xffaa,0xcecc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_220 (AllBlocked.nil))
private theorem no_3_245 : search 3 [0xcf00,0xf0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xcf00,0xf0,0xaaaa,0xcccc] [[0xcff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_74 (AllBlocked.nil))
private theorem no_3_246 : search 3 [0xd0d0,0xa0a,0xcccc,0xff00] = false :=
  noNode 2 [0xd0d0,0xa0a,0xcccc,0xff00] [[0xdada,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_75 (AllBlocked.nil))
private theorem no_3_247 : search 3 [0xd0f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xd0f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_248 : search 3 [0xdccc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xdccc,0xaaaa,0xf0f0,0xff00] [[0xfff0,0xdccc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_259 (AllBlocked.nil))
private theorem no_3_249 : search 3 [0xdd00,0xaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xdd00,0xaa,0xcccc,0xf0f0] [[0xddaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_77 (AllBlocked.nil))
private theorem no_3_250 : search 3 [0xdf00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xdf00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_251 : search 3 [0xe0e0,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0xe0e0,0xfafa,0xcccc,0xff00] [[0xffe0,0xfafa,0xcccc],[0xecec,0xfafa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_254 (AllBlocked.cons no_2_88 (AllBlocked.nil)))
private theorem no_3_252 : search 3 [0xe0e0,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0xe0e0,0xfcfc,0xaaaa,0xff00] [[0xffe0,0xfcfc,0xaaaa],[0xeaea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_255 (AllBlocked.cons no_2_82 (AllBlocked.nil)))
private theorem no_3_253 : search 3 [0xeaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xeaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_254 : search 3 [0xeaea,0xc0c,0xf0f0,0xff00] = false :=
  noNode 2 [0xeaea,0xc0c,0xf0f0,0xff00] [[0xfcfc,0xeaea,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_185 (AllBlocked.nil))
private theorem no_3_255 : search 3 [0xeaea,0x3030,0xcccc,0xff00] = false :=
  noNode 2 [0xeaea,0x3030,0xcccc,0xff00] [[0xfcfc,0xeaea,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_185 (AllBlocked.nil))
private theorem no_3_256 : search 3 [0xeaea,0x3f00,0xcccc,0xf0f0] = false :=
  noNode 2 [0xeaea,0x3f00,0xcccc,0xf0f0] [[0xfcfc,0xeaea,0x3f00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_184 (AllBlocked.nil))
private theorem no_3_257 : search 3 [0xeaea,0xc0c0,0xfcfc,0xff00] = false :=
  noNode 2 [0xeaea,0xc0c0,0xfcfc,0xff00] [[0x3c3c,0xeaea,0xff00],[0x3f00,0xeaea,0xfcfc],[0xffc0,0xeaea,0xfcfc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_28 (AllBlocked.cons no_2_31 (AllBlocked.cons no_2_234 (AllBlocked.nil))))
private theorem no_3_258 : search 3 [0xeaea,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xeaea,0xcccc,0xf0f0,0xff00] [[0xfcfc,0xeaea,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_185 (AllBlocked.nil))
private theorem no_3_259 : search 3 [0xeaea,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0xeaea,0xfcfc,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_260 : search 3 [0xeaea,0xfcfc,0xc0c0,0xff00] = false :=
  noNode 2 [0xeaea,0xfcfc,0xc0c0,0xff00] [[0x3c3c,0xeaea,0xff00],[0x3f00,0xeaea,0xfcfc],[0xffc0,0xeaea,0xfcfc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_28 (AllBlocked.cons no_2_31 (AllBlocked.cons no_2_234 (AllBlocked.nil))))
private theorem no_3_261 : search 3 [0xeaea,0xfcfc,0xcccc,0xff00] = false :=
  noNode 2 [0xeaea,0xfcfc,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_262 : search 3 [0xeaea,0xfcfc,0xf0f0,0xff00] = false :=
  noNode 2 [0xeaea,0xfcfc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_263 : search 3 [0xeaea,0xfcfc,0xff00] = false :=
  noNode 2 [0xeaea,0xfcfc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_264 : search 3 [0xeaea,0xffc0,0xcccc,0xf0f0] = false :=
  noNode 2 [0xeaea,0xffc0,0xcccc,0xf0f0] [[0xfcfc,0xeaea,0xffc0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_186 (AllBlocked.nil))
private theorem no_3_265 : search 3 [0xeccc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xeccc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_266 : search 3 [0xecec,0xa0a,0xf0f0,0xff00] = false :=
  noNode 2 [0xecec,0xa0a,0xf0f0,0xff00] [[0xfafa,0xecec,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_154 (AllBlocked.nil))
private theorem no_3_267 : search 3 [0xecec,0x5050,0xaaaa,0xff00] = false :=
  noNode 2 [0xecec,0x5050,0xaaaa,0xff00] [[0xfafa,0xecec,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_154 (AllBlocked.nil))
private theorem no_3_268 : search 3 [0xecec,0x5f00,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xecec,0x5f00,0xaaaa,0xf0f0] [[0xfafa,0xecec,0x5f00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_153 (AllBlocked.nil))
private theorem no_3_269 : search 3 [0xecec,0xa0a0,0xfafa,0xff00] = false :=
  noNode 2 [0xecec,0xa0a0,0xfafa,0xff00] [[0x5a5a,0xecec,0xff00],[0x5f00,0xecec,0xfafa],[0xffa0,0xecec,0xfafa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_50 (AllBlocked.cons no_2_53 (AllBlocked.cons no_2_212 (AllBlocked.nil))))
private theorem no_3_270 : search 3 [0xecec,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xecec,0xaaaa,0xf0f0,0xff00] [[0xfafa,0xecec,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_154 (AllBlocked.nil))
private theorem no_3_271 : search 3 [0xecec,0xfafa,0xa0a0,0xff00] = false :=
  noNode 2 [0xecec,0xfafa,0xa0a0,0xff00] [[0x5a5a,0xecec,0xff00],[0x5f00,0xecec,0xfafa],[0xffa0,0xecec,0xfafa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_50 (AllBlocked.cons no_2_53 (AllBlocked.cons no_2_212 (AllBlocked.nil))))
private theorem no_3_272 : search 3 [0xecec,0xfafa,0xaaaa,0xff00] = false :=
  noNode 2 [0xecec,0xfafa,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_273 : search 3 [0xecec,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0xecec,0xfafa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_274 : search 3 [0xecec,0xfafa,0xf0f0,0xff00] = false :=
  noNode 2 [0xecec,0xfafa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_275 : search 3 [0xecec,0xfafa,0xff00] = false :=
  noNode 2 [0xecec,0xfafa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_276 : search 3 [0xecec,0xffa0,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xecec,0xffa0,0xaaaa,0xf0f0] [[0xfafa,0xecec,0xffa0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_155 (AllBlocked.nil))
private theorem no_3_277 : search 3 [0xee00,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xee00,0xffaa,0xcccc,0xf0f0] [[0xfef0,0xffaa,0xcccc],[0xeecc,0xffaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_199 (AllBlocked.cons no_2_102 (AllBlocked.nil)))
private theorem no_3_278 : search 3 [0xee00,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xee00,0xffcc,0xaaaa,0xf0f0] [[0xfef0,0xffcc,0xaaaa],[0xeeaa,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_200 (AllBlocked.cons no_2_96 (AllBlocked.nil)))
private theorem no_3_279 : search 3 [0xeeaa,0xcc,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeaa,0xcc,0xf0f0,0xff00] [[0xffcc,0xeeaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_244 (AllBlocked.nil))
private theorem no_3_280 : search 3 [0xeeaa,0x30f0,0xcccc,0xff00] = false :=
  noNode 2 [0xeeaa,0x30f0,0xcccc,0xff00] [[0xffcc,0xeeaa,0x30f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_243 (AllBlocked.nil))
private theorem no_3_281 : search 3 [0xeeaa,0x3300,0xcccc,0xf0f0] = false :=
  noNode 2 [0xeeaa,0x3300,0xcccc,0xf0f0] [[0xffcc,0xeeaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_244 (AllBlocked.nil))
private theorem no_3_282 : search 3 [0xeeaa,0xcc00,0xffcc,0xf0f0] = false :=
  noNode 2 [0xeeaa,0xcc00,0xffcc,0xf0f0] [[0x33cc,0xeeaa,0xf0f0],[0x30f0,0xeeaa,0xffcc],[0xfcf0,0xeeaa,0xffcc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_23 (AllBlocked.cons no_2_18 (AllBlocked.cons no_2_175 (AllBlocked.nil))))
private theorem no_3_283 : search 3 [0xeeaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeaa,0xcccc,0xf0f0,0xff00] [[0xffcc,0xeeaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_244 (AllBlocked.nil))
private theorem no_3_284 : search 3 [0xeeaa,0xfcf0,0xcccc,0xff00] = false :=
  noNode 2 [0xeeaa,0xfcf0,0xcccc,0xff00] [[0xffcc,0xeeaa,0xfcf0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_245 (AllBlocked.nil))
private theorem no_3_285 : search 3 [0xeeaa,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xeeaa,0xffcc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_286 : search 3 [0xeeaa,0xffcc,0xcc00,0xf0f0] = false :=
  noNode 2 [0xeeaa,0xffcc,0xcc00,0xf0f0] [[0x33cc,0xeeaa,0xf0f0],[0x30f0,0xeeaa,0xffcc],[0xfcf0,0xeeaa,0xffcc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_23 (AllBlocked.cons no_2_18 (AllBlocked.cons no_2_175 (AllBlocked.nil))))
private theorem no_3_287 : search 3 [0xeeaa,0xffcc,0xcccc,0xf0f0] = false :=
  noNode 2 [0xeeaa,0xffcc,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_288 : search 3 [0xeeaa,0xffcc,0xf0f0] = false :=
  noNode 2 [0xeeaa,0xffcc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_289 : search 3 [0xeeaa,0xffcc,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeaa,0xffcc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_290 : search 3 [0xeecc,0xaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xeecc,0xaa,0xf0f0,0xff00] [[0xffaa,0xeecc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_222 (AllBlocked.nil))
private theorem no_3_291 : search 3 [0xeecc,0x50f0,0xaaaa,0xff00] = false :=
  noNode 2 [0xeecc,0x50f0,0xaaaa,0xff00] [[0xffaa,0xeecc,0x50f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_221 (AllBlocked.nil))
private theorem no_3_292 : search 3 [0xeecc,0x5500,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xeecc,0x5500,0xaaaa,0xf0f0] [[0xffaa,0xeecc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_222 (AllBlocked.nil))
private theorem no_3_293 : search 3 [0xeecc,0xaa00,0xffaa,0xf0f0] = false :=
  noNode 2 [0xeecc,0xaa00,0xffaa,0xf0f0] [[0x55aa,0xeecc,0xf0f0],[0x50f0,0xeecc,0xffaa],[0xfaf0,0xeecc,0xffaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_45 (AllBlocked.cons no_2_40 (AllBlocked.cons no_2_144 (AllBlocked.nil))))
private theorem no_3_294 : search 3 [0xeecc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xeecc,0xaaaa,0xf0f0,0xff00] [[0xffaa,0xeecc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_222 (AllBlocked.nil))
private theorem no_3_295 : search 3 [0xeecc,0xfaf0,0xaaaa,0xff00] = false :=
  noNode 2 [0xeecc,0xfaf0,0xaaaa,0xff00] [[0xffaa,0xeecc,0xfaf0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_223 (AllBlocked.nil))
private theorem no_3_296 : search 3 [0xeecc,0xffaa,0xaa00,0xf0f0] = false :=
  noNode 2 [0xeecc,0xffaa,0xaa00,0xf0f0] [[0x55aa,0xeecc,0xf0f0],[0x50f0,0xeecc,0xffaa],[0xfaf0,0xeecc,0xffaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_45 (AllBlocked.cons no_2_40 (AllBlocked.cons no_2_144 (AllBlocked.nil))))
private theorem no_3_297 : search 3 [0xeecc,0xffaa,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xeecc,0xffaa,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_298 : search 3 [0xeecc,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xeecc,0xffaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_299 : search 3 [0xeecc,0xffaa,0xf0f0] = false :=
  noNode 2 [0xeecc,0xffaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_300 : search 3 [0xeecc,0xffaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xeecc,0xffaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_301 : search 3 [0xeeea,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeea,0xcccc,0xf0f0,0xff00] [[0xfcfc,0xeeea,0xff00],[0xffcc,0xeeea,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_187 (AllBlocked.cons no_2_246 (AllBlocked.nil)))
private theorem no_3_302 : search 3 [0xeeec,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeec,0xaaaa,0xf0f0,0xff00] [[0xfafa,0xeeec,0xff00],[0xffaa,0xeeec,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_156 (AllBlocked.cons no_2_224 (AllBlocked.nil)))
private theorem no_3_303 : search 3 [0xeeee,0x88,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeee,0x88,0xf0f0,0xff00] [[0xee66,0xf0f0,0xff00],[0xf0f8,0xeeee,0xff00],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_91 (AllBlocked.cons no_2_122 (AllBlocked.cons no_2_207 (AllBlocked.nil))))
private theorem no_3_304 : search 3 [0xeeee,0x808,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeee,0x808,0xf0f0,0xff00] [[0xe6e6,0xf0f0,0xff00],[0xf8f8,0xeeee,0xff00],[0xff08,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_78 (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_201 (AllBlocked.nil))))
private theorem no_3_305 : search 3 [0xeeee,0x7070,0x8888,0xff00] = false :=
  noNode 2 [0xeeee,0x7070,0x8888,0xff00] [[0xf8f8,0xeeee,0xff00],[0x6666,0x7070,0xff00],[0xff88,0xeeee,0x7070]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_55 (AllBlocked.cons no_2_206 (AllBlocked.nil))))
private theorem no_3_306 : search 3 [0xeeee,0x7700,0x8888,0xf0f0] = false :=
  noNode 2 [0xeeee,0x7700,0x8888,0xf0f0] [[0xff88,0xeeee,0xf0f0],[0x6666,0x7700,0xf0f0],[0xf8f8,0xeeee,0x7700]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_207 (AllBlocked.cons no_2_56 (AllBlocked.cons no_2_129 (AllBlocked.nil))))
private theorem no_3_307 : search 3 [0xeeee,0x8888,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeee,0x8888,0xf0f0,0xff00] [[0x6666,0xf0f0,0xff00],[0xf8f8,0xeeee,0xff00],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_57 (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_207 (AllBlocked.nil))))
private theorem no_3_308 : search 3 [0xeeee,0xa8a8,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeee,0xa8a8,0xf0f0,0xff00] [[0xf8f8,0xeeee,0xff00],[0xffa8,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_216 (AllBlocked.nil)))
private theorem no_3_309 : search 3 [0xeeee,0xaa88,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeee,0xaa88,0xf0f0,0xff00] [[0xfaf8,0xeeee,0xff00],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_148 (AllBlocked.cons no_2_207 (AllBlocked.nil)))
private theorem no_3_310 : search 3 [0xeeee,0xc8c8,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeee,0xc8c8,0xf0f0,0xff00] [[0xf8f8,0xeeee,0xff00],[0xffc8,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_238 (AllBlocked.nil)))
private theorem no_3_311 : search 3 [0xeeee,0xcc88,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeee,0xcc88,0xf0f0,0xff00] [[0xfcf8,0xeeee,0xff00],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_179 (AllBlocked.cons no_2_207 (AllBlocked.nil)))
private theorem no_3_312 : search 3 [0xeeee,0xf8f8,0x8888,0xff00] = false :=
  noNode 2 [0xeeee,0xf8f8,0x8888,0xff00] [[0x6666,0xf8f8,0xff00],[0x7700,0xeeee,0xf8f8],[0xff88,0xeeee,0xf8f8]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_58 (AllBlocked.cons no_2_64 (AllBlocked.cons no_2_208 (AllBlocked.nil))))
private theorem no_3_313 : search 3 [0xeeee,0xf8f8,0xaaaa,0xff00] = false :=
  noNode 2 [0xeeee,0xf8f8,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_314 : search 3 [0xeeee,0xf8f8,0xcccc,0xff00] = false :=
  noNode 2 [0xeeee,0xf8f8,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_315 : search 3 [0xeeee,0xf8f8,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeee,0xf8f8,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_316 : search 3 [0xeeee,0xf8f8,0xff00] = false :=
  noNode 2 [0xeeee,0xf8f8,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_317 : search 3 [0xeeee,0xfafa,0xfcfc,0xff00] = false :=
  noNode 2 [0xeeee,0xfafa,0xfcfc,0xff00] [[0xeaea,0xfcfc,0xff00],[0xecec,0xfafa,0xff00],[0xf8f8,0xeeee,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_130 (AllBlocked.nil))))
private theorem no_3_318 : search 3 [0xeeee,0xfcfc,0xfafa,0xff00] = false :=
  noNode 2 [0xeeee,0xfcfc,0xfafa,0xff00] [[0xecec,0xfafa,0xff00],[0xeaea,0xfcfc,0xff00],[0xf8f8,0xeeee,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_130 (AllBlocked.nil))))
private theorem no_3_319 : search 3 [0xeeee,0xff88,0x8888,0xf0f0] = false :=
  noNode 2 [0xeeee,0xff88,0x8888,0xf0f0] [[0x6666,0xff88,0xf0f0],[0x7070,0xeeee,0xff88],[0xf8f8,0xeeee,0xff88]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_59 (AllBlocked.cons no_2_61 (AllBlocked.cons no_2_131 (AllBlocked.nil))))
private theorem no_3_320 : search 3 [0xeeee,0xff88,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xeeee,0xff88,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_321 : search 3 [0xeeee,0xff88,0xcccc,0xf0f0] = false :=
  noNode 2 [0xeeee,0xff88,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_322 : search 3 [0xeeee,0xff88,0xf0f0] = false :=
  noNode 2 [0xeeee,0xff88,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_323 : search 3 [0xeeee,0xff88,0xf0f0,0xff00] = false :=
  noNode 2 [0xeeee,0xff88,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_324 : search 3 [0xeeee,0xffaa,0xffcc,0xf0f0] = false :=
  noNode 2 [0xeeee,0xffaa,0xffcc,0xf0f0] [[0xeeaa,0xffcc,0xf0f0],[0xeecc,0xffaa,0xf0f0],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_207 (AllBlocked.nil))))
private theorem no_3_325 : search 3 [0xeeee,0xffcc,0xffaa,0xf0f0] = false :=
  noNode 2 [0xeeee,0xffcc,0xffaa,0xf0f0] [[0xeecc,0xffaa,0xf0f0],[0xeeaa,0xffcc,0xf0f0],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_207 (AllBlocked.nil))))
private theorem no_3_326 : search 3 [0xf000,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf000,0xfff0,0xaaaa,0xcccc] [[0xff0,0xaaaa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xfccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_8 (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_169 (AllBlocked.nil))))
private theorem no_3_327 : search 3 [0xf030,0xc0c,0xaaaa,0xff00] = false :=
  noNode 2 [0xf030,0xc0c,0xaaaa,0xff00] [[0xfc3c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_164 (AllBlocked.nil))
private theorem no_3_328 : search 3 [0xf050,0xa0a,0xcccc,0xff00] = false :=
  noNode 2 [0xf050,0xa0a,0xcccc,0xff00] [[0xfa5a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_133 (AllBlocked.nil))
private theorem no_3_329 : search 3 [0xf070,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf070,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_330 : search 3 [0xf0a0,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0xf0a0,0xfafa,0xcccc,0xff00] [[0xffa0,0xfafa,0xcccc],[0xfcec,0xfafa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_214 (AllBlocked.cons no_2_171 (AllBlocked.nil)))
private theorem no_3_331 : search 3 [0xf0a0,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf0a0,0xfff0,0xaaaa,0xcccc] [[0xfaaa,0xfff0,0xcccc],[0xfcec,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_172 (AllBlocked.nil)))
private theorem no_3_332 : search 3 [0xf0c0,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0xf0c0,0xfcfc,0xaaaa,0xff00] [[0xffc0,0xfcfc,0xaaaa],[0xfaea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_140 (AllBlocked.nil)))
private theorem no_3_333 : search 3 [0xf0c0,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf0c0,0xfff0,0xaaaa,0xcccc] [[0xfaea,0xfff0,0xcccc],[0xfccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_141 (AllBlocked.cons no_2_169 (AllBlocked.nil)))
private theorem no_3_334 : search 3 [0xf0e0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf0e0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_335 : search 3 [0xf0f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf0f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_336 : search 3 [0xf0f8,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf0f8,0xaaaa,0xcccc,0xff00] [[0xeeee,0xf0f8,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_110 (AllBlocked.nil))
private theorem no_3_337 : search 3 [0xf2f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf2f0,0xaaaa,0xcccc,0xff00] [[0xffaa,0xf2f0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_225 (AllBlocked.nil))
private theorem no_3_338 : search 3 [0xf300,0xcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xf300,0xcc,0xaaaa,0xf0f0] [[0xf3cc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_124 (AllBlocked.nil))
private theorem no_3_339 : search 3 [0xf4f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf4f0,0xaaaa,0xcccc,0xff00] [[0xffcc,0xf4f0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_247 (AllBlocked.nil))
private theorem no_3_340 : search 3 [0xf500,0xaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xf500,0xaa,0xcccc,0xf0f0] [[0xf5aa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_126 (AllBlocked.nil))
private theorem no_3_341 : search 3 [0xf700,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xf700,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_342 : search 3 [0xf8f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf8f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_343 : search 3 [0xf8f8,0x2222,0xcccc,0xff00] = false :=
  noNode 2 [0xf8f8,0x2222,0xcccc,0xff00] [[0xeeee,0xf8f8,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_112 (AllBlocked.nil))
private theorem no_3_344 : search 3 [0xf8f8,0x4444,0xaaaa,0xff00] = false :=
  noNode 2 [0xf8f8,0x4444,0xaaaa,0xff00] [[0xeeee,0xf8f8,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_112 (AllBlocked.nil))
private theorem no_3_345 : search 3 [0xf8f8,0x7700,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf8f8,0x7700,0xaaaa,0xcccc] [[0xeeee,0xf8f8,0x7700]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_111 (AllBlocked.nil))
private theorem no_3_346 : search 3 [0xf8f8,0x8888,0xeeee,0xff00] = false :=
  noNode 2 [0xf8f8,0x8888,0xeeee,0xff00] [[0x6666,0xf8f8,0xff00],[0x7700,0xf8f8,0xeeee],[0xff88,0xf8f8,0xeeee]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_58 (AllBlocked.cons no_2_65 (AllBlocked.cons no_2_209 (AllBlocked.nil))))
private theorem no_3_347 : search 3 [0xf8f8,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xf8f8,0xaaaa,0xcccc,0xff00] [[0xeeee,0xf8f8,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_112 (AllBlocked.nil))
private theorem no_3_348 : search 3 [0xf8f8,0xeeee,0x8888,0xff00] = false :=
  noNode 2 [0xf8f8,0xeeee,0x8888,0xff00] [[0x6666,0xf8f8,0xff00],[0x7700,0xf8f8,0xeeee],[0xff88,0xf8f8,0xeeee]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_58 (AllBlocked.cons no_2_65 (AllBlocked.cons no_2_209 (AllBlocked.nil))))
private theorem no_3_349 : search 3 [0xf8f8,0xeeee,0xaaaa,0xff00] = false :=
  noNode 2 [0xf8f8,0xeeee,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_350 : search 3 [0xf8f8,0xeeee,0xcccc,0xff00] = false :=
  noNode 2 [0xf8f8,0xeeee,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_351 : search 3 [0xf8f8,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0xf8f8,0xeeee,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_352 : search 3 [0xf8f8,0xeeee,0xff00] = false :=
  noNode 2 [0xf8f8,0xeeee,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_353 : search 3 [0xf8f8,0xff88,0xaaaa,0xcccc] = false :=
  noNode 2 [0xf8f8,0xff88,0xaaaa,0xcccc] [[0xeeee,0xf8f8,0xff88]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_113 (AllBlocked.nil))
private theorem no_3_354 : search 3 [0xfa00,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xfa00,0xffaa,0xcccc,0xf0f0] [[0xfecc,0xffaa,0xf0f0],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_197 (AllBlocked.cons no_2_146 (AllBlocked.nil)))
private theorem no_3_355 : search 3 [0xfa00,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfa00,0xfff0,0xaaaa,0xcccc] [[0xfaaa,0xfff0,0xcccc],[0xfecc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_198 (AllBlocked.nil)))
private theorem no_3_356 : search 3 [0xfaaa,0xf0,0xcccc,0xff00] = false :=
  noNode 2 [0xfaaa,0xf0,0xcccc,0xff00] [[0xfff0,0xfaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_261 (AllBlocked.nil))
private theorem no_3_357 : search 3 [0xfaaa,0xccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xfaaa,0xccc,0xf0f0,0xff00] [[0xfff0,0xfaaa,0xccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_260 (AllBlocked.nil))
private theorem no_3_358 : search 3 [0xfaaa,0xf00,0xcccc,0xf0f0] = false :=
  noNode 2 [0xfaaa,0xf00,0xcccc,0xf0f0] [[0xfff0,0xfaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_261 (AllBlocked.nil))
private theorem no_3_359 : search 3 [0xfaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xfaaa,0xcccc,0xf0f0,0xff00] [[0xfff0,0xfaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_261 (AllBlocked.nil))
private theorem no_3_360 : search 3 [0xfaaa,0xf000,0xfff0,0xcccc] = false :=
  noNode 2 [0xfaaa,0xf000,0xfff0,0xcccc] [[0xff0,0xfaaa,0xcccc],[0xccc,0xfaaa,0xfff0],[0xfccc,0xfaaa,0xfff0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_9 (AllBlocked.cons no_2_4 (AllBlocked.cons no_2_167 (AllBlocked.nil))))
private theorem no_3_361 : search 3 [0xfaaa,0xfccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xfaaa,0xfccc,0xf0f0,0xff00] [[0xfff0,0xfaaa,0xfccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_262 (AllBlocked.nil))
private theorem no_3_362 : search 3 [0xfaaa,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfaaa,0xfff0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_363 : search 3 [0xfaaa,0xfff0,0xcccc] = false :=
  noNode 2 [0xfaaa,0xfff0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_364 : search 3 [0xfaaa,0xfff0,0xcccc,0xf0f0] = false :=
  noNode 2 [0xfaaa,0xfff0,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_365 : search 3 [0xfaaa,0xfff0,0xcccc,0xff00] = false :=
  noNode 2 [0xfaaa,0xfff0,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_366 : search 3 [0xfaaa,0xfff0,0xf000,0xcccc] = false :=
  noNode 2 [0xfaaa,0xfff0,0xf000,0xcccc] [[0xff0,0xfaaa,0xcccc],[0xccc,0xfaaa,0xfff0],[0xfccc,0xfaaa,0xfff0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_9 (AllBlocked.cons no_2_4 (AllBlocked.cons no_2_167 (AllBlocked.nil))))
private theorem no_3_367 : search 3 [0xfaea,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xfaea,0xcccc,0xf0f0,0xff00] [[0xfcfc,0xfaea,0xff00],[0xfff0,0xfaea,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_188 (AllBlocked.cons no_2_263 (AllBlocked.nil)))
private theorem no_3_368 : search 3 [0xfaf0,0xaa,0xcccc,0xff00] = false :=
  noNode 2 [0xfaf0,0xaa,0xcccc,0xff00] [[0xffaa,0xfaf0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_227 (AllBlocked.nil))
private theorem no_3_369 : search 3 [0xfaf0,0x44cc,0xaaaa,0xff00] = false :=
  noNode 2 [0xfaf0,0x44cc,0xaaaa,0xff00] [[0xffaa,0xfaf0,0x44cc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_226 (AllBlocked.nil))
private theorem no_3_370 : search 3 [0xfaf0,0x5500,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfaf0,0x5500,0xaaaa,0xcccc] [[0xffaa,0xfaf0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_227 (AllBlocked.nil))
private theorem no_3_371 : search 3 [0xfaf0,0xaa00,0xffaa,0xcccc] = false :=
  noNode 2 [0xfaf0,0xaa00,0xffaa,0xcccc] [[0x55aa,0xfaf0,0xcccc],[0x44cc,0xfaf0,0xffaa],[0xeecc,0xfaf0,0xffaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_46 (AllBlocked.cons no_2_34 (AllBlocked.cons no_2_100 (AllBlocked.nil))))
private theorem no_3_372 : search 3 [0xfaf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xfaf0,0xaaaa,0xcccc,0xff00] [[0xffaa,0xfaf0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_227 (AllBlocked.nil))
private theorem no_3_373 : search 3 [0xfaf0,0xeecc,0xaaaa,0xff00] = false :=
  noNode 2 [0xfaf0,0xeecc,0xaaaa,0xff00] [[0xffaa,0xfaf0,0xeecc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_228 (AllBlocked.nil))
private theorem no_3_374 : search 3 [0xfaf0,0xffaa,0xaa00,0xcccc] = false :=
  noNode 2 [0xfaf0,0xffaa,0xaa00,0xcccc] [[0x55aa,0xfaf0,0xcccc],[0x44cc,0xfaf0,0xffaa],[0xeecc,0xfaf0,0xffaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_46 (AllBlocked.cons no_2_34 (AllBlocked.cons no_2_100 (AllBlocked.nil))))
private theorem no_3_375 : search 3 [0xfaf0,0xffaa,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfaf0,0xffaa,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_376 : search 3 [0xfaf0,0xffaa,0xcccc] = false :=
  noNode 2 [0xfaf0,0xffaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_377 : search 3 [0xfaf0,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xfaf0,0xffaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_378 : search 3 [0xfaf0,0xffaa,0xcccc,0xff00] = false :=
  noNode 2 [0xfaf0,0xffaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_379 : search 3 [0xfaf8,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xfaf8,0xaaaa,0xcccc,0xff00] [[0xeeee,0xfaf8,0xff00],[0xffaa,0xfaf8,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_114 (AllBlocked.cons no_2_229 (AllBlocked.nil)))
private theorem no_3_380 : search 3 [0xfafa,0xa0,0xcccc,0xff00] = false :=
  noNode 2 [0xfafa,0xa0,0xcccc,0xff00] [[0xfa5a,0xcccc,0xff00],[0xccec,0xfafa,0xff00],[0xffa0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_133 (AllBlocked.cons no_2_72 (AllBlocked.cons no_2_214 (AllBlocked.nil))))
private theorem no_3_381 : search 3 [0xfafa,0x2020,0xcccc,0xff00] = false :=
  noNode 2 [0xfafa,0x2020,0xcccc,0xff00] [[0xdada,0xcccc,0xff00],[0xecec,0xfafa,0xff00],[0xff20,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_75 (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_202 (AllBlocked.nil))))
private theorem no_3_382 : search 3 [0xfafa,0x4c4c,0xa0a0,0xff00] = false :=
  noNode 2 [0xfafa,0x4c4c,0xa0a0,0xff00] [[0xecec,0xfafa,0xff00],[0x5a5a,0x4c4c,0xff00],[0xffa0,0xfafa,0x4c4c]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_47 (AllBlocked.cons no_2_213 (AllBlocked.nil))))
private theorem no_3_383 : search 3 [0xfafa,0x5f00,0xa0a0,0xcccc] = false :=
  noNode 2 [0xfafa,0x5f00,0xa0a0,0xcccc] [[0xffa0,0xfafa,0xcccc],[0x5a5a,0x5f00,0xcccc],[0xecec,0xfafa,0x5f00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_214 (AllBlocked.cons no_2_48 (AllBlocked.cons no_2_87 (AllBlocked.nil))))
private theorem no_3_384 : search 3 [0xfafa,0xa0a0,0xcccc,0xff00] = false :=
  noNode 2 [0xfafa,0xa0a0,0xcccc,0xff00] [[0x5a5a,0xcccc,0xff00],[0xecec,0xfafa,0xff00],[0xffa0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_49 (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_214 (AllBlocked.nil))))
private theorem no_3_385 : search 3 [0xfafa,0xa8a8,0xcccc,0xff00] = false :=
  noNode 2 [0xfafa,0xa8a8,0xcccc,0xff00] [[0xecec,0xfafa,0xff00],[0xffa8,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_217 (AllBlocked.nil)))
private theorem no_3_386 : search 3 [0xfafa,0xaaa0,0xcccc,0xff00] = false :=
  noNode 2 [0xfafa,0xaaa0,0xcccc,0xff00] [[0xeeec,0xfafa,0xff00],[0xffa0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_106 (AllBlocked.cons no_2_214 (AllBlocked.nil)))
private theorem no_3_387 : search 3 [0xfafa,0xe0e0,0xcccc,0xff00] = false :=
  noNode 2 [0xfafa,0xe0e0,0xcccc,0xff00] [[0xffe0,0xfafa,0xcccc],[0xecec,0xfafa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_254 (AllBlocked.cons no_2_88 (AllBlocked.nil)))
private theorem no_3_388 : search 3 [0xfafa,0xecec,0xa0a0,0xff00] = false :=
  noNode 2 [0xfafa,0xecec,0xa0a0,0xff00] [[0x5a5a,0xecec,0xff00],[0x5f00,0xfafa,0xecec],[0xffa0,0xfafa,0xecec]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_50 (AllBlocked.cons no_2_54 (AllBlocked.cons no_2_215 (AllBlocked.nil))))
private theorem no_3_389 : search 3 [0xfafa,0xecec,0xaaaa,0xff00] = false :=
  noNode 2 [0xfafa,0xecec,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_390 : search 3 [0xfafa,0xecec,0xcccc,0xff00] = false :=
  noNode 2 [0xfafa,0xecec,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_391 : search 3 [0xfafa,0xecec,0xf0f0,0xff00] = false :=
  noNode 2 [0xfafa,0xecec,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_392 : search 3 [0xfafa,0xecec,0xff00] = false :=
  noNode 2 [0xfafa,0xecec,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_393 : search 3 [0xfafa,0xeeee,0xfcfc,0xff00] = false :=
  noNode 2 [0xfafa,0xeeee,0xfcfc,0xff00] [[0xf8f8,0xeeee,0xff00],[0xeaea,0xfcfc,0xff00],[0xecec,0xfafa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_88 (AllBlocked.nil))))
private theorem no_3_394 : search 3 [0xfafa,0xf0a0,0xcccc,0xff00] = false :=
  noNode 2 [0xfafa,0xf0a0,0xcccc,0xff00] [[0xffa0,0xfafa,0xcccc],[0xfcec,0xfafa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_214 (AllBlocked.cons no_2_171 (AllBlocked.nil)))
private theorem no_3_395 : search 3 [0xfafa,0xfcfc,0xeeee,0xff00] = false :=
  noNode 2 [0xfafa,0xfcfc,0xeeee,0xff00] [[0xf8f8,0xeeee,0xff00],[0xeaea,0xfcfc,0xff00],[0xecec,0xfafa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_88 (AllBlocked.nil))))
private theorem no_3_396 : search 3 [0xfafa,0xffa0,0xa0a0,0xcccc] = false :=
  noNode 2 [0xfafa,0xffa0,0xa0a0,0xcccc] [[0x5a5a,0xffa0,0xcccc],[0x4c4c,0xfafa,0xffa0],[0xecec,0xfafa,0xffa0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_51 (AllBlocked.cons no_2_37 (AllBlocked.cons no_2_89 (AllBlocked.nil))))
private theorem no_3_397 : search 3 [0xfafa,0xffa0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfafa,0xffa0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_398 : search 3 [0xfafa,0xffa0,0xcccc] = false :=
  noNode 2 [0xfafa,0xffa0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_399 : search 3 [0xfafa,0xffa0,0xcccc,0xf0f0] = false :=
  noNode 2 [0xfafa,0xffa0,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_400 : search 3 [0xfafa,0xffa0,0xcccc,0xff00] = false :=
  noNode 2 [0xfafa,0xffa0,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_401 : search 3 [0xfafa,0xffaa,0xfff0,0xcccc] = false :=
  noNode 2 [0xfafa,0xffaa,0xfff0,0xcccc] [[0xfaaa,0xfff0,0xcccc],[0xfaf0,0xffaa,0xcccc],[0xffa0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_146 (AllBlocked.cons no_2_214 (AllBlocked.nil))))
private theorem no_3_402 : search 3 [0xfafa,0xfff0,0xffaa,0xcccc] = false :=
  noNode 2 [0xfafa,0xfff0,0xffaa,0xcccc] [[0xfaf0,0xffaa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xffa0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_146 (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_214 (AllBlocked.nil))))
private theorem no_3_403 : search 3 [0xfc00,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xfc00,0xffcc,0xaaaa,0xf0f0] [[0xfeaa,0xffcc,0xf0f0],[0xfcf0,0xffcc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_195 (AllBlocked.cons no_2_177 (AllBlocked.nil)))
private theorem no_3_404 : search 3 [0xfc00,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfc00,0xfff0,0xaaaa,0xcccc] [[0xfeaa,0xfff0,0xcccc],[0xfccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_196 (AllBlocked.cons no_2_169 (AllBlocked.nil)))
private theorem no_3_405 : search 3 [0xfccc,0xf0,0xaaaa,0xff00] = false :=
  noNode 2 [0xfccc,0xf0,0xaaaa,0xff00] [[0xfff0,0xfccc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_265 (AllBlocked.nil))
private theorem no_3_406 : search 3 [0xfccc,0xaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xfccc,0xaaa,0xf0f0,0xff00] [[0xfff0,0xfccc,0xaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_264 (AllBlocked.nil))
private theorem no_3_407 : search 3 [0xfccc,0xf00,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xfccc,0xf00,0xaaaa,0xf0f0] [[0xfff0,0xfccc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_265 (AllBlocked.nil))
private theorem no_3_408 : search 3 [0xfccc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xfccc,0xaaaa,0xf0f0,0xff00] [[0xfff0,0xfccc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_265 (AllBlocked.nil))
private theorem no_3_409 : search 3 [0xfccc,0xf000,0xfff0,0xaaaa] = false :=
  noNode 2 [0xfccc,0xf000,0xfff0,0xaaaa] [[0xff0,0xfccc,0xaaaa],[0xaaa,0xfccc,0xfff0],[0xfaaa,0xfccc,0xfff0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_10 (AllBlocked.cons no_2_1 (AllBlocked.cons no_2_136 (AllBlocked.nil))))
private theorem no_3_410 : search 3 [0xfccc,0xfaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xfccc,0xfaaa,0xf0f0,0xff00] [[0xfff0,0xfccc,0xfaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_266 (AllBlocked.nil))
private theorem no_3_411 : search 3 [0xfccc,0xfff0,0xaaaa] = false :=
  noNode 2 [0xfccc,0xfff0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_412 : search 3 [0xfccc,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfccc,0xfff0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_413 : search 3 [0xfccc,0xfff0,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xfccc,0xfff0,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_414 : search 3 [0xfccc,0xfff0,0xaaaa,0xff00] = false :=
  noNode 2 [0xfccc,0xfff0,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_415 : search 3 [0xfccc,0xfff0,0xf000,0xaaaa] = false :=
  noNode 2 [0xfccc,0xfff0,0xf000,0xaaaa] [[0xff0,0xfccc,0xaaaa],[0xaaa,0xfccc,0xfff0],[0xfaaa,0xfccc,0xfff0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_10 (AllBlocked.cons no_2_1 (AllBlocked.cons no_2_136 (AllBlocked.nil))))
private theorem no_3_416 : search 3 [0xfcec,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xfcec,0xaaaa,0xf0f0,0xff00] [[0xfafa,0xfcec,0xff00],[0xfff0,0xfcec,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_157 (AllBlocked.cons no_2_267 (AllBlocked.nil)))
private theorem no_3_417 : search 3 [0xfcf0,0xcc,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcf0,0xcc,0xaaaa,0xff00] [[0xffcc,0xfcf0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_249 (AllBlocked.nil))
private theorem no_3_418 : search 3 [0xfcf0,0x22aa,0xcccc,0xff00] = false :=
  noNode 2 [0xfcf0,0x22aa,0xcccc,0xff00] [[0xffcc,0xfcf0,0x22aa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_248 (AllBlocked.nil))
private theorem no_3_419 : search 3 [0xfcf0,0x3300,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfcf0,0x3300,0xaaaa,0xcccc] [[0xffcc,0xfcf0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_249 (AllBlocked.nil))
private theorem no_3_420 : search 3 [0xfcf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xfcf0,0xaaaa,0xcccc,0xff00] [[0xffcc,0xfcf0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_249 (AllBlocked.nil))
private theorem no_3_421 : search 3 [0xfcf0,0xcc00,0xffcc,0xaaaa] = false :=
  noNode 2 [0xfcf0,0xcc00,0xffcc,0xaaaa] [[0x33cc,0xfcf0,0xaaaa],[0x22aa,0xfcf0,0xffcc],[0xeeaa,0xfcf0,0xffcc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_24 (AllBlocked.cons no_2_12 (AllBlocked.cons no_2_94 (AllBlocked.nil))))
private theorem no_3_422 : search 3 [0xfcf0,0xeeaa,0xcccc,0xff00] = false :=
  noNode 2 [0xfcf0,0xeeaa,0xcccc,0xff00] [[0xffcc,0xfcf0,0xeeaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_250 (AllBlocked.nil))
private theorem no_3_423 : search 3 [0xfcf0,0xffcc,0xaaaa] = false :=
  noNode 2 [0xfcf0,0xffcc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_424 : search 3 [0xfcf0,0xffcc,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfcf0,0xffcc,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_425 : search 3 [0xfcf0,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xfcf0,0xffcc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_426 : search 3 [0xfcf0,0xffcc,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcf0,0xffcc,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_427 : search 3 [0xfcf0,0xffcc,0xcc00,0xaaaa] = false :=
  noNode 2 [0xfcf0,0xffcc,0xcc00,0xaaaa] [[0x33cc,0xfcf0,0xaaaa],[0x22aa,0xfcf0,0xffcc],[0xeeaa,0xfcf0,0xffcc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_24 (AllBlocked.cons no_2_12 (AllBlocked.cons no_2_94 (AllBlocked.nil))))
private theorem no_3_428 : search 3 [0xfcf8,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xfcf8,0xaaaa,0xcccc,0xff00] [[0xeeee,0xfcf8,0xff00],[0xffcc,0xfcf8,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_115 (AllBlocked.cons no_2_251 (AllBlocked.nil)))
private theorem no_3_429 : search 3 [0xfcfc,0xc0,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcfc,0xc0,0xaaaa,0xff00] [[0xfc3c,0xaaaa,0xff00],[0xaaea,0xfcfc,0xff00],[0xffc0,0xfcfc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_164 (AllBlocked.cons no_2_66 (AllBlocked.cons no_2_236 (AllBlocked.nil))))
private theorem no_3_430 : search 3 [0xfcfc,0x2a2a,0xc0c0,0xff00] = false :=
  noNode 2 [0xfcfc,0x2a2a,0xc0c0,0xff00] [[0xeaea,0xfcfc,0xff00],[0x3c3c,0x2a2a,0xff00],[0xffc0,0xfcfc,0x2a2a]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_25 (AllBlocked.cons no_2_235 (AllBlocked.nil))))
private theorem no_3_431 : search 3 [0xfcfc,0x3f00,0xc0c0,0xaaaa] = false :=
  noNode 2 [0xfcfc,0x3f00,0xc0c0,0xaaaa] [[0xffc0,0xfcfc,0xaaaa],[0x3c3c,0x3f00,0xaaaa],[0xeaea,0xfcfc,0x3f00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_26 (AllBlocked.cons no_2_81 (AllBlocked.nil))))
private theorem no_3_432 : search 3 [0xfcfc,0x4040,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcfc,0x4040,0xaaaa,0xff00] [[0xbcbc,0xaaaa,0xff00],[0xeaea,0xfcfc,0xff00],[0xff40,0xfcfc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_71 (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_203 (AllBlocked.nil))))
private theorem no_3_433 : search 3 [0xfcfc,0xc0c0,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcfc,0xc0c0,0xaaaa,0xff00] [[0x3c3c,0xaaaa,0xff00],[0xffc0,0xfcfc,0xaaaa],[0xeaea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_27 (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_82 (AllBlocked.nil))))
private theorem no_3_434 : search 3 [0xfcfc,0xc8c8,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcfc,0xc8c8,0xaaaa,0xff00] [[0xffc8,0xfcfc,0xaaaa],[0xeaea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_239 (AllBlocked.cons no_2_82 (AllBlocked.nil)))
private theorem no_3_435 : search 3 [0xfcfc,0xccc0,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcfc,0xccc0,0xaaaa,0xff00] [[0xffc0,0xfcfc,0xaaaa],[0xeeea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_104 (AllBlocked.nil)))
private theorem no_3_436 : search 3 [0xfcfc,0xe0e0,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcfc,0xe0e0,0xaaaa,0xff00] [[0xffe0,0xfcfc,0xaaaa],[0xeaea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_255 (AllBlocked.cons no_2_82 (AllBlocked.nil)))
private theorem no_3_437 : search 3 [0xfcfc,0xeaea,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcfc,0xeaea,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_438 : search 3 [0xfcfc,0xeaea,0xc0c0,0xff00] = false :=
  noNode 2 [0xfcfc,0xeaea,0xc0c0,0xff00] [[0x3c3c,0xeaea,0xff00],[0x3f00,0xfcfc,0xeaea],[0xffc0,0xfcfc,0xeaea]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_28 (AllBlocked.cons no_2_32 (AllBlocked.cons no_2_237 (AllBlocked.nil))))
private theorem no_3_439 : search 3 [0xfcfc,0xeaea,0xcccc,0xff00] = false :=
  noNode 2 [0xfcfc,0xeaea,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_440 : search 3 [0xfcfc,0xeaea,0xf0f0,0xff00] = false :=
  noNode 2 [0xfcfc,0xeaea,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_441 : search 3 [0xfcfc,0xeaea,0xff00] = false :=
  noNode 2 [0xfcfc,0xeaea,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_442 : search 3 [0xfcfc,0xeeee,0xfafa,0xff00] = false :=
  noNode 2 [0xfcfc,0xeeee,0xfafa,0xff00] [[0xecec,0xfafa,0xff00],[0xeaea,0xfcfc,0xff00],[0xf8f8,0xeeee,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_82 (AllBlocked.cons no_2_130 (AllBlocked.nil))))
private theorem no_3_443 : search 3 [0xfcfc,0xf0c0,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcfc,0xf0c0,0xaaaa,0xff00] [[0xffc0,0xfcfc,0xaaaa],[0xfaea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_140 (AllBlocked.nil)))
private theorem no_3_444 : search 3 [0xfcfc,0xfafa,0xeeee,0xff00] = false :=
  noNode 2 [0xfcfc,0xfafa,0xeeee,0xff00] [[0xf8f8,0xeeee,0xff00],[0xecec,0xfafa,0xff00],[0xeaea,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_130 (AllBlocked.cons no_2_88 (AllBlocked.cons no_2_82 (AllBlocked.nil))))
private theorem no_3_445 : search 3 [0xfcfc,0xffc0,0xaaaa] = false :=
  noNode 2 [0xfcfc,0xffc0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_446 : search 3 [0xfcfc,0xffc0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfcfc,0xffc0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_447 : search 3 [0xfcfc,0xffc0,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xfcfc,0xffc0,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_448 : search 3 [0xfcfc,0xffc0,0xaaaa,0xff00] = false :=
  noNode 2 [0xfcfc,0xffc0,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_449 : search 3 [0xfcfc,0xffc0,0xc0c0,0xaaaa] = false :=
  noNode 2 [0xfcfc,0xffc0,0xc0c0,0xaaaa] [[0x3c3c,0xffc0,0xaaaa],[0x2a2a,0xfcfc,0xffc0],[0xeaea,0xfcfc,0xffc0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_29 (AllBlocked.cons no_2_15 (AllBlocked.cons no_2_83 (AllBlocked.nil))))
private theorem no_3_450 : search 3 [0xfcfc,0xffcc,0xfff0,0xaaaa] = false :=
  noNode 2 [0xfcfc,0xffcc,0xfff0,0xaaaa] [[0xfccc,0xfff0,0xaaaa],[0xfcf0,0xffcc,0xaaaa],[0xffc0,0xfcfc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_169 (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_236 (AllBlocked.nil))))
private theorem no_3_451 : search 3 [0xfcfc,0xfff0,0xffcc,0xaaaa] = false :=
  noNode 2 [0xfcfc,0xfff0,0xffcc,0xaaaa] [[0xfcf0,0xffcc,0xaaaa],[0xfccc,0xfff0,0xaaaa],[0xffc0,0xfcfc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_169 (AllBlocked.cons no_2_236 (AllBlocked.nil))))
private theorem no_3_452 : search 3 [0xfe00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xfe00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_453 : search 3 [0xfeaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 2 [0xfeaa,0xcccc,0xf0f0,0xff00] [[0xffcc,0xfeaa,0xf0f0],[0xfff0,0xfeaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_252 (AllBlocked.cons no_2_268 (AllBlocked.nil)))
private theorem no_3_454 : search 3 [0xfecc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xfecc,0xaaaa,0xf0f0,0xff00] [[0xffaa,0xfecc,0xf0f0],[0xfff0,0xfecc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_230 (AllBlocked.cons no_2_269 (AllBlocked.nil)))
private theorem no_3_455 : search 3 [0xfef0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xfef0,0xaaaa,0xcccc,0xff00] [[0xffaa,0xfef0,0xcccc],[0xffcc,0xfef0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_231 (AllBlocked.cons no_2_253 (AllBlocked.nil)))
private theorem no_3_456 : search 3 [0xff00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xff00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_457 : search 3 [0xff08,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xff08,0xaaaa,0xcccc,0xf0f0] [[0xeeee,0xff08,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_116 (AllBlocked.nil))
private theorem no_3_458 : search 3 [0xff20,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xff20,0xaaaa,0xcccc,0xf0f0] [[0xfafa,0xff20,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_158 (AllBlocked.nil))
private theorem no_3_459 : search 3 [0xff40,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xff40,0xaaaa,0xcccc,0xf0f0] [[0xfcfc,0xff40,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_189 (AllBlocked.nil))
private theorem no_3_460 : search 3 [0xff80,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xff80,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_461 : search 3 [0xff88,0x2222,0xcccc,0xf0f0] = false :=
  noNode 2 [0xff88,0x2222,0xcccc,0xf0f0] [[0xeeee,0xff88,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_118 (AllBlocked.nil))
private theorem no_3_462 : search 3 [0xff88,0x4444,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xff88,0x4444,0xaaaa,0xf0f0] [[0xeeee,0xff88,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_118 (AllBlocked.nil))
private theorem no_3_463 : search 3 [0xff88,0x7070,0xaaaa,0xcccc] = false :=
  noNode 2 [0xff88,0x7070,0xaaaa,0xcccc] [[0xeeee,0xff88,0x7070]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_117 (AllBlocked.nil))
private theorem no_3_464 : search 3 [0xff88,0x8888,0xeeee,0xf0f0] = false :=
  noNode 2 [0xff88,0x8888,0xeeee,0xf0f0] [[0x6666,0xff88,0xf0f0],[0x7070,0xff88,0xeeee],[0xf8f8,0xff88,0xeeee]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_59 (AllBlocked.cons no_2_62 (AllBlocked.cons no_2_132 (AllBlocked.nil))))
private theorem no_3_465 : search 3 [0xff88,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xff88,0xaaaa,0xcccc,0xf0f0] [[0xeeee,0xff88,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_118 (AllBlocked.nil))
private theorem no_3_466 : search 3 [0xff88,0xeeee,0x8888,0xf0f0] = false :=
  noNode 2 [0xff88,0xeeee,0x8888,0xf0f0] [[0x6666,0xff88,0xf0f0],[0x7070,0xff88,0xeeee],[0xf8f8,0xff88,0xeeee]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_59 (AllBlocked.cons no_2_62 (AllBlocked.cons no_2_132 (AllBlocked.nil))))
private theorem no_3_467 : search 3 [0xff88,0xeeee,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xff88,0xeeee,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_468 : search 3 [0xff88,0xeeee,0xcccc,0xf0f0] = false :=
  noNode 2 [0xff88,0xeeee,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_469 : search 3 [0xff88,0xeeee,0xf0f0] = false :=
  noNode 2 [0xff88,0xeeee,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_470 : search 3 [0xff88,0xeeee,0xf0f0,0xff00] = false :=
  noNode 2 [0xff88,0xeeee,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_471 : search 3 [0xff88,0xf8f8,0xaaaa,0xcccc] = false :=
  noNode 2 [0xff88,0xf8f8,0xaaaa,0xcccc] [[0xeeee,0xff88,0xf8f8]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_119 (AllBlocked.nil))
private theorem no_3_472 : search 3 [0xffa0,0xa0a,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffa0,0xa0a,0xcccc,0xf0f0] [[0xfafa,0xffa0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_160 (AllBlocked.nil))
private theorem no_3_473 : search 3 [0xffa0,0x4c4c,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffa0,0x4c4c,0xaaaa,0xf0f0] [[0xfafa,0xffa0,0x4c4c]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_159 (AllBlocked.nil))
private theorem no_3_474 : search 3 [0xffa0,0x5050,0xaaaa,0xcccc] = false :=
  noNode 2 [0xffa0,0x5050,0xaaaa,0xcccc] [[0xfafa,0xffa0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_160 (AllBlocked.nil))
private theorem no_3_475 : search 3 [0xffa0,0xa0a0,0xfafa,0xcccc] = false :=
  noNode 2 [0xffa0,0xa0a0,0xfafa,0xcccc] [[0x5a5a,0xffa0,0xcccc],[0x4c4c,0xffa0,0xfafa],[0xecec,0xffa0,0xfafa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_51 (AllBlocked.cons no_2_38 (AllBlocked.cons no_2_90 (AllBlocked.nil))))
private theorem no_3_476 : search 3 [0xffa0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffa0,0xaaaa,0xcccc,0xf0f0] [[0xfafa,0xffa0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_160 (AllBlocked.nil))
private theorem no_3_477 : search 3 [0xffa0,0xecec,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffa0,0xecec,0xaaaa,0xf0f0] [[0xfafa,0xffa0,0xecec]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_161 (AllBlocked.nil))
private theorem no_3_478 : search 3 [0xffa0,0xfafa,0xa0a0,0xcccc] = false :=
  noNode 2 [0xffa0,0xfafa,0xa0a0,0xcccc] [[0x5a5a,0xffa0,0xcccc],[0x4c4c,0xffa0,0xfafa],[0xecec,0xffa0,0xfafa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_51 (AllBlocked.cons no_2_38 (AllBlocked.cons no_2_90 (AllBlocked.nil))))
private theorem no_3_479 : search 3 [0xffa0,0xfafa,0xaaaa,0xcccc] = false :=
  noNode 2 [0xffa0,0xfafa,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_480 : search 3 [0xffa0,0xfafa,0xcccc] = false :=
  noNode 2 [0xffa0,0xfafa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_481 : search 3 [0xffa0,0xfafa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffa0,0xfafa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_482 : search 3 [0xffa0,0xfafa,0xcccc,0xff00] = false :=
  noNode 2 [0xffa0,0xfafa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_483 : search 3 [0xffa8,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffa8,0xaaaa,0xcccc,0xf0f0] [[0xeeee,0xffa8,0xf0f0],[0xfafa,0xffa8,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_120 (AllBlocked.cons no_2_162 (AllBlocked.nil)))
private theorem no_3_484 : search 3 [0xffaa,0xa00,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xa00,0xcccc,0xf0f0] [[0xf5aa,0xcccc,0xf0f0],[0xcecc,0xffaa,0xf0f0],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_126 (AllBlocked.cons no_2_73 (AllBlocked.cons no_2_146 (AllBlocked.nil))))
private theorem no_3_485 : search 3 [0xffaa,0x2200,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffaa,0x2200,0xcccc,0xf0f0] [[0xddaa,0xcccc,0xf0f0],[0xeecc,0xffaa,0xf0f0],[0xf2f0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_77 (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_123 (AllBlocked.nil))))
private theorem no_3_486 : search 3 [0xffaa,0x44cc,0xaa00,0xf0f0] = false :=
  noNode 2 [0xffaa,0x44cc,0xaa00,0xf0f0] [[0xeecc,0xffaa,0xf0f0],[0x55aa,0x44cc,0xf0f0],[0xfaf0,0xffaa,0x44cc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_42 (AllBlocked.cons no_2_145 (AllBlocked.nil))))
private theorem no_3_487 : search 3 [0xffaa,0x50f0,0xaa00,0xcccc] = false :=
  noNode 2 [0xffaa,0x50f0,0xaa00,0xcccc] [[0xfaf0,0xffaa,0xcccc],[0x55aa,0x50f0,0xcccc],[0xeecc,0xffaa,0x50f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_146 (AllBlocked.cons no_2_43 (AllBlocked.cons no_2_101 (AllBlocked.nil))))
private theorem no_3_488 : search 3 [0xffaa,0xaa00,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xaa00,0xcccc,0xf0f0] [[0x55aa,0xcccc,0xf0f0],[0xeecc,0xffaa,0xf0f0],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_44 (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_146 (AllBlocked.nil))))
private theorem no_3_489 : search 3 [0xffaa,0xaa88,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xaa88,0xcccc,0xf0f0] [[0xeecc,0xffaa,0xf0f0],[0xfaf8,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_149 (AllBlocked.nil)))
private theorem no_3_490 : search 3 [0xffaa,0xaaa0,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xaaa0,0xcccc,0xf0f0] [[0xeeec,0xffaa,0xf0f0],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_107 (AllBlocked.cons no_2_146 (AllBlocked.nil)))
private theorem no_3_491 : search 3 [0xffaa,0xee00,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xee00,0xcccc,0xf0f0] [[0xfef0,0xffaa,0xcccc],[0xeecc,0xffaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_199 (AllBlocked.cons no_2_102 (AllBlocked.nil)))
private theorem no_3_492 : search 3 [0xffaa,0xeecc,0xaa00,0xf0f0] = false :=
  noNode 2 [0xffaa,0xeecc,0xaa00,0xf0f0] [[0x55aa,0xeecc,0xf0f0],[0x50f0,0xffaa,0xeecc],[0xfaf0,0xffaa,0xeecc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_45 (AllBlocked.cons no_2_41 (AllBlocked.cons no_2_147 (AllBlocked.nil))))
private theorem no_3_493 : search 3 [0xffaa,0xeecc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffaa,0xeecc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_494 : search 3 [0xffaa,0xeecc,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xeecc,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_495 : search 3 [0xffaa,0xeecc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xeecc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_496 : search 3 [0xffaa,0xeecc,0xf0f0,0xff00] = false :=
  noNode 2 [0xffaa,0xeecc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_497 : search 3 [0xffaa,0xeeee,0xffcc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xeeee,0xffcc,0xf0f0] [[0xff88,0xeeee,0xf0f0],[0xeeaa,0xffcc,0xf0f0],[0xeecc,0xffaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_207 (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_102 (AllBlocked.nil))))
private theorem no_3_498 : search 3 [0xffaa,0xfa00,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xfa00,0xcccc,0xf0f0] [[0xfecc,0xffaa,0xf0f0],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_197 (AllBlocked.cons no_2_146 (AllBlocked.nil)))
private theorem no_3_499 : search 3 [0xffaa,0xfaf0,0xaa00,0xcccc] = false :=
  noNode 2 [0xffaa,0xfaf0,0xaa00,0xcccc] [[0x55aa,0xfaf0,0xcccc],[0x44cc,0xffaa,0xfaf0],[0xeecc,0xffaa,0xfaf0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_46 (AllBlocked.cons no_2_35 (AllBlocked.cons no_2_103 (AllBlocked.nil))))
private theorem no_3_500 : search 3 [0xffaa,0xfaf0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xffaa,0xfaf0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_501 : search 3 [0xffaa,0xfaf0,0xcccc] = false :=
  noNode 2 [0xffaa,0xfaf0,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_502 : search 3 [0xffaa,0xfaf0,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffaa,0xfaf0,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_503 : search 3 [0xffaa,0xfaf0,0xcccc,0xff00] = false :=
  noNode 2 [0xffaa,0xfaf0,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_504 : search 3 [0xffaa,0xfafa,0xfff0,0xcccc] = false :=
  noNode 2 [0xffaa,0xfafa,0xfff0,0xcccc] [[0xffa0,0xfafa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_214 (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_146 (AllBlocked.nil))))
private theorem no_3_505 : search 3 [0xffaa,0xffcc,0xeeee,0xf0f0] = false :=
  noNode 2 [0xffaa,0xffcc,0xeeee,0xf0f0] [[0xff88,0xeeee,0xf0f0],[0xeeaa,0xffcc,0xf0f0],[0xeecc,0xffaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_207 (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_102 (AllBlocked.nil))))
private theorem no_3_506 : search 3 [0xffaa,0xfff0,0xfafa,0xcccc] = false :=
  noNode 2 [0xffaa,0xfff0,0xfafa,0xcccc] [[0xffa0,0xfafa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xfaf0,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_214 (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_146 (AllBlocked.nil))))
private theorem no_3_507 : search 3 [0xffc0,0xc0c,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffc0,0xc0c,0xaaaa,0xf0f0] [[0xfcfc,0xffc0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_191 (AllBlocked.nil))
private theorem no_3_508 : search 3 [0xffc0,0x2a2a,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffc0,0x2a2a,0xcccc,0xf0f0] [[0xfcfc,0xffc0,0x2a2a]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_190 (AllBlocked.nil))
private theorem no_3_509 : search 3 [0xffc0,0x3030,0xaaaa,0xcccc] = false :=
  noNode 2 [0xffc0,0x3030,0xaaaa,0xcccc] [[0xfcfc,0xffc0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_191 (AllBlocked.nil))
private theorem no_3_510 : search 3 [0xffc0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffc0,0xaaaa,0xcccc,0xf0f0] [[0xfcfc,0xffc0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_191 (AllBlocked.nil))
private theorem no_3_511 : search 3 [0xffc0,0xc0c0,0xfcfc,0xaaaa] = false :=
  noNode 2 [0xffc0,0xc0c0,0xfcfc,0xaaaa] [[0x3c3c,0xffc0,0xaaaa],[0x2a2a,0xffc0,0xfcfc],[0xeaea,0xffc0,0xfcfc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_29 (AllBlocked.cons no_2_16 (AllBlocked.cons no_2_84 (AllBlocked.nil))))
private theorem no_3_512 : search 3 [0xffc0,0xeaea,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffc0,0xeaea,0xcccc,0xf0f0] [[0xfcfc,0xffc0,0xeaea]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_192 (AllBlocked.nil))
private theorem no_3_513 : search 3 [0xffc0,0xfcfc,0xaaaa] = false :=
  noNode 2 [0xffc0,0xfcfc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_514 : search 3 [0xffc0,0xfcfc,0xaaaa,0xcccc] = false :=
  noNode 2 [0xffc0,0xfcfc,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_515 : search 3 [0xffc0,0xfcfc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffc0,0xfcfc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_516 : search 3 [0xffc0,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 2 [0xffc0,0xfcfc,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_517 : search 3 [0xffc0,0xfcfc,0xc0c0,0xaaaa] = false :=
  noNode 2 [0xffc0,0xfcfc,0xc0c0,0xaaaa] [[0x3c3c,0xffc0,0xaaaa],[0x2a2a,0xffc0,0xfcfc],[0xeaea,0xffc0,0xfcfc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_29 (AllBlocked.cons no_2_16 (AllBlocked.cons no_2_84 (AllBlocked.nil))))
private theorem no_3_518 : search 3 [0xffc8,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffc8,0xaaaa,0xcccc,0xf0f0] [[0xeeee,0xffc8,0xf0f0],[0xfcfc,0xffc8,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_121 (AllBlocked.cons no_2_193 (AllBlocked.nil)))
private theorem no_3_519 : search 3 [0xffcc,0xc00,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xc00,0xaaaa,0xf0f0] [[0xf3cc,0xaaaa,0xf0f0],[0xaeaa,0xffcc,0xf0f0],[0xfcf0,0xffcc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_124 (AllBlocked.cons no_2_67 (AllBlocked.cons no_2_177 (AllBlocked.nil))))
private theorem no_3_520 : search 3 [0xffcc,0x22aa,0xcc00,0xf0f0] = false :=
  noNode 2 [0xffcc,0x22aa,0xcc00,0xf0f0] [[0xeeaa,0xffcc,0xf0f0],[0x33cc,0x22aa,0xf0f0],[0xfcf0,0xffcc,0x22aa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_20 (AllBlocked.cons no_2_176 (AllBlocked.nil))))
private theorem no_3_521 : search 3 [0xffcc,0x30f0,0xcc00,0xaaaa] = false :=
  noNode 2 [0xffcc,0x30f0,0xcc00,0xaaaa] [[0xfcf0,0xffcc,0xaaaa],[0x33cc,0x30f0,0xaaaa],[0xeeaa,0xffcc,0x30f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_21 (AllBlocked.cons no_2_95 (AllBlocked.nil))))
private theorem no_3_522 : search 3 [0xffcc,0x4400,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0x4400,0xaaaa,0xf0f0] [[0xbbcc,0xaaaa,0xf0f0],[0xeeaa,0xffcc,0xf0f0],[0xf4f0,0xffcc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_70 (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_125 (AllBlocked.nil))))
private theorem no_3_523 : search 3 [0xffcc,0xcc00,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xcc00,0xaaaa,0xf0f0] [[0x33cc,0xaaaa,0xf0f0],[0xfcf0,0xffcc,0xaaaa],[0xeeaa,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_22 (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_96 (AllBlocked.nil))))
private theorem no_3_524 : search 3 [0xffcc,0xcc88,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xcc88,0xaaaa,0xf0f0] [[0xfcf8,0xffcc,0xaaaa],[0xeeaa,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_180 (AllBlocked.cons no_2_96 (AllBlocked.nil)))
private theorem no_3_525 : search 3 [0xffcc,0xccc0,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xccc0,0xaaaa,0xf0f0] [[0xfcf0,0xffcc,0xaaaa],[0xeeea,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_105 (AllBlocked.nil)))
private theorem no_3_526 : search 3 [0xffcc,0xee00,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xee00,0xaaaa,0xf0f0] [[0xfef0,0xffcc,0xaaaa],[0xeeaa,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_200 (AllBlocked.cons no_2_96 (AllBlocked.nil)))
private theorem no_3_527 : search 3 [0xffcc,0xeeaa,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xeeaa,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_528 : search 3 [0xffcc,0xeeaa,0xcc00,0xf0f0] = false :=
  noNode 2 [0xffcc,0xeeaa,0xcc00,0xf0f0] [[0x33cc,0xeeaa,0xf0f0],[0x30f0,0xffcc,0xeeaa],[0xfcf0,0xffcc,0xeeaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_23 (AllBlocked.cons no_2_19 (AllBlocked.cons no_2_178 (AllBlocked.nil))))
private theorem no_3_529 : search 3 [0xffcc,0xeeaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffcc,0xeeaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_530 : search 3 [0xffcc,0xeeaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xeeaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_531 : search 3 [0xffcc,0xeeaa,0xf0f0,0xff00] = false :=
  noNode 2 [0xffcc,0xeeaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_532 : search 3 [0xffcc,0xeeee,0xffaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xeeee,0xffaa,0xf0f0] [[0xeecc,0xffaa,0xf0f0],[0xeeaa,0xffcc,0xf0f0],[0xff88,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_96 (AllBlocked.cons no_2_207 (AllBlocked.nil))))
private theorem no_3_533 : search 3 [0xffcc,0xfc00,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xfc00,0xaaaa,0xf0f0] [[0xfeaa,0xffcc,0xf0f0],[0xfcf0,0xffcc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_195 (AllBlocked.cons no_2_177 (AllBlocked.nil)))
private theorem no_3_534 : search 3 [0xffcc,0xfcf0,0xaaaa] = false :=
  noNode 2 [0xffcc,0xfcf0,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_535 : search 3 [0xffcc,0xfcf0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xffcc,0xfcf0,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_536 : search 3 [0xffcc,0xfcf0,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xffcc,0xfcf0,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_537 : search 3 [0xffcc,0xfcf0,0xaaaa,0xff00] = false :=
  noNode 2 [0xffcc,0xfcf0,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_538 : search 3 [0xffcc,0xfcf0,0xcc00,0xaaaa] = false :=
  noNode 2 [0xffcc,0xfcf0,0xcc00,0xaaaa] [[0x33cc,0xfcf0,0xaaaa],[0x22aa,0xffcc,0xfcf0],[0xeeaa,0xffcc,0xfcf0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_24 (AllBlocked.cons no_2_13 (AllBlocked.cons no_2_97 (AllBlocked.nil))))
private theorem no_3_539 : search 3 [0xffcc,0xfcfc,0xfff0,0xaaaa] = false :=
  noNode 2 [0xffcc,0xfcfc,0xfff0,0xaaaa] [[0xffc0,0xfcfc,0xaaaa],[0xfccc,0xfff0,0xaaaa],[0xfcf0,0xffcc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_169 (AllBlocked.cons no_2_177 (AllBlocked.nil))))
private theorem no_3_540 : search 3 [0xffcc,0xffaa,0xeeee,0xf0f0] = false :=
  noNode 2 [0xffcc,0xffaa,0xeeee,0xf0f0] [[0xff88,0xeeee,0xf0f0],[0xeecc,0xffaa,0xf0f0],[0xeeaa,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_207 (AllBlocked.cons no_2_102 (AllBlocked.cons no_2_96 (AllBlocked.nil))))
private theorem no_3_541 : search 3 [0xffcc,0xfff0,0xfcfc,0xaaaa] = false :=
  noNode 2 [0xffcc,0xfff0,0xfcfc,0xaaaa] [[0xffc0,0xfcfc,0xaaaa],[0xfccc,0xfff0,0xaaaa],[0xfcf0,0xffcc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_169 (AllBlocked.cons no_2_177 (AllBlocked.nil))))
private theorem no_3_542 : search 3 [0xffe0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xffe0,0xaaaa,0xcccc,0xf0f0] [[0xfafa,0xffe0,0xcccc],[0xfcfc,0xffe0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_163 (AllBlocked.cons no_2_194 (AllBlocked.nil)))
private theorem no_3_543 : search 3 [0xfff0,0xaaa,0xf000,0xcccc] = false :=
  noNode 2 [0xfff0,0xaaa,0xf000,0xcccc] [[0xfaaa,0xfff0,0xcccc],[0xff0,0xaaa,0xcccc],[0xfccc,0xfff0,0xaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_6 (AllBlocked.cons no_2_168 (AllBlocked.nil))))
private theorem no_3_544 : search 3 [0xfff0,0xccc,0xf000,0xaaaa] = false :=
  noNode 2 [0xfff0,0xccc,0xf000,0xaaaa] [[0xfccc,0xfff0,0xaaaa],[0xff0,0xccc,0xaaaa],[0xfaaa,0xfff0,0xccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_169 (AllBlocked.cons no_2_7 (AllBlocked.cons no_2_137 (AllBlocked.nil))))
private theorem no_3_545 : search 3 [0xfff0,0x3000,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0x3000,0xaaaa,0xcccc] [[0xcff0,0xaaaa,0xcccc],[0xbaaa,0xfff0,0xcccc],[0xfccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_74 (AllBlocked.cons no_2_69 (AllBlocked.cons no_2_169 (AllBlocked.nil))))
private theorem no_3_546 : search 3 [0xfff0,0x5000,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0x5000,0xaaaa,0xcccc] [[0xaff0,0xaaaa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xdccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_68 (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_76 (AllBlocked.nil))))
private theorem no_3_547 : search 3 [0xfff0,0xf000,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0xf000,0xaaaa,0xcccc] [[0xff0,0xaaaa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xfccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_8 (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_169 (AllBlocked.nil))))
private theorem no_3_548 : search 3 [0xfff0,0xf0a0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0xf0a0,0xaaaa,0xcccc] [[0xfaaa,0xfff0,0xcccc],[0xfcec,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_172 (AllBlocked.nil)))
private theorem no_3_549 : search 3 [0xfff0,0xf0c0,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0xf0c0,0xaaaa,0xcccc] [[0xfaea,0xfff0,0xcccc],[0xfccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_141 (AllBlocked.cons no_2_169 (AllBlocked.nil)))
private theorem no_3_550 : search 3 [0xfff0,0xfa00,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0xfa00,0xaaaa,0xcccc] [[0xfaaa,0xfff0,0xcccc],[0xfecc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_198 (AllBlocked.nil)))
private theorem no_3_551 : search 3 [0xfff0,0xfaaa,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0xfaaa,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_552 : search 3 [0xfff0,0xfaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0xfaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_553 : search 3 [0xfff0,0xfaaa,0xcccc,0xf0f0] = false :=
  noNode 2 [0xfff0,0xfaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_554 : search 3 [0xfff0,0xfaaa,0xcccc,0xff00] = false :=
  noNode 2 [0xfff0,0xfaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_555 : search 3 [0xfff0,0xfaaa,0xf000,0xcccc] = false :=
  noNode 2 [0xfff0,0xfaaa,0xf000,0xcccc] [[0xff0,0xfaaa,0xcccc],[0xccc,0xfff0,0xfaaa],[0xfccc,0xfff0,0xfaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_9 (AllBlocked.cons no_2_5 (AllBlocked.cons no_2_170 (AllBlocked.nil))))
private theorem no_3_556 : search 3 [0xfff0,0xfafa,0xffaa,0xcccc] = false :=
  noNode 2 [0xfff0,0xfafa,0xffaa,0xcccc] [[0xfaf0,0xffaa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xffa0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_146 (AllBlocked.cons no_2_138 (AllBlocked.cons no_2_214 (AllBlocked.nil))))
private theorem no_3_557 : search 3 [0xfff0,0xfc00,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0xfc00,0xaaaa,0xcccc] [[0xfeaa,0xfff0,0xcccc],[0xfccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_196 (AllBlocked.cons no_2_169 (AllBlocked.nil)))
private theorem no_3_558 : search 3 [0xfff0,0xfccc,0xaaaa] = false :=
  noNode 2 [0xfff0,0xfccc,0xaaaa] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_559 : search 3 [0xfff0,0xfccc,0xaaaa,0xcccc] = false :=
  noNode 2 [0xfff0,0xfccc,0xaaaa,0xcccc] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_560 : search 3 [0xfff0,0xfccc,0xaaaa,0xf0f0] = false :=
  noNode 2 [0xfff0,0xfccc,0xaaaa,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_561 : search 3 [0xfff0,0xfccc,0xaaaa,0xff00] = false :=
  noNode 2 [0xfff0,0xfccc,0xaaaa,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_3_562 : search 3 [0xfff0,0xfccc,0xf000,0xaaaa] = false :=
  noNode 2 [0xfff0,0xfccc,0xf000,0xaaaa] [[0xff0,0xfccc,0xaaaa],[0xaaa,0xfff0,0xfccc],[0xfaaa,0xfff0,0xfccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_10 (AllBlocked.cons no_2_2 (AllBlocked.cons no_2_139 (AllBlocked.nil))))
private theorem no_3_563 : search 3 [0xfff0,0xfcfc,0xffcc,0xaaaa] = false :=
  noNode 2 [0xfff0,0xfcfc,0xffcc,0xaaaa] [[0xfcf0,0xffcc,0xaaaa],[0xfccc,0xfff0,0xaaaa],[0xffc0,0xfcfc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_169 (AllBlocked.cons no_2_236 (AllBlocked.nil))))
private theorem no_3_564 : search 3 [0xfff0,0xffaa,0xfafa,0xcccc] = false :=
  noNode 2 [0xfff0,0xffaa,0xfafa,0xcccc] [[0xffa0,0xfafa,0xcccc],[0xfaf0,0xffaa,0xcccc],[0xfaaa,0xfff0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_214 (AllBlocked.cons no_2_146 (AllBlocked.cons no_2_138 (AllBlocked.nil))))
private theorem no_3_565 : search 3 [0xfff0,0xffcc,0xfcfc,0xaaaa] = false :=
  noNode 2 [0xfff0,0xffcc,0xfcfc,0xaaaa] [[0xffc0,0xfcfc,0xaaaa],[0xfcf0,0xffcc,0xaaaa],[0xfccc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_2_236 (AllBlocked.cons no_2_177 (AllBlocked.cons no_2_169 (AllBlocked.nil))))
private theorem no_4_0 : search 4 [0xa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_1 : search 4 [0xc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_2 : search 4 [0x22,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x22,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_3 : search 4 [0x30,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x30,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_4 : search 4 [0x44,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x44,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_5 : search 4 [0x50,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x50,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_6 : search 4 [0x88,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x88,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xf070,0xaaaa,0xcccc,0xff00],[0xf0f8,0xaaaa,0xcccc,0xff00],[0xff88,0xaaaa,0xcccc,0xf0f0],[0xeeee,0x88,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_329 (AllBlocked.cons no_3_336 (AllBlocked.cons no_3_465 (AllBlocked.cons no_3_303 (AllBlocked.nil)))))
private theorem no_4_7 : search 4 [0xa0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xcc4c,0xaaaa,0xf0f0,0xff00],[0xccec,0xaaaa,0xf0f0,0xff00],[0xffa0,0xaaaa,0xcccc,0xf0f0],[0xfafa,0xa0,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_236 (AllBlocked.cons no_3_243 (AllBlocked.cons no_3_476 (AllBlocked.cons no_3_380 (AllBlocked.nil)))))
private theorem no_4_8 : search 4 [0xaa,0xa0a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa,0xa0a,0xcccc,0xf0f0,0xff00] [[0xaaa,0xcccc,0xf0f0,0xff00],[0xf050,0xa0a,0xcccc,0xff00],[0xf500,0xaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_30 (AllBlocked.cons no_3_328 (AllBlocked.cons no_3_340 (AllBlocked.nil))))
private theorem no_4_9 : search 4 [0xaa,0x2222,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa,0x2222,0xcccc,0xf0f0,0xff00] [[0x22aa,0xcccc,0xf0f0,0xff00],[0xcc44,0x2222,0xf0f0,0xff00],[0xdd00,0xaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_71 (AllBlocked.cons no_3_235 (AllBlocked.cons no_3_249 (AllBlocked.nil))))
private theorem no_4_10 : search 4 [0xaa,0x5500,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xaa,0x5500,0xaaaa,0xcccc,0xf0f0] [[0x55aa,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_158 (AllBlocked.nil))
private theorem no_4_11 : search 4 [0xaa,0x5500,0xcccc,0xf0f0] = false :=
  noNode 3 [0xaa,0x5500,0xcccc,0xf0f0] [[0x55aa,0xcccc,0xf0f0],[0x55aa,0x5500,0xcccc,0xf0f0],[0x55aa,0xaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_159 (AllBlocked.cons no_3_156 (AllBlocked.cons no_3_155 (AllBlocked.nil))))
private theorem no_4_12 : search 4 [0xaa,0x5500,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa,0x5500,0xcccc,0xf0f0,0xff00] [[0x55aa,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_160 (AllBlocked.nil))
private theorem no_4_13 : search 4 [0xaa,0xaa00,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa,0xaa00,0xcccc,0xf0f0,0xff00] [[0xaaaa,0xcccc,0xf0f0,0xff00],[0xffaa,0xaa00,0xcccc,0xf0f0],[0xeecc,0xaa,0xf0f0,0xff00],[0xfaf0,0xaa,0xcccc,0xff00],[0x5500,0xaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_488 (AllBlocked.cons no_3_290 (AllBlocked.cons no_3_368 (AllBlocked.cons no_3_149 (AllBlocked.nil))))))
private theorem no_4_14 : search 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x5500,0xaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_149 (AllBlocked.nil))
private theorem no_4_15 : search 4 [0xaa,0xeeee,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa,0xeeee,0xcccc,0xf0f0,0xff00] [[0x88,0xeeee,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_0 (AllBlocked.nil))
private theorem no_4_16 : search 4 [0xaa,0xfafa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa,0xfafa,0xcccc,0xf0f0,0xff00] [[0xa0,0xfafa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_1 (AllBlocked.nil))
private theorem no_4_17 : search 4 [0xaa,0xffaa,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xaa,0xffaa,0xaaaa,0xcccc,0xf0f0] [[0xff00,0xaaaa,0xcccc,0xf0f0],[0xaa00,0xffaa,0xcccc,0xf0f0],[0x5500,0xaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_208 (AllBlocked.cons no_3_149 (AllBlocked.nil))))
private theorem no_4_18 : search 4 [0xc0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaa2a,0xcccc,0xf0f0,0xff00],[0xaaea,0xcccc,0xf0f0,0xff00],[0xffc0,0xaaaa,0xcccc,0xf0f0],[0xfcfc,0xc0,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_211 (AllBlocked.cons no_3_218 (AllBlocked.cons no_3_510 (AllBlocked.cons no_3_429 (AllBlocked.nil)))))
private theorem no_4_19 : search 4 [0xcc,0xc0c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc,0xc0c,0xaaaa,0xf0f0,0xff00] [[0xccc,0xaaaa,0xf0f0,0xff00],[0xf030,0xc0c,0xaaaa,0xff00],[0xf300,0xcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_42 (AllBlocked.cons no_3_327 (AllBlocked.cons no_3_338 (AllBlocked.nil))))
private theorem no_4_20 : search 4 [0xcc,0x3300,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xcc,0x3300,0xaaaa,0xcccc,0xf0f0] [[0x33cc,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_100 (AllBlocked.nil))
private theorem no_4_21 : search 4 [0xcc,0x3300,0xaaaa,0xf0f0] = false :=
  noNode 3 [0xcc,0x3300,0xaaaa,0xf0f0] [[0x33cc,0xaaaa,0xf0f0],[0x33cc,0x3300,0xaaaa,0xf0f0],[0x33cc,0xcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_101 (AllBlocked.cons no_3_99 (AllBlocked.cons no_3_98 (AllBlocked.nil))))
private theorem no_4_22 : search 4 [0xcc,0x3300,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc,0x3300,0xaaaa,0xf0f0,0xff00] [[0x33cc,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_102 (AllBlocked.nil))
private theorem no_4_23 : search 4 [0xcc,0x4444,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc,0x4444,0xaaaa,0xf0f0,0xff00] [[0x44cc,0xaaaa,0xf0f0,0xff00],[0xaa22,0x4444,0xf0f0,0xff00],[0xbb00,0xcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_128 (AllBlocked.cons no_3_210 (AllBlocked.cons no_3_224 (AllBlocked.nil))))
private theorem no_4_24 : search 4 [0xcc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x3300,0xcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_92 (AllBlocked.nil))
private theorem no_4_25 : search 4 [0xcc,0xcc00,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc,0xcc00,0xaaaa,0xf0f0,0xff00] [[0xcccc,0xaaaa,0xf0f0,0xff00],[0xffcc,0xcc00,0xaaaa,0xf0f0],[0xfcf0,0xcc,0xaaaa,0xff00],[0x3300,0xcc,0xaaaa,0xf0f0],[0xeeaa,0xcc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_523 (AllBlocked.cons no_3_417 (AllBlocked.cons no_3_92 (AllBlocked.cons no_3_279 (AllBlocked.nil))))))
private theorem no_4_26 : search 4 [0xcc,0xeeee,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc,0xeeee,0xaaaa,0xf0f0,0xff00] [[0x88,0xeeee,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_0 (AllBlocked.nil))
private theorem no_4_27 : search 4 [0xcc,0xfcfc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc,0xfcfc,0xaaaa,0xf0f0,0xff00] [[0xc0,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_7 (AllBlocked.nil))
private theorem no_4_28 : search 4 [0xcc,0xffcc,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xcc,0xffcc,0xaaaa,0xcccc,0xf0f0] [[0xff00,0xaaaa,0xcccc,0xf0f0],[0xcc00,0xffcc,0xaaaa,0xf0f0],[0x3300,0xcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_233 (AllBlocked.cons no_3_92 (AllBlocked.nil))))
private theorem no_4_29 : search 4 [0xee,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xee,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_30 : search 4 [0xf0,0xf00,0xaaaa,0xcccc] = false :=
  noNode 3 [0xf0,0xf00,0xaaaa,0xcccc] [[0xff0,0xaaaa,0xcccc],[0xff0,0xf00,0xaaaa,0xcccc],[0xff0,0xf0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_54 (AllBlocked.cons no_3_53 (AllBlocked.cons no_3_52 (AllBlocked.nil))))
private theorem no_4_31 : search 4 [0xf0,0xf00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf0,0xf00,0xaaaa,0xcccc,0xf0f0] [[0xff0,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_55 (AllBlocked.nil))
private theorem no_4_32 : search 4 [0xf0,0xf00,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf0,0xf00,0xaaaa,0xcccc,0xff00] [[0xff0,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_56 (AllBlocked.nil))
private theorem no_4_33 : search 4 [0xf0,0x3030,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf0,0x3030,0xaaaa,0xcccc,0xff00] [[0x30f0,0xaaaa,0xcccc,0xff00],[0xcc0c,0x3030,0xaaaa,0xff00],[0xcf00,0xf0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_88 (AllBlocked.cons no_3_234 (AllBlocked.cons no_3_245 (AllBlocked.nil))))
private theorem no_4_34 : search 4 [0xf0,0x5050,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf0,0x5050,0xaaaa,0xcccc,0xff00] [[0x50f0,0xaaaa,0xcccc,0xff00],[0xaa0a,0x5050,0xcccc,0xff00],[0xaf00,0xf0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_146 (AllBlocked.cons no_3_209 (AllBlocked.cons no_3_220 (AllBlocked.nil))))
private theorem no_4_35 : search 4 [0xf0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xf00,0xf0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_46 (AllBlocked.nil))
private theorem no_4_36 : search 4 [0xf0,0xf000,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf0,0xf000,0xaaaa,0xcccc,0xff00] [[0xf0f0,0xaaaa,0xcccc,0xff00],[0xfff0,0xf000,0xaaaa,0xcccc],[0xf00,0xf0,0xaaaa,0xcccc],[0xfaaa,0xf0,0xcccc,0xff00],[0xfccc,0xf0,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_547 (AllBlocked.cons no_3_46 (AllBlocked.cons no_3_356 (AllBlocked.cons no_3_405 (AllBlocked.nil))))))
private theorem no_4_37 : search 4 [0xf0,0xfafa,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf0,0xfafa,0xaaaa,0xcccc,0xff00] [[0xa0,0xfafa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_1 (AllBlocked.nil))
private theorem no_4_38 : search 4 [0xf0,0xfcfc,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf0,0xfcfc,0xaaaa,0xcccc,0xff00] [[0xc0,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_7 (AllBlocked.nil))
private theorem no_4_39 : search 4 [0xf0,0xfff0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf0,0xfff0,0xaaaa,0xcccc,0xf0f0] [[0xff00,0xaaaa,0xcccc,0xf0f0],[0xf000,0xfff0,0xaaaa,0xcccc],[0xf00,0xf0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_326 (AllBlocked.cons no_3_46 (AllBlocked.nil))))
private theorem no_4_40 : search 4 [0xfa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfa,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_41 : search 4 [0xfc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfc,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_42 : search 4 [0x202,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x202,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_43 : search 4 [0x300,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x300,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_44 : search 4 [0x404,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x404,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_45 : search 4 [0x500,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x500,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_46 : search 4 [0x808,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x808,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xf8f8,0xaaaa,0xcccc,0xff00],[0xf700,0xaaaa,0xcccc,0xf0f0],[0xff08,0xaaaa,0xcccc,0xf0f0],[0xeeee,0x808,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_347 (AllBlocked.cons no_3_341 (AllBlocked.cons no_3_457 (AllBlocked.cons no_3_304 (AllBlocked.nil)))))
private theorem no_4_47 : search 4 [0xa00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xc4cc,0xaaaa,0xf0f0,0xff00],[0xcecc,0xaaaa,0xf0f0,0xff00],[0xfaf0,0xaaaa,0xcccc,0xff00],[0xffaa,0xa00,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_230 (AllBlocked.cons no_3_244 (AllBlocked.cons no_3_372 (AllBlocked.cons no_3_484 (AllBlocked.nil)))))
private theorem no_4_48 : search 4 [0xa0a,0xaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a,0xaa,0xcccc,0xf0f0,0xff00] [[0xf500,0xaa,0xcccc,0xf0f0],[0xaaa,0xcccc,0xf0f0,0xff00],[0xf050,0xa0a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_340 (AllBlocked.cons no_3_30 (AllBlocked.cons no_3_328 (AllBlocked.nil))))
private theorem no_4_49 : search 4 [0xa0a,0x2222,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a,0x2222,0xcccc,0xf0f0,0xff00] [[0x2a2a,0xcccc,0xf0f0,0xff00],[0xc4c4,0x2222,0xf0f0,0xff00],[0xd0d0,0xa0a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_76 (AllBlocked.cons no_3_229 (AllBlocked.cons no_3_246 (AllBlocked.nil))))
private theorem no_4_50 : search 4 [0xa0a,0x5050,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xa0a,0x5050,0xaaaa,0xcccc,0xff00] [[0x5a5a,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_166 (AllBlocked.nil))
private theorem no_4_51 : search 4 [0xa0a,0x5050,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a,0x5050,0xcccc,0xf0f0,0xff00] [[0x5a5a,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_167 (AllBlocked.nil))
private theorem no_4_52 : search 4 [0xa0a,0x5050,0xcccc,0xff00] = false :=
  noNode 3 [0xa0a,0x5050,0xcccc,0xff00] [[0x5a5a,0xcccc,0xff00],[0x5a5a,0x5050,0xcccc,0xff00],[0x5a5a,0xa0a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_168 (AllBlocked.cons no_3_164 (AllBlocked.cons no_3_163 (AllBlocked.nil))))
private theorem no_4_53 : search 4 [0xa0a,0xa0a0,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a,0xa0a0,0xcccc,0xf0f0,0xff00] [[0xaaaa,0xcccc,0xf0f0,0xff00],[0xfafa,0xa0a0,0xcccc,0xff00],[0xecec,0xa0a,0xf0f0,0xff00],[0x5050,0xa0a,0xcccc,0xff00],[0xffa0,0xa0a,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_384 (AllBlocked.cons no_3_266 (AllBlocked.cons no_3_138 (AllBlocked.cons no_3_472 (AllBlocked.nil))))))
private theorem no_4_54 : search 4 [0xa0a,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x5050,0xa0a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_138 (AllBlocked.nil))
private theorem no_4_55 : search 4 [0xa0a,0xeeee,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a,0xeeee,0xcccc,0xf0f0,0xff00] [[0x808,0xeeee,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_21 (AllBlocked.nil))
private theorem no_4_56 : search 4 [0xa0a,0xfafa,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xa0a,0xfafa,0xaaaa,0xcccc,0xff00] [[0xf0f0,0xaaaa,0xcccc,0xff00],[0xa0a0,0xfafa,0xcccc,0xff00],[0x5050,0xa0a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_201 (AllBlocked.cons no_3_138 (AllBlocked.nil))))
private theorem no_4_57 : search 4 [0xa0a,0xffaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a,0xffaa,0xcccc,0xf0f0,0xff00] [[0xa00,0xffaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_22 (AllBlocked.nil))
private theorem no_4_58 : search 4 [0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_59 : search 4 [0xaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_60 : search 4 [0xaaa,0xf000,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaaa,0xf000,0xcccc,0xf0f0,0xff00] [[0xfaaa,0xcccc,0xf0f0,0xff00],[0xccc,0xaaa,0xf0f0,0xff00],[0xfccc,0xaaa,0xf0f0,0xff00],[0xfff0,0xaaa,0xf000,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_359 (AllBlocked.cons no_3_41 (AllBlocked.cons no_3_406 (AllBlocked.cons no_3_543 (AllBlocked.nil)))))
private theorem no_4_61 : search 4 [0xc00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xa2aa,0xcccc,0xf0f0,0xff00],[0xaeaa,0xcccc,0xf0f0,0xff00],[0xfcf0,0xaaaa,0xcccc,0xff00],[0xffcc,0xc00,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_205 (AllBlocked.cons no_3_219 (AllBlocked.cons no_3_420 (AllBlocked.cons no_3_519 (AllBlocked.nil)))))
private theorem no_4_62 : search 4 [0xc0c,0xcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c,0xcc,0xaaaa,0xf0f0,0xff00] [[0xf300,0xcc,0xaaaa,0xf0f0],[0xccc,0xaaaa,0xf0f0,0xff00],[0xf030,0xc0c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_338 (AllBlocked.cons no_3_42 (AllBlocked.cons no_3_327 (AllBlocked.nil))))
private theorem no_4_63 : search 4 [0xc0c,0x3030,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xc0c,0x3030,0xaaaa,0xcccc,0xff00] [[0x3c3c,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_108 (AllBlocked.nil))
private theorem no_4_64 : search 4 [0xc0c,0x3030,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c,0x3030,0xaaaa,0xf0f0,0xff00] [[0x3c3c,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_109 (AllBlocked.nil))
private theorem no_4_65 : search 4 [0xc0c,0x3030,0xaaaa,0xff00] = false :=
  noNode 3 [0xc0c,0x3030,0xaaaa,0xff00] [[0x3c3c,0xaaaa,0xff00],[0x3c3c,0x3030,0xaaaa,0xff00],[0x3c3c,0xc0c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_110 (AllBlocked.cons no_3_107 (AllBlocked.cons no_3_106 (AllBlocked.nil))))
private theorem no_4_66 : search 4 [0xc0c,0x4444,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c,0x4444,0xaaaa,0xf0f0,0xff00] [[0x4c4c,0xaaaa,0xf0f0,0xff00],[0xa2a2,0x4444,0xf0f0,0xff00],[0xb0b0,0xc0c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_133 (AllBlocked.cons no_3_204 (AllBlocked.cons no_3_221 (AllBlocked.nil))))
private theorem no_4_67 : search 4 [0xc0c,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x3030,0xc0c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_81 (AllBlocked.nil))
private theorem no_4_68 : search 4 [0xc0c,0xc0c0,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c,0xc0c0,0xaaaa,0xf0f0,0xff00] [[0xcccc,0xaaaa,0xf0f0,0xff00],[0xfcfc,0xc0c0,0xaaaa,0xff00],[0x3030,0xc0c,0xaaaa,0xff00],[0xffc0,0xc0c,0xaaaa,0xf0f0],[0xeaea,0xc0c,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_433 (AllBlocked.cons no_3_81 (AllBlocked.cons no_3_507 (AllBlocked.cons no_3_254 (AllBlocked.nil))))))
private theorem no_4_69 : search 4 [0xc0c,0xeeee,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c,0xeeee,0xaaaa,0xf0f0,0xff00] [[0x808,0xeeee,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_21 (AllBlocked.nil))
private theorem no_4_70 : search 4 [0xc0c,0xfcfc,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xc0c,0xfcfc,0xaaaa,0xcccc,0xff00] [[0xf0f0,0xaaaa,0xcccc,0xff00],[0xc0c0,0xfcfc,0xaaaa,0xff00],[0x3030,0xc0c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_226 (AllBlocked.cons no_3_81 (AllBlocked.nil))))
private theorem no_4_71 : search 4 [0xc0c,0xffcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c,0xffcc,0xaaaa,0xf0f0,0xff00] [[0xc00,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_34 (AllBlocked.nil))
private theorem no_4_72 : search 4 [0xccc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xccc,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_73 : search 4 [0xccc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xccc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_74 : search 4 [0xccc,0xf000,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xccc,0xf000,0xaaaa,0xf0f0,0xff00] [[0xfccc,0xaaaa,0xf0f0,0xff00],[0xaaa,0xccc,0xf0f0,0xff00],[0xfaaa,0xccc,0xf0f0,0xff00],[0xfff0,0xccc,0xf000,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_408 (AllBlocked.cons no_3_29 (AllBlocked.cons no_3_357 (AllBlocked.cons no_3_544 (AllBlocked.nil)))))
private theorem no_4_75 : search 4 [0xe0e,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xe0e,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_76 : search 4 [0xf00,0xf0,0xaaaa,0xcccc] = false :=
  noNode 3 [0xf00,0xf0,0xaaaa,0xcccc] [[0xff0,0xaaaa,0xcccc],[0xff0,0xf00,0xaaaa,0xcccc],[0xff0,0xf0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_54 (AllBlocked.cons no_3_53 (AllBlocked.cons no_3_52 (AllBlocked.nil))))
private theorem no_4_77 : search 4 [0xf00,0xf0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf00,0xf0,0xaaaa,0xcccc,0xf0f0] [[0xff0,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_55 (AllBlocked.nil))
private theorem no_4_78 : search 4 [0xf00,0xf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf00,0xf0,0xaaaa,0xcccc,0xff00] [[0xff0,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_56 (AllBlocked.nil))
private theorem no_4_79 : search 4 [0xf00,0x3300,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf00,0x3300,0xaaaa,0xcccc,0xf0f0] [[0x3f00,0xaaaa,0xcccc,0xf0f0],[0xc0cc,0x3300,0xaaaa,0xf0f0],[0xc0f0,0xf00,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_114 (AllBlocked.cons no_3_227 (AllBlocked.cons no_3_228 (AllBlocked.nil))))
private theorem no_4_80 : search 4 [0xf00,0x5500,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf00,0x5500,0xaaaa,0xcccc,0xf0f0] [[0x5f00,0xaaaa,0xcccc,0xf0f0],[0xa0aa,0x5500,0xcccc,0xf0f0],[0xa0f0,0xf00,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_172 (AllBlocked.cons no_3_202 (AllBlocked.cons no_3_203 (AllBlocked.nil))))
private theorem no_4_81 : search 4 [0xf00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xf0,0xf00,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_13 (AllBlocked.nil))
private theorem no_4_82 : search 4 [0xf00,0xf000,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf00,0xf000,0xaaaa,0xcccc,0xf0f0] [[0xff00,0xaaaa,0xcccc,0xf0f0],[0xfff0,0xf000,0xaaaa,0xcccc],[0xf0,0xf00,0xaaaa,0xcccc],[0xfaaa,0xf00,0xcccc,0xf0f0],[0xfccc,0xf00,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_547 (AllBlocked.cons no_3_13 (AllBlocked.cons no_3_358 (AllBlocked.cons no_3_407 (AllBlocked.nil))))))
private theorem no_4_83 : search 4 [0xf00,0xffaa,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf00,0xffaa,0xaaaa,0xcccc,0xf0f0] [[0xa00,0xffaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_22 (AllBlocked.nil))
private theorem no_4_84 : search 4 [0xf00,0xffcc,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf00,0xffcc,0xaaaa,0xcccc,0xf0f0] [[0xc00,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_34 (AllBlocked.nil))
private theorem no_4_85 : search 4 [0xf00,0xfff0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf00,0xfff0,0xaaaa,0xcccc,0xff00] [[0xf0f0,0xaaaa,0xcccc,0xff00],[0xf000,0xfff0,0xaaaa,0xcccc],[0xf0,0xf00,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_326 (AllBlocked.cons no_3_13 (AllBlocked.nil))))
private theorem no_4_86 : search 4 [0xf0a,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf0a,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_87 : search 4 [0xf0c,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf0c,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_88 : search 4 [0x1010,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x1010,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_89 : search 4 [0x1100,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x1100,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_90 : search 4 [0x2020,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2020,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xecec,0xaaaa,0xf0f0,0xff00],[0xdf00,0xaaaa,0xcccc,0xf0f0],[0xff20,0xaaaa,0xcccc,0xf0f0],[0xfafa,0x2020,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_270 (AllBlocked.cons no_3_250 (AllBlocked.cons no_3_458 (AllBlocked.cons no_3_381 (AllBlocked.nil)))))
private theorem no_4_91 : search 4 [0x2200,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2200,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xeecc,0xaaaa,0xf0f0,0xff00],[0xd0f0,0xaaaa,0xcccc,0xff00],[0xf2f0,0xaaaa,0xcccc,0xff00],[0xffaa,0x2200,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_294 (AllBlocked.cons no_3_247 (AllBlocked.cons no_3_337 (AllBlocked.cons no_3_485 (AllBlocked.nil)))))
private theorem no_4_92 : search 4 [0x2222,0xaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0xaa,0xcccc,0xf0f0,0xff00] [[0xdd00,0xaa,0xcccc,0xf0f0],[0x22aa,0xcccc,0xf0f0,0xff00],[0xcc44,0x2222,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_249 (AllBlocked.cons no_3_71 (AllBlocked.cons no_3_235 (AllBlocked.nil))))
private theorem no_4_93 : search 4 [0x2222,0xa0a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0xa0a,0xcccc,0xf0f0,0xff00] [[0xd0d0,0xa0a,0xcccc,0xff00],[0x2a2a,0xcccc,0xf0f0,0xff00],[0xc4c4,0x2222,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_246 (AllBlocked.cons no_3_76 (AllBlocked.cons no_3_229 (AllBlocked.nil))))
private theorem no_4_94 : search 4 [0x2222,0x4444,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0x4444,0xaaaa,0xf0f0,0xff00] [[0x6666,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_178 (AllBlocked.nil))
private theorem no_4_95 : search 4 [0x2222,0x4444,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0x4444,0xcccc,0xf0f0,0xff00] [[0x6666,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_179 (AllBlocked.nil))
private theorem no_4_96 : search 4 [0x2222,0x4444,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0x4444,0xf0f0,0xff00] [[0x6666,0xf0f0,0xff00],[0x6666,0x4444,0xf0f0,0xff00],[0x6666,0x2222,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_181 (AllBlocked.cons no_3_176 (AllBlocked.cons no_3_175 (AllBlocked.nil))))
private theorem no_4_97 : search 4 [0x2222,0x8888,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0x8888,0xcccc,0xf0f0,0xff00] [[0xaaaa,0xcccc,0xf0f0,0xff00],[0xeeee,0x8888,0xf0f0,0xff00],[0x4444,0x2222,0xf0f0,0xff00],[0xf8f8,0x2222,0xcccc,0xff00],[0xff88,0x2222,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_307 (AllBlocked.cons no_3_120 (AllBlocked.cons no_3_343 (AllBlocked.cons no_3_461 (AllBlocked.nil))))))
private theorem no_4_98 : search 4 [0x2222,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x4444,0x2222,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_120 (AllBlocked.nil))
private theorem no_4_99 : search 4 [0x2222,0xeeee,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0xeeee,0xaaaa,0xf0f0,0xff00] [[0xcccc,0xaaaa,0xf0f0,0xff00],[0x8888,0xeeee,0xf0f0,0xff00],[0x4444,0x2222,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_194 (AllBlocked.cons no_3_120 (AllBlocked.nil))))
private theorem no_4_100 : search 4 [0x2222,0xfafa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0xfafa,0xcccc,0xf0f0,0xff00] [[0x2020,0xfafa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_61 (AllBlocked.nil))
private theorem no_4_101 : search 4 [0x2222,0xffaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2222,0xffaa,0xcccc,0xf0f0,0xff00] [[0x2200,0xffaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_62 (AllBlocked.nil))
private theorem no_4_102 : search 4 [0x22aa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x22aa,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_103 : search 4 [0x22aa,0xcc00,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x22aa,0xcc00,0xcccc,0xf0f0,0xff00] [[0xeeaa,0xcccc,0xf0f0,0xff00],[0x30f0,0x22aa,0xcccc,0xff00],[0xfcf0,0x22aa,0xcccc,0xff00],[0xffcc,0x22aa,0xcc00,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_283 (AllBlocked.cons no_3_87 (AllBlocked.cons no_3_418 (AllBlocked.cons no_3_520 (AllBlocked.nil)))))
private theorem no_4_104 : search 4 [0x22aa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x22aa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_105 : search 4 [0x2a2a,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2a2a,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_106 : search 4 [0x2a2a,0xc0c0,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2a2a,0xc0c0,0xcccc,0xf0f0,0xff00] [[0xeaea,0xcccc,0xf0f0,0xff00],[0x3f00,0x2a2a,0xcccc,0xf0f0],[0xffc0,0x2a2a,0xcccc,0xf0f0],[0xfcfc,0x2a2a,0xc0c0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_258 (AllBlocked.cons no_3_113 (AllBlocked.cons no_3_508 (AllBlocked.cons no_3_430 (AllBlocked.nil)))))
private theorem no_4_107 : search 4 [0x2a2a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x2a2a,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_108 : search 4 [0x3000,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x3000,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x8aaa,0xcccc,0xf0f0,0xff00],[0xbaaa,0xcccc,0xf0f0,0xff00],[0xfccc,0xaaaa,0xf0f0,0xff00],[0xfff0,0x3000,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_198 (AllBlocked.cons no_3_223 (AllBlocked.cons no_3_408 (AllBlocked.cons no_3_545 (AllBlocked.nil)))))
private theorem no_4_109 : search 4 [0x3030,0xf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x3030,0xf0,0xaaaa,0xcccc,0xff00] [[0xcf00,0xf0,0xaaaa,0xcccc],[0x30f0,0xaaaa,0xcccc,0xff00],[0xcc0c,0x3030,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_245 (AllBlocked.cons no_3_88 (AllBlocked.cons no_3_234 (AllBlocked.nil))))
private theorem no_4_110 : search 4 [0x3030,0xc0c,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x3030,0xc0c,0xaaaa,0xcccc,0xff00] [[0x3c3c,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_108 (AllBlocked.nil))
private theorem no_4_111 : search 4 [0x3030,0xc0c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x3030,0xc0c,0xaaaa,0xf0f0,0xff00] [[0x3c3c,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_109 (AllBlocked.nil))
private theorem no_4_112 : search 4 [0x3030,0xc0c,0xaaaa,0xff00] = false :=
  noNode 3 [0x3030,0xc0c,0xaaaa,0xff00] [[0x3c3c,0xaaaa,0xff00],[0x3c3c,0x3030,0xaaaa,0xff00],[0x3c3c,0xc0c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_110 (AllBlocked.cons no_3_107 (AllBlocked.cons no_3_106 (AllBlocked.nil))))
private theorem no_4_113 : search 4 [0x3030,0x5050,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x3030,0x5050,0xaaaa,0xcccc,0xff00] [[0x7070,0xaaaa,0xcccc,0xff00],[0x8a8a,0x5050,0xcccc,0xff00],[0x8c8c,0x3030,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_184 (AllBlocked.cons no_3_197 (AllBlocked.cons no_3_199 (AllBlocked.nil))))
private theorem no_4_114 : search 4 [0x3030,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x3030,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xc0c,0x3030,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_35 (AllBlocked.nil))
private theorem no_4_115 : search 4 [0x3030,0xc0c0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x3030,0xc0c0,0xaaaa,0xcccc,0xff00] [[0xf0f0,0xaaaa,0xcccc,0xff00],[0xfcfc,0xc0c0,0xaaaa,0xff00],[0xc0c,0x3030,0xaaaa,0xff00],[0xffc0,0x3030,0xaaaa,0xcccc],[0xeaea,0x3030,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_433 (AllBlocked.cons no_3_35 (AllBlocked.cons no_3_509 (AllBlocked.cons no_3_255 (AllBlocked.nil))))))
private theorem no_4_116 : search 4 [0x3030,0xfafa,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x3030,0xfafa,0xaaaa,0xcccc,0xff00] [[0x2020,0xfafa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_61 (AllBlocked.nil))
private theorem no_4_117 : search 4 [0x3030,0xfcfc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x3030,0xfcfc,0xaaaa,0xf0f0,0xff00] [[0xcccc,0xaaaa,0xf0f0,0xff00],[0xc0c0,0xfcfc,0xaaaa,0xff00],[0xc0c,0x3030,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_226 (AllBlocked.cons no_3_35 (AllBlocked.nil))))
private theorem no_4_118 : search 4 [0x3030,0xfff0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x3030,0xfff0,0xaaaa,0xcccc,0xff00] [[0x3000,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_80 (AllBlocked.nil))
private theorem no_4_119 : search 4 [0x30f0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x30f0,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_120 : search 4 [0x30f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x30f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_121 : search 4 [0x30f0,0xcc00,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x30f0,0xcc00,0xaaaa,0xcccc,0xff00] [[0xfcf0,0xaaaa,0xcccc,0xff00],[0x22aa,0x30f0,0xcccc,0xff00],[0xeeaa,0x30f0,0xcccc,0xff00],[0xffcc,0x30f0,0xcc00,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_420 (AllBlocked.cons no_3_69 (AllBlocked.cons no_3_280 (AllBlocked.cons no_3_521 (AllBlocked.nil)))))
private theorem no_4_122 : search 4 [0x3232,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x3232,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_123 : search 4 [0x3300,0xcc,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x3300,0xcc,0xaaaa,0xcccc,0xf0f0] [[0x33cc,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_100 (AllBlocked.nil))
private theorem no_4_124 : search 4 [0x3300,0xcc,0xaaaa,0xf0f0] = false :=
  noNode 3 [0x3300,0xcc,0xaaaa,0xf0f0] [[0x33cc,0xaaaa,0xf0f0],[0x33cc,0x3300,0xaaaa,0xf0f0],[0x33cc,0xcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_101 (AllBlocked.cons no_3_99 (AllBlocked.cons no_3_98 (AllBlocked.nil))))
private theorem no_4_125 : search 4 [0x3300,0xcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x3300,0xcc,0xaaaa,0xf0f0,0xff00] [[0x33cc,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_102 (AllBlocked.nil))
private theorem no_4_126 : search 4 [0x3300,0xf00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x3300,0xf00,0xaaaa,0xcccc,0xf0f0] [[0xc0f0,0xf00,0xaaaa,0xcccc],[0x3f00,0xaaaa,0xcccc,0xf0f0],[0xc0cc,0x3300,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_228 (AllBlocked.cons no_3_114 (AllBlocked.cons no_3_227 (AllBlocked.nil))))
private theorem no_4_127 : search 4 [0x3300,0x5500,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x3300,0x5500,0xaaaa,0xcccc,0xf0f0] [[0x7700,0xaaaa,0xcccc,0xf0f0],[0x88aa,0x5500,0xcccc,0xf0f0],[0x88cc,0x3300,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_190 (AllBlocked.cons no_3_195 (AllBlocked.cons no_3_196 (AllBlocked.nil))))
private theorem no_4_128 : search 4 [0x3300,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x3300,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xcc,0x3300,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_8 (AllBlocked.nil))
private theorem no_4_129 : search 4 [0x3300,0xcc00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x3300,0xcc00,0xaaaa,0xcccc,0xf0f0] [[0xff00,0xaaaa,0xcccc,0xf0f0],[0xffcc,0xcc00,0xaaaa,0xf0f0],[0xcc,0x3300,0xaaaa,0xf0f0],[0xfcf0,0x3300,0xaaaa,0xcccc],[0xeeaa,0x3300,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_523 (AllBlocked.cons no_3_8 (AllBlocked.cons no_3_419 (AllBlocked.cons no_3_281 (AllBlocked.nil))))))
private theorem no_4_130 : search 4 [0x3300,0xffaa,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x3300,0xffaa,0xaaaa,0xcccc,0xf0f0] [[0x2200,0xffaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_62 (AllBlocked.nil))
private theorem no_4_131 : search 4 [0x3300,0xffcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x3300,0xffcc,0xaaaa,0xf0f0,0xff00] [[0xcccc,0xaaaa,0xf0f0,0xff00],[0xcc00,0xffcc,0xaaaa,0xf0f0],[0xcc,0x3300,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_233 (AllBlocked.cons no_3_8 (AllBlocked.nil))))
private theorem no_4_132 : search 4 [0x3300,0xfff0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x3300,0xfff0,0xaaaa,0xcccc,0xf0f0] [[0x3000,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_80 (AllBlocked.nil))
private theorem no_4_133 : search 4 [0x3322,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x3322,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_134 : search 4 [0x3330,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x3330,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_135 : search 4 [0x3f00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x3f00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_136 : search 4 [0x3f00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x3f00,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_137 : search 4 [0x3f00,0xc0c0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x3f00,0xc0c0,0xaaaa,0xcccc,0xf0f0] [[0xffc0,0xaaaa,0xcccc,0xf0f0],[0x2a2a,0x3f00,0xcccc,0xf0f0],[0xeaea,0x3f00,0xcccc,0xf0f0],[0xfcfc,0x3f00,0xc0c0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_510 (AllBlocked.cons no_3_74 (AllBlocked.cons no_3_256 (AllBlocked.cons no_3_431 (AllBlocked.nil)))))
private theorem no_4_138 : search 4 [0x4040,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x4040,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xeaea,0xcccc,0xf0f0,0xff00],[0xbf00,0xaaaa,0xcccc,0xf0f0],[0xff40,0xaaaa,0xcccc,0xf0f0],[0xfcfc,0x4040,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_258 (AllBlocked.cons no_3_225 (AllBlocked.cons no_3_459 (AllBlocked.cons no_3_432 (AllBlocked.nil)))))
private theorem no_4_139 : search 4 [0x4400,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x4400,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xeeaa,0xcccc,0xf0f0,0xff00],[0xb0f0,0xaaaa,0xcccc,0xff00],[0xf4f0,0xaaaa,0xcccc,0xff00],[0xffcc,0x4400,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_283 (AllBlocked.cons no_3_222 (AllBlocked.cons no_3_339 (AllBlocked.cons no_3_522 (AllBlocked.nil)))))
private theorem no_4_140 : search 4 [0x4444,0xcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0xcc,0xaaaa,0xf0f0,0xff00] [[0xbb00,0xcc,0xaaaa,0xf0f0],[0x44cc,0xaaaa,0xf0f0,0xff00],[0xaa22,0x4444,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_224 (AllBlocked.cons no_3_128 (AllBlocked.cons no_3_210 (AllBlocked.nil))))
private theorem no_4_141 : search 4 [0x4444,0xc0c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0xc0c,0xaaaa,0xf0f0,0xff00] [[0xb0b0,0xc0c,0xaaaa,0xff00],[0x4c4c,0xaaaa,0xf0f0,0xff00],[0xa2a2,0x4444,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_221 (AllBlocked.cons no_3_133 (AllBlocked.cons no_3_204 (AllBlocked.nil))))
private theorem no_4_142 : search 4 [0x4444,0x2222,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0x2222,0xaaaa,0xf0f0,0xff00] [[0x6666,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_178 (AllBlocked.nil))
private theorem no_4_143 : search 4 [0x4444,0x2222,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0x2222,0xcccc,0xf0f0,0xff00] [[0x6666,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_179 (AllBlocked.nil))
private theorem no_4_144 : search 4 [0x4444,0x2222,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0x2222,0xf0f0,0xff00] [[0x6666,0xf0f0,0xff00],[0x6666,0x4444,0xf0f0,0xff00],[0x6666,0x2222,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_181 (AllBlocked.cons no_3_176 (AllBlocked.cons no_3_175 (AllBlocked.nil))))
private theorem no_4_145 : search 4 [0x4444,0x8888,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0x8888,0xaaaa,0xf0f0,0xff00] [[0xcccc,0xaaaa,0xf0f0,0xff00],[0xeeee,0x8888,0xf0f0,0xff00],[0x2222,0x4444,0xf0f0,0xff00],[0xf8f8,0x4444,0xaaaa,0xff00],[0xff88,0x4444,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_307 (AllBlocked.cons no_3_63 (AllBlocked.cons no_3_344 (AllBlocked.cons no_3_462 (AllBlocked.nil))))))
private theorem no_4_146 : search 4 [0x4444,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x2222,0x4444,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_63 (AllBlocked.nil))
private theorem no_4_147 : search 4 [0x4444,0xeeee,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0xeeee,0xcccc,0xf0f0,0xff00] [[0xaaaa,0xcccc,0xf0f0,0xff00],[0x8888,0xeeee,0xf0f0,0xff00],[0x2222,0x4444,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_194 (AllBlocked.cons no_3_63 (AllBlocked.nil))))
private theorem no_4_148 : search 4 [0x4444,0xfcfc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0xfcfc,0xaaaa,0xf0f0,0xff00] [[0x4040,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_118 (AllBlocked.nil))
private theorem no_4_149 : search 4 [0x4444,0xffcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x4444,0xffcc,0xaaaa,0xf0f0,0xff00] [[0x4400,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_119 (AllBlocked.nil))
private theorem no_4_150 : search 4 [0x44cc,0xaa00,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x44cc,0xaa00,0xaaaa,0xf0f0,0xff00] [[0xeecc,0xaaaa,0xf0f0,0xff00],[0x50f0,0x44cc,0xaaaa,0xff00],[0xfaf0,0x44cc,0xaaaa,0xff00],[0xffaa,0x44cc,0xaa00,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_294 (AllBlocked.cons no_3_144 (AllBlocked.cons no_3_369 (AllBlocked.cons no_3_486 (AllBlocked.nil)))))
private theorem no_4_151 : search 4 [0x44cc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x44cc,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_152 : search 4 [0x44cc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x44cc,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_153 : search 4 [0x4c4c,0xa0a0,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x4c4c,0xa0a0,0xaaaa,0xf0f0,0xff00] [[0xecec,0xaaaa,0xf0f0,0xff00],[0x5f00,0x4c4c,0xaaaa,0xf0f0],[0xffa0,0x4c4c,0xaaaa,0xf0f0],[0xfafa,0x4c4c,0xa0a0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_270 (AllBlocked.cons no_3_170 (AllBlocked.cons no_3_473 (AllBlocked.cons no_3_382 (AllBlocked.nil)))))
private theorem no_4_154 : search 4 [0x4c4c,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x4c4c,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_155 : search 4 [0x4c4c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x4c4c,0xaaaa,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_156 : search 4 [0x5000,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5000,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfaaa,0xcccc,0xf0f0,0xff00],[0x8ccc,0xaaaa,0xf0f0,0xff00],[0xdccc,0xaaaa,0xf0f0,0xff00],[0xfff0,0x5000,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_359 (AllBlocked.cons no_3_200 (AllBlocked.cons no_3_248 (AllBlocked.cons no_3_546 (AllBlocked.nil)))))
private theorem no_4_157 : search 4 [0x5050,0xf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x5050,0xf0,0xaaaa,0xcccc,0xff00] [[0xaf00,0xf0,0xaaaa,0xcccc],[0x50f0,0xaaaa,0xcccc,0xff00],[0xaa0a,0x5050,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_220 (AllBlocked.cons no_3_146 (AllBlocked.cons no_3_209 (AllBlocked.nil))))
private theorem no_4_158 : search 4 [0x5050,0xa0a,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x5050,0xa0a,0xaaaa,0xcccc,0xff00] [[0x5a5a,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_166 (AllBlocked.nil))
private theorem no_4_159 : search 4 [0x5050,0xa0a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5050,0xa0a,0xcccc,0xf0f0,0xff00] [[0x5a5a,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_167 (AllBlocked.nil))
private theorem no_4_160 : search 4 [0x5050,0xa0a,0xcccc,0xff00] = false :=
  noNode 3 [0x5050,0xa0a,0xcccc,0xff00] [[0x5a5a,0xcccc,0xff00],[0x5a5a,0x5050,0xcccc,0xff00],[0x5a5a,0xa0a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_168 (AllBlocked.cons no_3_164 (AllBlocked.cons no_3_163 (AllBlocked.nil))))
private theorem no_4_161 : search 4 [0x5050,0x3030,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x5050,0x3030,0xaaaa,0xcccc,0xff00] [[0x8c8c,0x3030,0xaaaa,0xff00],[0x7070,0xaaaa,0xcccc,0xff00],[0x8a8a,0x5050,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_199 (AllBlocked.cons no_3_184 (AllBlocked.cons no_3_197 (AllBlocked.nil))))
private theorem no_4_162 : search 4 [0x5050,0xa0a0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x5050,0xa0a0,0xaaaa,0xcccc,0xff00] [[0xf0f0,0xaaaa,0xcccc,0xff00],[0xfafa,0xa0a0,0xcccc,0xff00],[0xa0a,0x5050,0xcccc,0xff00],[0xecec,0x5050,0xaaaa,0xff00],[0xffa0,0x5050,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_384 (AllBlocked.cons no_3_23 (AllBlocked.cons no_3_267 (AllBlocked.cons no_3_474 (AllBlocked.nil))))))
private theorem no_4_163 : search 4 [0x5050,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5050,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xa0a,0x5050,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_23 (AllBlocked.nil))
private theorem no_4_164 : search 4 [0x5050,0xfafa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5050,0xfafa,0xcccc,0xf0f0,0xff00] [[0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0a0,0xfafa,0xcccc,0xff00],[0xa0a,0x5050,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_201 (AllBlocked.cons no_3_23 (AllBlocked.nil))))
private theorem no_4_165 : search 4 [0x5050,0xfcfc,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x5050,0xfcfc,0xaaaa,0xcccc,0xff00] [[0x4040,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_118 (AllBlocked.nil))
private theorem no_4_166 : search 4 [0x5050,0xfff0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x5050,0xfff0,0xaaaa,0xcccc,0xff00] [[0x5000,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_137 (AllBlocked.nil))
private theorem no_4_167 : search 4 [0x50f0,0xaa00,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x50f0,0xaa00,0xaaaa,0xcccc,0xff00] [[0xfaf0,0xaaaa,0xcccc,0xff00],[0x44cc,0x50f0,0xaaaa,0xff00],[0xeecc,0x50f0,0xaaaa,0xff00],[0xffaa,0x50f0,0xaa00,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_372 (AllBlocked.cons no_3_126 (AllBlocked.cons no_3_291 (AllBlocked.cons no_3_487 (AllBlocked.nil)))))
private theorem no_4_168 : search 4 [0x50f0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x50f0,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_169 : search 4 [0x50f0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x50f0,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_170 : search 4 [0x5454,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5454,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_171 : search 4 [0x5500,0xaa,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x5500,0xaa,0xaaaa,0xcccc,0xf0f0] [[0x55aa,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_158 (AllBlocked.nil))
private theorem no_4_172 : search 4 [0x5500,0xaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x5500,0xaa,0xcccc,0xf0f0] [[0x55aa,0xcccc,0xf0f0],[0x55aa,0x5500,0xcccc,0xf0f0],[0x55aa,0xaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_159 (AllBlocked.cons no_3_156 (AllBlocked.cons no_3_155 (AllBlocked.nil))))
private theorem no_4_173 : search 4 [0x5500,0xaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5500,0xaa,0xcccc,0xf0f0,0xff00] [[0x55aa,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_160 (AllBlocked.nil))
private theorem no_4_174 : search 4 [0x5500,0xf00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x5500,0xf00,0xaaaa,0xcccc,0xf0f0] [[0xa0f0,0xf00,0xaaaa,0xcccc],[0x5f00,0xaaaa,0xcccc,0xf0f0],[0xa0aa,0x5500,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_203 (AllBlocked.cons no_3_172 (AllBlocked.cons no_3_202 (AllBlocked.nil))))
private theorem no_4_175 : search 4 [0x5500,0x3300,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x5500,0x3300,0xaaaa,0xcccc,0xf0f0] [[0x88cc,0x3300,0xaaaa,0xf0f0],[0x7700,0xaaaa,0xcccc,0xf0f0],[0x88aa,0x5500,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_196 (AllBlocked.cons no_3_190 (AllBlocked.cons no_3_195 (AllBlocked.nil))))
private theorem no_4_176 : search 4 [0x5500,0xaa00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x5500,0xaa00,0xaaaa,0xcccc,0xf0f0] [[0xff00,0xaaaa,0xcccc,0xf0f0],[0xffaa,0xaa00,0xcccc,0xf0f0],[0xaa,0x5500,0xcccc,0xf0f0],[0xeecc,0x5500,0xaaaa,0xf0f0],[0xfaf0,0x5500,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_488 (AllBlocked.cons no_3_2 (AllBlocked.cons no_3_292 (AllBlocked.cons no_3_370 (AllBlocked.nil))))))
private theorem no_4_177 : search 4 [0x5500,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5500,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaa,0x5500,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_2 (AllBlocked.nil))
private theorem no_4_178 : search 4 [0x5500,0xffaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5500,0xffaa,0xcccc,0xf0f0,0xff00] [[0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa00,0xffaa,0xcccc,0xf0f0],[0xaa,0x5500,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_208 (AllBlocked.cons no_3_2 (AllBlocked.nil))))
private theorem no_4_179 : search 4 [0x5500,0xffcc,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x5500,0xffcc,0xaaaa,0xcccc,0xf0f0] [[0x4400,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_119 (AllBlocked.nil))
private theorem no_4_180 : search 4 [0x5500,0xfff0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x5500,0xfff0,0xaaaa,0xcccc,0xf0f0] [[0x5000,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_137 (AllBlocked.nil))
private theorem no_4_181 : search 4 [0x5544,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5544,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_182 : search 4 [0x5550,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5550,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_183 : search 4 [0x5f00,0xa0a0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x5f00,0xa0a0,0xaaaa,0xcccc,0xf0f0] [[0xffa0,0xaaaa,0xcccc,0xf0f0],[0x4c4c,0x5f00,0xaaaa,0xf0f0],[0xecec,0x5f00,0xaaaa,0xf0f0],[0xfafa,0x5f00,0xa0a0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_476 (AllBlocked.cons no_3_131 (AllBlocked.cons no_3_268 (AllBlocked.cons no_3_383 (AllBlocked.nil)))))
private theorem no_4_184 : search 4 [0x5f00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x5f00,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_185 : search 4 [0x5f00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x5f00,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_186 : search 4 [0x7070,0x8888,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x7070,0x8888,0xaaaa,0xcccc,0xff00] [[0xf8f8,0xaaaa,0xcccc,0xff00],[0x7700,0x7070,0xaaaa,0xcccc],[0xff88,0x7070,0xaaaa,0xcccc],[0xeeee,0x7070,0x8888,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_347 (AllBlocked.cons no_3_188 (AllBlocked.cons no_3_463 (AllBlocked.cons no_3_305 (AllBlocked.nil)))))
private theorem no_4_187 : search 4 [0x7070,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x7070,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_188 : search 4 [0x7070,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0x7070,0xaaaa,0xcccc,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_189 : search 4 [0x7700,0x8888,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x7700,0x8888,0xaaaa,0xcccc,0xf0f0] [[0xff88,0xaaaa,0xcccc,0xf0f0],[0x7070,0x7700,0xaaaa,0xcccc],[0xf8f8,0x7700,0xaaaa,0xcccc],[0xeeee,0x7700,0x8888,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_465 (AllBlocked.cons no_3_182 (AllBlocked.cons no_3_345 (AllBlocked.cons no_3_306 (AllBlocked.nil)))))
private theorem no_4_190 : search 4 [0x7700,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0x7700,0xaaaa,0xcccc,0xf0f0] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_191 : search 4 [0x7700,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x7700,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_192 : search 4 [0x8080,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x8080,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x2a2a,0xcccc,0xf0f0,0xff00],[0x4c4c,0xaaaa,0xf0f0,0xff00],[0x7070,0xaaaa,0xcccc,0xff00],[0x7f00,0xaaaa,0xcccc,0xf0f0],[0xff80,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_76 (AllBlocked.cons no_3_133 (AllBlocked.cons no_3_184 (AllBlocked.cons no_3_193 (AllBlocked.cons no_3_460 (AllBlocked.nil))))))
private theorem no_4_193 : search 4 [0x8800,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x8800,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x22aa,0xcccc,0xf0f0,0xff00],[0x44cc,0xaaaa,0xf0f0,0xff00],[0x70f0,0xaaaa,0xcccc,0xff00],[0xf8f0,0xaaaa,0xcccc,0xff00],[0x7700,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_71 (AllBlocked.cons no_3_128 (AllBlocked.cons no_3_187 (AllBlocked.cons no_3_342 (AllBlocked.cons no_3_190 (AllBlocked.nil))))))
private theorem no_4_194 : search 4 [0x8888,0x2222,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x8888,0x2222,0xcccc,0xf0f0,0xff00] [[0x4444,0x2222,0xf0f0,0xff00],[0xf8f8,0x2222,0xcccc,0xff00],[0xff88,0x2222,0xcccc,0xf0f0],[0xaaaa,0xcccc,0xf0f0,0xff00],[0xeeee,0x8888,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_120 (AllBlocked.cons no_3_343 (AllBlocked.cons no_3_461 (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_307 (AllBlocked.nil))))))
private theorem no_4_195 : search 4 [0x8888,0x4444,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x8888,0x4444,0xaaaa,0xf0f0,0xff00] [[0x2222,0x4444,0xf0f0,0xff00],[0xf8f8,0x4444,0xaaaa,0xff00],[0xff88,0x4444,0xaaaa,0xf0f0],[0xcccc,0xaaaa,0xf0f0,0xff00],[0xeeee,0x8888,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_63 (AllBlocked.cons no_3_344 (AllBlocked.cons no_3_462 (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_307 (AllBlocked.nil))))))
private theorem no_4_196 : search 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x7070,0xaaaa,0xcccc,0xff00],[0xf8f8,0xaaaa,0xcccc,0xff00],[0x7700,0xaaaa,0xcccc,0xf0f0],[0xff88,0xaaaa,0xcccc,0xf0f0],[0xeeee,0x8888,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_184 (AllBlocked.cons no_3_347 (AllBlocked.cons no_3_190 (AllBlocked.cons no_3_465 (AllBlocked.cons no_3_307 (AllBlocked.nil))))))
private theorem no_4_197 : search 4 [0x8888,0xeeee,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0x8888,0xeeee,0xaaaa,0xf0f0,0xff00] [[0x6666,0xaaaa,0xf0f0,0xff00],[0xf8f8,0xeeee,0xaaaa,0xff00],[0xff88,0xeeee,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_178 (AllBlocked.cons no_3_349 (AllBlocked.cons no_3_467 (AllBlocked.nil))))
private theorem no_4_198 : search 4 [0x8888,0xeeee,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x8888,0xeeee,0xcccc,0xf0f0,0xff00] [[0x6666,0xcccc,0xf0f0,0xff00],[0xf8f8,0xeeee,0xcccc,0xff00],[0xff88,0xeeee,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_179 (AllBlocked.cons no_3_350 (AllBlocked.cons no_3_468 (AllBlocked.nil))))
private theorem no_4_199 : search 4 [0x8888,0xeeee,0xf0f0,0xff00] = false :=
  noNode 3 [0x8888,0xeeee,0xf0f0,0xff00] [[0x6666,0xf0f0,0xff00],[0x6666,0xeeee,0xf0f0,0xff00],[0x6666,0x8888,0xf0f0,0xff00],[0x808,0xeeee,0xf0f0,0xff00],[0x7070,0x8888,0xeeee,0xff00],[0xf8f8,0xeeee,0xff00],[0xf8f8,0xeeee,0xf0f0,0xff00],[0xf8f8,0x8888,0xeeee,0xff00],[0x88,0xeeee,0xf0f0,0xff00],[0x7700,0x8888,0xeeee,0xf0f0],[0xff88,0xeeee,0xf0f0],[0xff88,0xeeee,0xf0f0,0xff00],[0xff88,0x8888,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_181 (AllBlocked.cons no_3_180 (AllBlocked.cons no_3_177 (AllBlocked.cons no_3_21 (AllBlocked.cons no_3_183 (AllBlocked.cons no_3_352 (AllBlocked.cons no_3_351 (AllBlocked.cons no_3_346 (AllBlocked.cons no_3_0 (AllBlocked.cons no_3_189 (AllBlocked.cons no_3_469 (AllBlocked.cons no_3_470 (AllBlocked.cons no_3_464 (AllBlocked.nil))))))))))))))
private theorem no_4_200 : search 4 [0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x7700,0xaaaa,0xcccc,0xf0f0],[0x5500,0x88aa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_190 (AllBlocked.cons no_3_150 (AllBlocked.nil)))
private theorem no_4_201 : search 4 [0x88cc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x88cc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x7700,0xaaaa,0xcccc,0xf0f0],[0x3300,0x88cc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_190 (AllBlocked.cons no_3_93 (AllBlocked.nil)))
private theorem no_4_202 : search 4 [0x8a8a,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x8a8a,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x7070,0xaaaa,0xcccc,0xff00],[0x5050,0x8a8a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_184 (AllBlocked.cons no_3_139 (AllBlocked.nil)))
private theorem no_4_203 : search 4 [0x8c8c,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0x8c8c,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x7070,0xaaaa,0xcccc,0xff00],[0x3030,0x8c8c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_184 (AllBlocked.cons no_3_82 (AllBlocked.nil)))
private theorem no_4_204 : search 4 [0xa000,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa000,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaaa,0xcccc,0xf0f0,0xff00],[0x4ccc,0xaaaa,0xf0f0,0xff00],[0xeccc,0xaaaa,0xf0f0,0xff00],[0x50f0,0xaaaa,0xcccc,0xff00],[0x5f00,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_30 (AllBlocked.cons no_3_136 (AllBlocked.cons no_3_265 (AllBlocked.cons no_3_146 (AllBlocked.cons no_3_172 (AllBlocked.nil))))))
private theorem no_4_205 : search 4 [0xa0a0,0xa0a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a0,0xa0a,0xcccc,0xf0f0,0xff00] [[0xecec,0xa0a,0xf0f0,0xff00],[0x5050,0xa0a,0xcccc,0xff00],[0xffa0,0xa0a,0xcccc,0xf0f0],[0xaaaa,0xcccc,0xf0f0,0xff00],[0xfafa,0xa0a0,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_266 (AllBlocked.cons no_3_138 (AllBlocked.cons no_3_472 (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_384 (AllBlocked.nil))))))
private theorem no_4_206 : search 4 [0xa0a0,0x5050,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xa0a0,0x5050,0xaaaa,0xcccc,0xff00] [[0xa0a,0x5050,0xcccc,0xff00],[0xecec,0x5050,0xaaaa,0xff00],[0xffa0,0x5050,0xaaaa,0xcccc],[0xf0f0,0xaaaa,0xcccc,0xff00],[0xfafa,0xa0a0,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_23 (AllBlocked.cons no_3_267 (AllBlocked.cons no_3_474 (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_384 (AllBlocked.nil))))))
private theorem no_4_207 : search 4 [0xa0a0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x4c4c,0xaaaa,0xf0f0,0xff00],[0xecec,0xaaaa,0xf0f0,0xff00],[0x5f00,0xaaaa,0xcccc,0xf0f0],[0xffa0,0xaaaa,0xcccc,0xf0f0],[0xfafa,0xa0a0,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_133 (AllBlocked.cons no_3_270 (AllBlocked.cons no_3_172 (AllBlocked.cons no_3_476 (AllBlocked.cons no_3_384 (AllBlocked.nil))))))
private theorem no_4_208 : search 4 [0xa0a0,0xfafa,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xa0a0,0xfafa,0xaaaa,0xcccc,0xff00] [[0x5a5a,0xaaaa,0xcccc,0xff00],[0xecec,0xfafa,0xaaaa,0xff00],[0xffa0,0xfafa,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_166 (AllBlocked.cons no_3_272 (AllBlocked.cons no_3_479 (AllBlocked.nil))))
private theorem no_4_209 : search 4 [0xa0a0,0xfafa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0a0,0xfafa,0xcccc,0xf0f0,0xff00] [[0x5a5a,0xcccc,0xf0f0,0xff00],[0xecec,0xfafa,0xf0f0,0xff00],[0xffa0,0xfafa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_167 (AllBlocked.cons no_3_274 (AllBlocked.cons no_3_481 (AllBlocked.nil))))
private theorem no_4_210 : search 4 [0xa0a0,0xfafa,0xcccc,0xff00] = false :=
  noNode 3 [0xa0a0,0xfafa,0xcccc,0xff00] [[0x5a5a,0xcccc,0xff00],[0x5a5a,0xfafa,0xcccc,0xff00],[0x5a5a,0xa0a0,0xcccc,0xff00],[0x2020,0xfafa,0xcccc,0xff00],[0x4c4c,0xa0a0,0xfafa,0xff00],[0xecec,0xfafa,0xff00],[0xecec,0xfafa,0xcccc,0xff00],[0xecec,0xa0a0,0xfafa,0xff00],[0xa0,0xfafa,0xcccc,0xff00],[0x5f00,0xa0a0,0xfafa,0xcccc],[0xffa0,0xfafa,0xcccc],[0xffa0,0xfafa,0xcccc,0xff00],[0xffa0,0xa0a0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_168 (AllBlocked.cons no_3_169 (AllBlocked.cons no_3_165 (AllBlocked.cons no_3_61 (AllBlocked.cons no_3_132 (AllBlocked.cons no_3_275 (AllBlocked.cons no_3_273 (AllBlocked.cons no_3_269 (AllBlocked.cons no_3_1 (AllBlocked.cons no_3_171 (AllBlocked.cons no_3_480 (AllBlocked.cons no_3_482 (AllBlocked.cons no_3_475 (AllBlocked.nil))))))))))))))
private theorem no_4_211 : search 4 [0xa0aa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0aa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x5f00,0xaaaa,0xcccc,0xf0f0],[0x5500,0xa0aa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_172 (AllBlocked.cons no_3_151 (AllBlocked.nil)))
private theorem no_4_212 : search 4 [0xa0f0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa0f0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x5f00,0xaaaa,0xcccc,0xf0f0],[0xf00,0xa0f0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_172 (AllBlocked.cons no_3_47 (AllBlocked.nil)))
private theorem no_4_213 : search 4 [0xa2a2,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa2a2,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x4c4c,0xaaaa,0xf0f0,0xff00],[0x4444,0xa2a2,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_133 (AllBlocked.cons no_3_121 (AllBlocked.nil)))
private theorem no_4_214 : search 4 [0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xecec,0xaaaa,0xf0f0,0xff00],[0xf8f8,0xaaaa,0xcccc,0xff00],[0x5700,0xaaaa,0xcccc,0xf0f0],[0xffa8,0xaaaa,0xcccc,0xf0f0],[0xeeee,0xa8a8,0xf0f0,0xff00],[0xfafa,0xa8a8,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_270 (AllBlocked.cons no_3_347 (AllBlocked.cons no_3_162 (AllBlocked.cons no_3_483 (AllBlocked.cons no_3_308 (AllBlocked.cons no_3_385 (AllBlocked.nil)))))))
private theorem no_4_215 : search 4 [0xaa00,0xaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa00,0xaa,0xcccc,0xf0f0,0xff00] [[0xeecc,0xaa,0xf0f0,0xff00],[0xfaf0,0xaa,0xcccc,0xff00],[0x5500,0xaa,0xcccc,0xf0f0],[0xaaaa,0xcccc,0xf0f0,0xff00],[0xffaa,0xaa00,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_290 (AllBlocked.cons no_3_368 (AllBlocked.cons no_3_149 (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_488 (AllBlocked.nil))))))
private theorem no_4_216 : search 4 [0xaa00,0x5500,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xaa00,0x5500,0xaaaa,0xcccc,0xf0f0] [[0xaa,0x5500,0xcccc,0xf0f0],[0xeecc,0x5500,0xaaaa,0xf0f0],[0xfaf0,0x5500,0xaaaa,0xcccc],[0xff00,0xaaaa,0xcccc,0xf0f0],[0xffaa,0xaa00,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_2 (AllBlocked.cons no_3_292 (AllBlocked.cons no_3_370 (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_488 (AllBlocked.nil))))))
private theorem no_4_217 : search 4 [0xaa00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x44cc,0xaaaa,0xf0f0,0xff00],[0xeecc,0xaaaa,0xf0f0,0xff00],[0x50f0,0xaaaa,0xcccc,0xff00],[0xfaf0,0xaaaa,0xcccc,0xff00],[0xffaa,0xaa00,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_128 (AllBlocked.cons no_3_294 (AllBlocked.cons no_3_146 (AllBlocked.cons no_3_372 (AllBlocked.cons no_3_488 (AllBlocked.nil))))))
private theorem no_4_218 : search 4 [0xaa00,0xffaa,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xaa00,0xffaa,0xaaaa,0xcccc,0xf0f0] [[0x55aa,0xaaaa,0xcccc,0xf0f0],[0xeecc,0xffaa,0xaaaa,0xf0f0],[0xfaf0,0xffaa,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_158 (AllBlocked.cons no_3_297 (AllBlocked.cons no_3_375 (AllBlocked.nil))))
private theorem no_4_219 : search 4 [0xaa00,0xffaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xaa00,0xffaa,0xcccc,0xf0f0] [[0x55aa,0xcccc,0xf0f0],[0x55aa,0xffaa,0xcccc,0xf0f0],[0x55aa,0xaa00,0xcccc,0xf0f0],[0x2200,0xffaa,0xcccc,0xf0f0],[0x44cc,0xaa00,0xffaa,0xf0f0],[0xeecc,0xffaa,0xf0f0],[0xeecc,0xffaa,0xcccc,0xf0f0],[0xeecc,0xaa00,0xffaa,0xf0f0],[0xa00,0xffaa,0xcccc,0xf0f0],[0x50f0,0xaa00,0xffaa,0xcccc],[0xfaf0,0xffaa,0xcccc],[0xfaf0,0xffaa,0xcccc,0xf0f0],[0xfaf0,0xaa00,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_159 (AllBlocked.cons no_3_161 (AllBlocked.cons no_3_157 (AllBlocked.cons no_3_62 (AllBlocked.cons no_3_127 (AllBlocked.cons no_3_299 (AllBlocked.cons no_3_298 (AllBlocked.cons no_3_293 (AllBlocked.cons no_3_22 (AllBlocked.cons no_3_145 (AllBlocked.cons no_3_376 (AllBlocked.cons no_3_377 (AllBlocked.cons no_3_371 (AllBlocked.nil))))))))))))))
private theorem no_4_220 : search 4 [0xaa00,0xffaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa00,0xffaa,0xcccc,0xf0f0,0xff00] [[0x55aa,0xcccc,0xf0f0,0xff00],[0xeecc,0xffaa,0xf0f0,0xff00],[0xfaf0,0xffaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_160 (AllBlocked.cons no_3_300 (AllBlocked.cons no_3_378 (AllBlocked.nil))))
private theorem no_4_221 : search 4 [0xaa0a,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa0a,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x50f0,0xaaaa,0xcccc,0xff00],[0x5050,0xaa0a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_146 (AllBlocked.cons no_3_140 (AllBlocked.nil)))
private theorem no_4_222 : search 4 [0xaa22,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa22,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x44cc,0xaaaa,0xf0f0,0xff00],[0x4444,0xaa22,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_128 (AllBlocked.cons no_3_122 (AllBlocked.nil)))
private theorem no_4_223 : search 4 [0xaa88,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaa88,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xeecc,0xaaaa,0xf0f0,0xff00],[0x5070,0xaaaa,0xcccc,0xff00],[0xfaf8,0xaaaa,0xcccc,0xff00],[0xff88,0xaaaa,0xcccc,0xf0f0],[0xeeee,0xaa88,0xf0f0,0xff00],[0xffaa,0xaa88,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_294 (AllBlocked.cons no_3_143 (AllBlocked.cons no_3_379 (AllBlocked.cons no_3_465 (AllBlocked.cons no_3_309 (AllBlocked.cons no_3_489 (AllBlocked.nil)))))))
private theorem no_4_224 : search 4 [0xaaa0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaaa0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x444c,0xaaaa,0xf0f0,0xff00],[0xeeec,0xaaaa,0xf0f0,0xff00],[0xfaf0,0xaaaa,0xcccc,0xff00],[0xffa0,0xaaaa,0xcccc,0xf0f0],[0xfafa,0xaaa0,0xcccc,0xff00],[0xffaa,0xaaa0,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_125 (AllBlocked.cons no_3_302 (AllBlocked.cons no_3_372 (AllBlocked.cons no_3_476 (AllBlocked.cons no_3_386 (AllBlocked.cons no_3_490 (AllBlocked.nil)))))))
private theorem no_4_225 : search 4 [0xaaee,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaaee,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_226 : search 4 [0xaafa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaafa,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_227 : search 4 [0xaeae,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaeae,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_228 : search 4 [0xaf00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xaf00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x50f0,0xaaaa,0xcccc,0xff00],[0xf0,0xaf00,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_146 (AllBlocked.cons no_3_14 (AllBlocked.nil)))
private theorem no_4_229 : search 4 [0xafaa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xafaa,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_230 : search 4 [0xb0b0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xb0b0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x4c4c,0xaaaa,0xf0f0,0xff00],[0xc0c,0xb0b0,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_133 (AllBlocked.cons no_3_36 (AllBlocked.nil)))
private theorem no_4_231 : search 4 [0xbaba,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xbaba,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_232 : search 4 [0xbb00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xbb00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x44cc,0xaaaa,0xf0f0,0xff00],[0xcc,0xbb00,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_128 (AllBlocked.cons no_3_9 (AllBlocked.nil)))
private theorem no_4_233 : search 4 [0xbbaa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xbbaa,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_234 : search 4 [0xc000,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc000,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xccc,0xaaaa,0xf0f0,0xff00],[0x30f0,0xaaaa,0xcccc,0xff00],[0x3f00,0xaaaa,0xcccc,0xf0f0],[0x2aaa,0xcccc,0xf0f0,0xff00],[0xeaaa,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_42 (AllBlocked.cons no_3_88 (AllBlocked.cons no_3_114 (AllBlocked.cons no_3_79 (AllBlocked.cons no_3_253 (AllBlocked.nil))))))
private theorem no_4_235 : search 4 [0xc0c0,0xc0c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c0,0xc0c,0xaaaa,0xf0f0,0xff00] [[0x3030,0xc0c,0xaaaa,0xff00],[0xffc0,0xc0c,0xaaaa,0xf0f0],[0xcccc,0xaaaa,0xf0f0,0xff00],[0xfcfc,0xc0c0,0xaaaa,0xff00],[0xeaea,0xc0c,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_81 (AllBlocked.cons no_3_507 (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_433 (AllBlocked.cons no_3_254 (AllBlocked.nil))))))
private theorem no_4_236 : search 4 [0xc0c0,0x3030,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xc0c0,0x3030,0xaaaa,0xcccc,0xff00] [[0xc0c,0x3030,0xaaaa,0xff00],[0xffc0,0x3030,0xaaaa,0xcccc],[0xf0f0,0xaaaa,0xcccc,0xff00],[0xfcfc,0xc0c0,0xaaaa,0xff00],[0xeaea,0x3030,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_35 (AllBlocked.cons no_3_509 (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_433 (AllBlocked.cons no_3_255 (AllBlocked.nil))))))
private theorem no_4_237 : search 4 [0xc0c0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x3f00,0xaaaa,0xcccc,0xf0f0],[0xffc0,0xaaaa,0xcccc,0xf0f0],[0x2a2a,0xcccc,0xf0f0,0xff00],[0xeaea,0xcccc,0xf0f0,0xff00],[0xfcfc,0xc0c0,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_114 (AllBlocked.cons no_3_510 (AllBlocked.cons no_3_76 (AllBlocked.cons no_3_258 (AllBlocked.cons no_3_433 (AllBlocked.nil))))))
private theorem no_4_238 : search 4 [0xc0c0,0xfcfc,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xc0c0,0xfcfc,0xaaaa,0xcccc,0xff00] [[0x3c3c,0xaaaa,0xcccc,0xff00],[0xffc0,0xfcfc,0xaaaa,0xcccc],[0xeaea,0xfcfc,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_108 (AllBlocked.cons no_3_514 (AllBlocked.cons no_3_261 (AllBlocked.nil))))
private theorem no_4_239 : search 4 [0xc0c0,0xfcfc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0c0,0xfcfc,0xaaaa,0xf0f0,0xff00] [[0x3c3c,0xaaaa,0xf0f0,0xff00],[0xffc0,0xfcfc,0xaaaa,0xf0f0],[0xeaea,0xfcfc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_109 (AllBlocked.cons no_3_515 (AllBlocked.cons no_3_262 (AllBlocked.nil))))
private theorem no_4_240 : search 4 [0xc0c0,0xfcfc,0xaaaa,0xff00] = false :=
  noNode 3 [0xc0c0,0xfcfc,0xaaaa,0xff00] [[0x3c3c,0xaaaa,0xff00],[0x3c3c,0xfcfc,0xaaaa,0xff00],[0x3c3c,0xc0c0,0xaaaa,0xff00],[0xc0,0xfcfc,0xaaaa,0xff00],[0x3f00,0xc0c0,0xfcfc,0xaaaa],[0xffc0,0xfcfc,0xaaaa],[0xffc0,0xfcfc,0xaaaa,0xff00],[0xffc0,0xc0c0,0xfcfc,0xaaaa],[0x2a2a,0xc0c0,0xfcfc,0xff00],[0x4040,0xfcfc,0xaaaa,0xff00],[0xeaea,0xfcfc,0xff00],[0xeaea,0xc0c0,0xfcfc,0xff00],[0xeaea,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_110 (AllBlocked.cons no_3_112 (AllBlocked.cons no_3_111 (AllBlocked.cons no_3_7 (AllBlocked.cons no_3_115 (AllBlocked.cons no_3_513 (AllBlocked.cons no_3_516 (AllBlocked.cons no_3_511 (AllBlocked.cons no_3_75 (AllBlocked.cons no_3_118 (AllBlocked.cons no_3_263 (AllBlocked.cons no_3_257 (AllBlocked.cons no_3_259 (AllBlocked.nil))))))))))))))
private theorem no_4_241 : search 4 [0xc0cc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0cc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x3f00,0xaaaa,0xcccc,0xf0f0],[0x3300,0xc0cc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_114 (AllBlocked.cons no_3_94 (AllBlocked.nil)))
private theorem no_4_242 : search 4 [0xc0f0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc0f0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x3f00,0xaaaa,0xcccc,0xf0f0],[0xf00,0xc0f0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_114 (AllBlocked.cons no_3_48 (AllBlocked.nil)))
private theorem no_4_243 : search 4 [0xc4c4,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc4c4,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x2a2a,0xcccc,0xf0f0,0xff00],[0x2222,0xc4c4,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_76 (AllBlocked.cons no_3_64 (AllBlocked.nil)))
private theorem no_4_244 : search 4 [0xc8c8,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xc8c8,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xf8f8,0xaaaa,0xcccc,0xff00],[0x3700,0xaaaa,0xcccc,0xf0f0],[0xffc8,0xaaaa,0xcccc,0xf0f0],[0xeaea,0xcccc,0xf0f0,0xff00],[0xeeee,0xc8c8,0xf0f0,0xff00],[0xfcfc,0xc8c8,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_347 (AllBlocked.cons no_3_105 (AllBlocked.cons no_3_518 (AllBlocked.cons no_3_258 (AllBlocked.cons no_3_310 (AllBlocked.cons no_3_434 (AllBlocked.nil)))))))
private theorem no_4_245 : search 4 [0xcc00,0xcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc00,0xcc,0xaaaa,0xf0f0,0xff00] [[0xfcf0,0xcc,0xaaaa,0xff00],[0x3300,0xcc,0xaaaa,0xf0f0],[0xcccc,0xaaaa,0xf0f0,0xff00],[0xffcc,0xcc00,0xaaaa,0xf0f0],[0xeeaa,0xcc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_417 (AllBlocked.cons no_3_92 (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_523 (AllBlocked.cons no_3_279 (AllBlocked.nil))))))
private theorem no_4_246 : search 4 [0xcc00,0x3300,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xcc00,0x3300,0xaaaa,0xcccc,0xf0f0] [[0xcc,0x3300,0xaaaa,0xf0f0],[0xfcf0,0x3300,0xaaaa,0xcccc],[0xff00,0xaaaa,0xcccc,0xf0f0],[0xffcc,0xcc00,0xaaaa,0xf0f0],[0xeeaa,0x3300,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_8 (AllBlocked.cons no_3_419 (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_523 (AllBlocked.cons no_3_281 (AllBlocked.nil))))))
private theorem no_4_247 : search 4 [0xcc00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x30f0,0xaaaa,0xcccc,0xff00],[0xfcf0,0xaaaa,0xcccc,0xff00],[0x22aa,0xcccc,0xf0f0,0xff00],[0xeeaa,0xcccc,0xf0f0,0xff00],[0xffcc,0xcc00,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_88 (AllBlocked.cons no_3_420 (AllBlocked.cons no_3_71 (AllBlocked.cons no_3_283 (AllBlocked.cons no_3_523 (AllBlocked.nil))))))
private theorem no_4_248 : search 4 [0xcc00,0xffcc,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xcc00,0xffcc,0xaaaa,0xcccc,0xf0f0] [[0x33cc,0xaaaa,0xcccc,0xf0f0],[0xfcf0,0xffcc,0xaaaa,0xcccc],[0xeeaa,0xffcc,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_100 (AllBlocked.cons no_3_424 (AllBlocked.cons no_3_287 (AllBlocked.nil))))
private theorem no_4_249 : search 4 [0xcc00,0xffcc,0xaaaa,0xf0f0] = false :=
  noNode 3 [0xcc00,0xffcc,0xaaaa,0xf0f0] [[0x33cc,0xaaaa,0xf0f0],[0x33cc,0xffcc,0xaaaa,0xf0f0],[0x33cc,0xcc00,0xaaaa,0xf0f0],[0xc00,0xffcc,0xaaaa,0xf0f0],[0x30f0,0xcc00,0xffcc,0xaaaa],[0xfcf0,0xffcc,0xaaaa],[0xfcf0,0xffcc,0xaaaa,0xf0f0],[0xfcf0,0xcc00,0xffcc,0xaaaa],[0x22aa,0xcc00,0xffcc,0xf0f0],[0x4400,0xffcc,0xaaaa,0xf0f0],[0xeeaa,0xffcc,0xf0f0],[0xeeaa,0xcc00,0xffcc,0xf0f0],[0xeeaa,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_101 (AllBlocked.cons no_3_104 (AllBlocked.cons no_3_103 (AllBlocked.cons no_3_34 (AllBlocked.cons no_3_89 (AllBlocked.cons no_3_423 (AllBlocked.cons no_3_425 (AllBlocked.cons no_3_421 (AllBlocked.cons no_3_70 (AllBlocked.cons no_3_119 (AllBlocked.cons no_3_288 (AllBlocked.cons no_3_282 (AllBlocked.cons no_3_285 (AllBlocked.nil))))))))))))))
private theorem no_4_250 : search 4 [0xcc00,0xffcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc00,0xffcc,0xaaaa,0xf0f0,0xff00] [[0x33cc,0xaaaa,0xf0f0,0xff00],[0xfcf0,0xffcc,0xaaaa,0xff00],[0xeeaa,0xffcc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_102 (AllBlocked.cons no_3_426 (AllBlocked.cons no_3_289 (AllBlocked.nil))))
private theorem no_4_251 : search 4 [0xcc0c,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc0c,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x30f0,0xaaaa,0xcccc,0xff00],[0x3030,0xcc0c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_88 (AllBlocked.cons no_3_83 (AllBlocked.nil)))
private theorem no_4_252 : search 4 [0xcc44,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc44,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x22aa,0xcccc,0xf0f0,0xff00],[0x2222,0xcc44,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_71 (AllBlocked.cons no_3_65 (AllBlocked.nil)))
private theorem no_4_253 : search 4 [0xcc88,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xcc88,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x3070,0xaaaa,0xcccc,0xff00],[0xfcf8,0xaaaa,0xcccc,0xff00],[0xff88,0xaaaa,0xcccc,0xf0f0],[0xeeaa,0xcccc,0xf0f0,0xff00],[0xeeee,0xcc88,0xf0f0,0xff00],[0xffcc,0xcc88,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_86 (AllBlocked.cons no_3_428 (AllBlocked.cons no_3_465 (AllBlocked.cons no_3_283 (AllBlocked.cons no_3_311 (AllBlocked.cons no_3_524 (AllBlocked.nil)))))))
private theorem no_4_254 : search 4 [0xccc0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xccc0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfcf0,0xaaaa,0xcccc,0xff00],[0xffc0,0xaaaa,0xcccc,0xf0f0],[0x222a,0xcccc,0xf0f0,0xff00],[0xeeea,0xcccc,0xf0f0,0xff00],[0xfcfc,0xccc0,0xaaaa,0xff00],[0xffcc,0xccc0,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_420 (AllBlocked.cons no_3_510 (AllBlocked.cons no_3_68 (AllBlocked.cons no_3_301 (AllBlocked.cons no_3_435 (AllBlocked.cons no_3_525 (AllBlocked.nil)))))))
private theorem no_4_255 : search 4 [0xccee,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xccee,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_256 : search 4 [0xccfc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xccfc,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_257 : search 4 [0xcece,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xcece,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_258 : search 4 [0xcf00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xcf00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x30f0,0xaaaa,0xcccc,0xff00],[0xf0,0xcf00,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_88 (AllBlocked.cons no_3_15 (AllBlocked.nil)))
private theorem no_4_259 : search 4 [0xcfcc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xcfcc,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_260 : search 4 [0xd0d0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xd0d0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x2a2a,0xcccc,0xf0f0,0xff00],[0xa0a,0xd0d0,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_76 (AllBlocked.cons no_3_24 (AllBlocked.nil)))
private theorem no_4_261 : search 4 [0xdcdc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xdcdc,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_262 : search 4 [0xdd00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xdd00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x22aa,0xcccc,0xf0f0,0xff00],[0xaa,0xdd00,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_71 (AllBlocked.cons no_3_3 (AllBlocked.nil)))
private theorem no_4_263 : search 4 [0xddcc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xddcc,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_264 : search 4 [0xe0e0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xe0e0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x1f00,0xaaaa,0xcccc,0xf0f0],[0xffe0,0xaaaa,0xcccc,0xf0f0],[0xeaea,0xcccc,0xf0f0,0xff00],[0xfafa,0xe0e0,0xcccc,0xff00],[0xecec,0xaaaa,0xf0f0,0xff00],[0xfcfc,0xe0e0,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_60 (AllBlocked.cons no_3_542 (AllBlocked.cons no_3_258 (AllBlocked.cons no_3_387 (AllBlocked.cons no_3_270 (AllBlocked.cons no_3_436 (AllBlocked.nil)))))))
private theorem no_4_265 : search 4 [0xeaea,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeaea,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfcfc,0xeaea,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_437 (AllBlocked.nil))
private theorem no_4_266 : search 4 [0xeaea,0xc0c0,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeaea,0xc0c0,0xcccc,0xf0f0,0xff00] [[0x2a2a,0xcccc,0xf0f0,0xff00],[0xc0c,0xeaea,0xf0f0,0xff00],[0x3030,0xeaea,0xcccc,0xff00],[0x3f00,0xeaea,0xcccc,0xf0f0],[0xffc0,0xeaea,0xcccc,0xf0f0],[0xfcfc,0xeaea,0xc0c0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_76 (AllBlocked.cons no_3_37 (AllBlocked.cons no_3_84 (AllBlocked.cons no_3_116 (AllBlocked.cons no_3_512 (AllBlocked.cons no_3_438 (AllBlocked.nil)))))))
private theorem no_4_267 : search 4 [0xeaea,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeaea,0xcccc,0xf0f0,0xff00] [[0xc0c,0xeaea,0xf0f0,0xff00],[0x3030,0xeaea,0xcccc,0xff00],[0xfcfc,0xeaea,0xff00],[0xfcfc,0xeaea,0xf0f0,0xff00],[0xfcfc,0xeaea,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_37 (AllBlocked.cons no_3_84 (AllBlocked.cons no_3_441 (AllBlocked.cons no_3_440 (AllBlocked.cons no_3_439 (AllBlocked.nil))))))
private theorem no_4_268 : search 4 [0xecec,0xa0a0,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xecec,0xa0a0,0xaaaa,0xf0f0,0xff00] [[0x4c4c,0xaaaa,0xf0f0,0xff00],[0xa0a,0xecec,0xf0f0,0xff00],[0x5050,0xecec,0xaaaa,0xff00],[0x5f00,0xecec,0xaaaa,0xf0f0],[0xffa0,0xecec,0xaaaa,0xf0f0],[0xfafa,0xecec,0xa0a0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_133 (AllBlocked.cons no_3_25 (AllBlocked.cons no_3_141 (AllBlocked.cons no_3_173 (AllBlocked.cons no_3_477 (AllBlocked.cons no_3_388 (AllBlocked.nil)))))))
private theorem no_4_269 : search 4 [0xecec,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xecec,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfafa,0xecec,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_390 (AllBlocked.nil))
private theorem no_4_270 : search 4 [0xecec,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xecec,0xaaaa,0xf0f0,0xff00] [[0xa0a,0xecec,0xf0f0,0xff00],[0x5050,0xecec,0xaaaa,0xff00],[0xfafa,0xecec,0xff00],[0xfafa,0xecec,0xf0f0,0xff00],[0xfafa,0xecec,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_25 (AllBlocked.cons no_3_141 (AllBlocked.cons no_3_392 (AllBlocked.cons no_3_391 (AllBlocked.cons no_3_389 (AllBlocked.nil))))))
private theorem no_4_271 : search 4 [0xee00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xee00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x10f0,0xaaaa,0xcccc,0xff00],[0xfef0,0xaaaa,0xcccc,0xff00],[0xeeaa,0xcccc,0xf0f0,0xff00],[0xffaa,0xee00,0xcccc,0xf0f0],[0xeecc,0xaaaa,0xf0f0,0xff00],[0xffcc,0xee00,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_59 (AllBlocked.cons no_3_455 (AllBlocked.cons no_3_283 (AllBlocked.cons no_3_491 (AllBlocked.cons no_3_294 (AllBlocked.cons no_3_526 (AllBlocked.nil)))))))
private theorem no_4_272 : search 4 [0xeeaa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeaa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xffcc,0xeeaa,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_527 (AllBlocked.nil))
private theorem no_4_273 : search 4 [0xeeaa,0xcc00,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeaa,0xcc00,0xcccc,0xf0f0,0xff00] [[0x22aa,0xcccc,0xf0f0,0xff00],[0xcc,0xeeaa,0xf0f0,0xff00],[0x30f0,0xeeaa,0xcccc,0xff00],[0xfcf0,0xeeaa,0xcccc,0xff00],[0x3300,0xeeaa,0xcccc,0xf0f0],[0xffcc,0xeeaa,0xcc00,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_71 (AllBlocked.cons no_3_10 (AllBlocked.cons no_3_90 (AllBlocked.cons no_3_422 (AllBlocked.cons no_3_95 (AllBlocked.cons no_3_528 (AllBlocked.nil)))))))
private theorem no_4_274 : search 4 [0xeeaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeaa,0xcccc,0xf0f0,0xff00] [[0xcc,0xeeaa,0xf0f0,0xff00],[0x3300,0xeeaa,0xcccc,0xf0f0],[0xffcc,0xeeaa,0xf0f0],[0xffcc,0xeeaa,0xf0f0,0xff00],[0xffcc,0xeeaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_10 (AllBlocked.cons no_3_95 (AllBlocked.cons no_3_530 (AllBlocked.cons no_3_531 (AllBlocked.cons no_3_529 (AllBlocked.nil))))))
private theorem no_4_275 : search 4 [0xeecc,0xaa00,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xeecc,0xaa00,0xaaaa,0xf0f0,0xff00] [[0x44cc,0xaaaa,0xf0f0,0xff00],[0xaa,0xeecc,0xf0f0,0xff00],[0x50f0,0xeecc,0xaaaa,0xff00],[0xfaf0,0xeecc,0xaaaa,0xff00],[0x5500,0xeecc,0xaaaa,0xf0f0],[0xffaa,0xeecc,0xaa00,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_128 (AllBlocked.cons no_3_4 (AllBlocked.cons no_3_147 (AllBlocked.cons no_3_373 (AllBlocked.cons no_3_152 (AllBlocked.cons no_3_492 (AllBlocked.nil)))))))
private theorem no_4_276 : search 4 [0xeecc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeecc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xffaa,0xeecc,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_494 (AllBlocked.nil))
private theorem no_4_277 : search 4 [0xeecc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xeecc,0xaaaa,0xf0f0,0xff00] [[0xaa,0xeecc,0xf0f0,0xff00],[0x5500,0xeecc,0xaaaa,0xf0f0],[0xffaa,0xeecc,0xf0f0],[0xffaa,0xeecc,0xf0f0,0xff00],[0xffaa,0xeecc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_4 (AllBlocked.cons no_3_152 (AllBlocked.cons no_3_495 (AllBlocked.cons no_3_496 (AllBlocked.cons no_3_493 (AllBlocked.nil))))))
private theorem no_4_278 : search 4 [0xeeee,0xaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0xaa,0xcccc,0xf0f0,0xff00] [[0x88,0xeeee,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_0 (AllBlocked.nil))
private theorem no_4_279 : search 4 [0xeeee,0xcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0xcc,0xaaaa,0xf0f0,0xff00] [[0x88,0xeeee,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_0 (AllBlocked.nil))
private theorem no_4_280 : search 4 [0xeeee,0xa0a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0xa0a,0xcccc,0xf0f0,0xff00] [[0x808,0xeeee,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_21 (AllBlocked.nil))
private theorem no_4_281 : search 4 [0xeeee,0xc0c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0xc0c,0xaaaa,0xf0f0,0xff00] [[0x808,0xeeee,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_21 (AllBlocked.nil))
private theorem no_4_282 : search 4 [0xeeee,0x2222,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0x2222,0xaaaa,0xf0f0,0xff00] [[0xcccc,0xaaaa,0xf0f0,0xff00],[0x8888,0xeeee,0xf0f0,0xff00],[0x4444,0x2222,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_194 (AllBlocked.cons no_3_120 (AllBlocked.nil))))
private theorem no_4_283 : search 4 [0xeeee,0x4444,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0x4444,0xcccc,0xf0f0,0xff00] [[0xaaaa,0xcccc,0xf0f0,0xff00],[0x8888,0xeeee,0xf0f0,0xff00],[0x2222,0x4444,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_194 (AllBlocked.cons no_3_63 (AllBlocked.nil))))
private theorem no_4_284 : search 4 [0xeeee,0x8888,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0x8888,0xaaaa,0xf0f0,0xff00] [[0x6666,0xaaaa,0xf0f0,0xff00],[0xf8f8,0xeeee,0xaaaa,0xff00],[0xff88,0xeeee,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_178 (AllBlocked.cons no_3_349 (AllBlocked.cons no_3_467 (AllBlocked.nil))))
private theorem no_4_285 : search 4 [0xeeee,0x8888,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0x8888,0xcccc,0xf0f0,0xff00] [[0x6666,0xcccc,0xf0f0,0xff00],[0xf8f8,0xeeee,0xcccc,0xff00],[0xff88,0xeeee,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_179 (AllBlocked.cons no_3_350 (AllBlocked.cons no_3_468 (AllBlocked.nil))))
private theorem no_4_286 : search 4 [0xeeee,0x8888,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0x8888,0xf0f0,0xff00] [[0x6666,0xf0f0,0xff00],[0x6666,0xeeee,0xf0f0,0xff00],[0x6666,0x8888,0xf0f0,0xff00],[0x808,0xeeee,0xf0f0,0xff00],[0x7070,0xeeee,0x8888,0xff00],[0xf8f8,0xeeee,0xff00],[0xf8f8,0xeeee,0xf0f0,0xff00],[0xf8f8,0xeeee,0x8888,0xff00],[0x88,0xeeee,0xf0f0,0xff00],[0x7700,0xeeee,0x8888,0xf0f0],[0xff88,0xeeee,0xf0f0],[0xff88,0xeeee,0xf0f0,0xff00],[0xff88,0xeeee,0x8888,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_181 (AllBlocked.cons no_3_180 (AllBlocked.cons no_3_177 (AllBlocked.cons no_3_21 (AllBlocked.cons no_3_185 (AllBlocked.cons no_3_352 (AllBlocked.cons no_3_351 (AllBlocked.cons no_3_348 (AllBlocked.cons no_3_0 (AllBlocked.cons no_3_191 (AllBlocked.cons no_3_469 (AllBlocked.cons no_3_470 (AllBlocked.cons no_3_466 (AllBlocked.nil))))))))))))))
private theorem no_4_287 : search 4 [0xeeee,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x8888,0xeeee,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_194 (AllBlocked.nil))
private theorem no_4_288 : search 4 [0xeeee,0xfafa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0xfafa,0xcccc,0xf0f0,0xff00] [[0xeaea,0xcccc,0xf0f0,0xff00],[0xe0e0,0xfafa,0xcccc,0xff00],[0xc8c8,0xeeee,0xf0f0,0xff00],[0xfcfc,0xeeee,0xfafa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_258 (AllBlocked.cons no_3_251 (AllBlocked.cons no_3_231 (AllBlocked.cons no_3_442 (AllBlocked.nil)))))
private theorem no_4_289 : search 4 [0xeeee,0xfcfc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0xfcfc,0xaaaa,0xf0f0,0xff00] [[0xecec,0xaaaa,0xf0f0,0xff00],[0xe0e0,0xfcfc,0xaaaa,0xff00],[0xa8a8,0xeeee,0xf0f0,0xff00],[0xfafa,0xeeee,0xfcfc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_270 (AllBlocked.cons no_3_252 (AllBlocked.cons no_3_206 (AllBlocked.cons no_3_393 (AllBlocked.nil)))))
private theorem no_4_290 : search 4 [0xeeee,0xffaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0xffaa,0xcccc,0xf0f0,0xff00] [[0xeeaa,0xcccc,0xf0f0,0xff00],[0xee00,0xffaa,0xcccc,0xf0f0],[0xcc88,0xeeee,0xf0f0,0xff00],[0xffcc,0xeeee,0xffaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_283 (AllBlocked.cons no_3_277 (AllBlocked.cons no_3_237 (AllBlocked.cons no_3_532 (AllBlocked.nil)))))
private theorem no_4_291 : search 4 [0xeeee,0xffcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xeeee,0xffcc,0xaaaa,0xf0f0,0xff00] [[0xeecc,0xaaaa,0xf0f0,0xff00],[0xee00,0xffcc,0xaaaa,0xf0f0],[0xaa88,0xeeee,0xf0f0,0xff00],[0xffaa,0xeeee,0xffcc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_294 (AllBlocked.cons no_3_278 (AllBlocked.cons no_3_212 (AllBlocked.cons no_3_497 (AllBlocked.nil)))))
private theorem no_4_292 : search 4 [0xf000,0xf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf000,0xf0,0xaaaa,0xcccc,0xff00] [[0xf00,0xf0,0xaaaa,0xcccc],[0xf0f0,0xaaaa,0xcccc,0xff00],[0xfff0,0xf000,0xaaaa,0xcccc],[0xfaaa,0xf0,0xcccc,0xff00],[0xfccc,0xf0,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_46 (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_547 (AllBlocked.cons no_3_356 (AllBlocked.cons no_3_405 (AllBlocked.nil))))))
private theorem no_4_293 : search 4 [0xf000,0xf00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf000,0xf00,0xaaaa,0xcccc,0xf0f0] [[0xf0,0xf00,0xaaaa,0xcccc],[0xff00,0xaaaa,0xcccc,0xf0f0],[0xfff0,0xf000,0xaaaa,0xcccc],[0xfaaa,0xf00,0xcccc,0xf0f0],[0xfccc,0xf00,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_13 (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_547 (AllBlocked.cons no_3_358 (AllBlocked.cons no_3_407 (AllBlocked.nil))))))
private theorem no_4_294 : search 4 [0xf000,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf000,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaaa,0xcccc,0xf0f0,0xff00],[0xfaaa,0xcccc,0xf0f0,0xff00],[0xccc,0xaaaa,0xf0f0,0xff00],[0xfccc,0xaaaa,0xf0f0,0xff00],[0xfff0,0xf000,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_30 (AllBlocked.cons no_3_359 (AllBlocked.cons no_3_42 (AllBlocked.cons no_3_408 (AllBlocked.cons no_3_547 (AllBlocked.nil))))))
private theorem no_4_295 : search 4 [0xf000,0xfff0,0xaaaa,0xcccc] = false :=
  noNode 3 [0xf000,0xfff0,0xaaaa,0xcccc] [[0xff0,0xaaaa,0xcccc],[0xff0,0xfff0,0xaaaa,0xcccc],[0xff0,0xf000,0xaaaa,0xcccc],[0xaaa,0xf000,0xfff0,0xcccc],[0x5000,0xfff0,0xaaaa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xfaaa,0xf000,0xfff0,0xcccc],[0xfaaa,0xfff0,0xaaaa,0xcccc],[0xccc,0xf000,0xfff0,0xaaaa],[0x3000,0xfff0,0xaaaa,0xcccc],[0xfccc,0xfff0,0xaaaa],[0xfccc,0xf000,0xfff0,0xaaaa],[0xfccc,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_54 (AllBlocked.cons no_3_58 (AllBlocked.cons no_3_57 (AllBlocked.cons no_3_31 (AllBlocked.cons no_3_137 (AllBlocked.cons no_3_363 (AllBlocked.cons no_3_360 (AllBlocked.cons no_3_362 (AllBlocked.cons no_3_43 (AllBlocked.cons no_3_80 (AllBlocked.cons no_3_411 (AllBlocked.cons no_3_409 (AllBlocked.cons no_3_412 (AllBlocked.nil))))))))))))))
private theorem no_4_296 : search 4 [0xf000,0xfff0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xf000,0xfff0,0xaaaa,0xcccc,0xf0f0] [[0xff0,0xaaaa,0xcccc,0xf0f0],[0xfaaa,0xfff0,0xcccc,0xf0f0],[0xfccc,0xfff0,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_55 (AllBlocked.cons no_3_364 (AllBlocked.cons no_3_413 (AllBlocked.nil))))
private theorem no_4_297 : search 4 [0xf000,0xfff0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf000,0xfff0,0xaaaa,0xcccc,0xff00] [[0xff0,0xaaaa,0xcccc,0xff00],[0xfaaa,0xfff0,0xcccc,0xff00],[0xfccc,0xfff0,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_56 (AllBlocked.cons no_3_365 (AllBlocked.cons no_3_414 (AllBlocked.nil))))
private theorem no_4_298 : search 4 [0xf030,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf030,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xccc,0xaaaa,0xf0f0,0xff00],[0xc0c,0xf030,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_42 (AllBlocked.cons no_3_38 (AllBlocked.nil)))
private theorem no_4_299 : search 4 [0xf050,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf050,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaaa,0xcccc,0xf0f0,0xff00],[0xa0a,0xf050,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_30 (AllBlocked.cons no_3_26 (AllBlocked.nil)))
private theorem no_4_300 : search 4 [0xf0a0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf0a0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xffa0,0xaaaa,0xcccc,0xf0f0],[0xfaaa,0xcccc,0xf0f0,0xff00],[0xfafa,0xf0a0,0xcccc,0xff00],[0xc4c,0xaaaa,0xf0f0,0xff00],[0xfcec,0xaaaa,0xf0f0,0xff00],[0xfff0,0xf0a0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_476 (AllBlocked.cons no_3_359 (AllBlocked.cons no_3_394 (AllBlocked.cons no_3_40 (AllBlocked.cons no_3_416 (AllBlocked.cons no_3_548 (AllBlocked.nil)))))))
private theorem no_4_301 : search 4 [0xf0c0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf0c0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xffc0,0xaaaa,0xcccc,0xf0f0],[0xa2a,0xcccc,0xf0f0,0xff00],[0xfaea,0xcccc,0xf0f0,0xff00],[0xfccc,0xaaaa,0xf0f0,0xff00],[0xfcfc,0xf0c0,0xaaaa,0xff00],[0xfff0,0xf0c0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_510 (AllBlocked.cons no_3_28 (AllBlocked.cons no_3_367 (AllBlocked.cons no_3_408 (AllBlocked.cons no_3_443 (AllBlocked.cons no_3_549 (AllBlocked.nil)))))))
private theorem no_4_302 : search 4 [0xf0fa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf0fa,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_303 : search 4 [0xf0fc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf0fc,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_304 : search 4 [0xf2f2,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf2f2,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_305 : search 4 [0xf300,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf300,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xccc,0xaaaa,0xf0f0,0xff00],[0xcc,0xf300,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_42 (AllBlocked.cons no_3_11 (AllBlocked.nil)))
private theorem no_4_306 : search 4 [0xf3f0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf3f0,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_307 : search 4 [0xf4f4,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf4f4,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_308 : search 4 [0xf500,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf500,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaaa,0xcccc,0xf0f0,0xff00],[0xaa,0xf500,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_30 (AllBlocked.cons no_3_5 (AllBlocked.nil)))
private theorem no_4_309 : search 4 [0xf5f0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf5f0,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_310 : search 4 [0xf8f8,0x8888,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf8f8,0x8888,0xaaaa,0xcccc,0xff00] [[0x7070,0xaaaa,0xcccc,0xff00],[0x2222,0xf8f8,0xcccc,0xff00],[0x4444,0xf8f8,0xaaaa,0xff00],[0x7700,0xf8f8,0xaaaa,0xcccc],[0xff88,0xf8f8,0xaaaa,0xcccc],[0xeeee,0xf8f8,0x8888,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_184 (AllBlocked.cons no_3_66 (AllBlocked.cons no_3_123 (AllBlocked.cons no_3_192 (AllBlocked.cons no_3_471 (AllBlocked.cons no_3_312 (AllBlocked.nil)))))))
private theorem no_4_311 : search 4 [0xf8f8,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xf8f8,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xeeee,0xf8f8,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_315 (AllBlocked.nil))
private theorem no_4_312 : search 4 [0xf8f8,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xf8f8,0xaaaa,0xcccc,0xff00] [[0x2222,0xf8f8,0xcccc,0xff00],[0x4444,0xf8f8,0xaaaa,0xff00],[0xeeee,0xf8f8,0xff00],[0xeeee,0xf8f8,0xcccc,0xff00],[0xeeee,0xf8f8,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_66 (AllBlocked.cons no_3_123 (AllBlocked.cons no_3_316 (AllBlocked.cons no_3_314 (AllBlocked.cons no_3_313 (AllBlocked.nil))))))
private theorem no_4_313 : search 4 [0xfa00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfa00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfaaa,0xcccc,0xf0f0,0xff00],[0xffaa,0xfa00,0xcccc,0xf0f0],[0x4cc,0xaaaa,0xf0f0,0xff00],[0xfecc,0xaaaa,0xf0f0,0xff00],[0xfaf0,0xaaaa,0xcccc,0xff00],[0xfff0,0xfa00,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_359 (AllBlocked.cons no_3_498 (AllBlocked.cons no_3_20 (AllBlocked.cons no_3_454 (AllBlocked.cons no_3_372 (AllBlocked.cons no_3_550 (AllBlocked.nil)))))))
private theorem no_4_314 : search 4 [0xfaaa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfaaa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfff0,0xfaaa,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_551 (AllBlocked.nil))
private theorem no_4_315 : search 4 [0xfaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfaaa,0xcccc,0xf0f0,0xff00] [[0xf0,0xfaaa,0xcccc,0xff00],[0xf00,0xfaaa,0xcccc,0xf0f0],[0xfff0,0xfaaa,0xcccc],[0xfff0,0xfaaa,0xcccc,0xff00],[0xfff0,0xfaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_16 (AllBlocked.cons no_3_49 (AllBlocked.cons no_3_552 (AllBlocked.cons no_3_554 (AllBlocked.cons no_3_553 (AllBlocked.nil))))))
private theorem no_4_316 : search 4 [0xfaaa,0xf000,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfaaa,0xf000,0xcccc,0xf0f0,0xff00] [[0xaaa,0xcccc,0xf0f0,0xff00],[0xf0,0xfaaa,0xcccc,0xff00],[0xf00,0xfaaa,0xcccc,0xf0f0],[0xccc,0xfaaa,0xf0f0,0xff00],[0xfccc,0xfaaa,0xf0f0,0xff00],[0xfff0,0xfaaa,0xf000,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_30 (AllBlocked.cons no_3_16 (AllBlocked.cons no_3_49 (AllBlocked.cons no_3_44 (AllBlocked.cons no_3_410 (AllBlocked.cons no_3_555 (AllBlocked.nil)))))))
private theorem no_4_317 : search 4 [0xfaf0,0xaa00,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfaf0,0xaa00,0xaaaa,0xcccc,0xff00] [[0x50f0,0xaaaa,0xcccc,0xff00],[0xaa,0xfaf0,0xcccc,0xff00],[0x44cc,0xfaf0,0xaaaa,0xff00],[0xeecc,0xfaf0,0xaaaa,0xff00],[0x5500,0xfaf0,0xaaaa,0xcccc],[0xffaa,0xfaf0,0xaa00,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_146 (AllBlocked.cons no_3_6 (AllBlocked.cons no_3_129 (AllBlocked.cons no_3_295 (AllBlocked.cons no_3_153 (AllBlocked.cons no_3_499 (AllBlocked.nil)))))))
private theorem no_4_318 : search 4 [0xfaf0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfaf0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xffaa,0xfaf0,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_502 (AllBlocked.nil))
private theorem no_4_319 : search 4 [0xfaf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfaf0,0xaaaa,0xcccc,0xff00] [[0xaa,0xfaf0,0xcccc,0xff00],[0x5500,0xfaf0,0xaaaa,0xcccc],[0xffaa,0xfaf0,0xcccc],[0xffaa,0xfaf0,0xcccc,0xff00],[0xffaa,0xfaf0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_6 (AllBlocked.cons no_3_153 (AllBlocked.cons no_3_501 (AllBlocked.cons no_3_503 (AllBlocked.cons no_3_500 (AllBlocked.nil))))))
private theorem no_4_320 : search 4 [0xfafa,0xaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfafa,0xaa,0xcccc,0xf0f0,0xff00] [[0xa0,0xfafa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_1 (AllBlocked.nil))
private theorem no_4_321 : search 4 [0xfafa,0xf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfafa,0xf0,0xaaaa,0xcccc,0xff00] [[0xa0,0xfafa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_1 (AllBlocked.nil))
private theorem no_4_322 : search 4 [0xfafa,0xa0a,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfafa,0xa0a,0xaaaa,0xcccc,0xff00] [[0xf0f0,0xaaaa,0xcccc,0xff00],[0xa0a0,0xfafa,0xcccc,0xff00],[0x5050,0xa0a,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_201 (AllBlocked.cons no_3_138 (AllBlocked.nil))))
private theorem no_4_323 : search 4 [0xfafa,0x2222,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfafa,0x2222,0xcccc,0xf0f0,0xff00] [[0x2020,0xfafa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_61 (AllBlocked.nil))
private theorem no_4_324 : search 4 [0xfafa,0x3030,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfafa,0x3030,0xaaaa,0xcccc,0xff00] [[0x2020,0xfafa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_61 (AllBlocked.nil))
private theorem no_4_325 : search 4 [0xfafa,0x5050,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfafa,0x5050,0xcccc,0xf0f0,0xff00] [[0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0a0,0xfafa,0xcccc,0xff00],[0xa0a,0x5050,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_201 (AllBlocked.cons no_3_23 (AllBlocked.nil))))
private theorem no_4_326 : search 4 [0xfafa,0xa0a0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfafa,0xa0a0,0xaaaa,0xcccc,0xff00] [[0x5a5a,0xaaaa,0xcccc,0xff00],[0xecec,0xfafa,0xaaaa,0xff00],[0xffa0,0xfafa,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_166 (AllBlocked.cons no_3_272 (AllBlocked.cons no_3_479 (AllBlocked.nil))))
private theorem no_4_327 : search 4 [0xfafa,0xa0a0,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfafa,0xa0a0,0xcccc,0xf0f0,0xff00] [[0x5a5a,0xcccc,0xf0f0,0xff00],[0xecec,0xfafa,0xf0f0,0xff00],[0xffa0,0xfafa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_167 (AllBlocked.cons no_3_274 (AllBlocked.cons no_3_481 (AllBlocked.nil))))
private theorem no_4_328 : search 4 [0xfafa,0xa0a0,0xcccc,0xff00] = false :=
  noNode 3 [0xfafa,0xa0a0,0xcccc,0xff00] [[0x5a5a,0xcccc,0xff00],[0x5a5a,0xfafa,0xcccc,0xff00],[0x5a5a,0xa0a0,0xcccc,0xff00],[0x2020,0xfafa,0xcccc,0xff00],[0x4c4c,0xfafa,0xa0a0,0xff00],[0xecec,0xfafa,0xff00],[0xecec,0xfafa,0xcccc,0xff00],[0xecec,0xfafa,0xa0a0,0xff00],[0xa0,0xfafa,0xcccc,0xff00],[0x5f00,0xfafa,0xa0a0,0xcccc],[0xffa0,0xfafa,0xcccc],[0xffa0,0xfafa,0xcccc,0xff00],[0xffa0,0xfafa,0xa0a0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_168 (AllBlocked.cons no_3_169 (AllBlocked.cons no_3_165 (AllBlocked.cons no_3_61 (AllBlocked.cons no_3_134 (AllBlocked.cons no_3_275 (AllBlocked.cons no_3_273 (AllBlocked.cons no_3_271 (AllBlocked.cons no_3_1 (AllBlocked.cons no_3_174 (AllBlocked.cons no_3_480 (AllBlocked.cons no_3_482 (AllBlocked.cons no_3_478 (AllBlocked.nil))))))))))))))
private theorem no_4_329 : search 4 [0xfafa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfafa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xa0a0,0xfafa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_201 (AllBlocked.nil))
private theorem no_4_330 : search 4 [0xfafa,0xeeee,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfafa,0xeeee,0xcccc,0xf0f0,0xff00] [[0xeaea,0xcccc,0xf0f0,0xff00],[0xe0e0,0xfafa,0xcccc,0xff00],[0xc8c8,0xeeee,0xf0f0,0xff00],[0xfcfc,0xfafa,0xeeee,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_258 (AllBlocked.cons no_3_251 (AllBlocked.cons no_3_231 (AllBlocked.cons no_3_444 (AllBlocked.nil)))))
private theorem no_4_331 : search 4 [0xfafa,0xfcfc,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfafa,0xfcfc,0xaaaa,0xcccc,0xff00] [[0xf8f8,0xaaaa,0xcccc,0xff00],[0xa8a8,0xfafa,0xcccc,0xff00],[0xeeee,0xfafa,0xfcfc,0xff00],[0xc8c8,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_347 (AllBlocked.cons no_3_207 (AllBlocked.cons no_3_317 (AllBlocked.cons no_3_232 (AllBlocked.nil)))))
private theorem no_4_332 : search 4 [0xfafa,0xffaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfafa,0xffaa,0xcccc,0xf0f0,0xff00] [[0xfaaa,0xcccc,0xf0f0,0xff00],[0xfa00,0xffaa,0xcccc,0xf0f0],[0xf0a0,0xfafa,0xcccc,0xff00],[0xfff0,0xfafa,0xffaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_359 (AllBlocked.cons no_3_354 (AllBlocked.cons no_3_330 (AllBlocked.cons no_3_556 (AllBlocked.nil)))))
private theorem no_4_333 : search 4 [0xfafa,0xfff0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfafa,0xfff0,0xaaaa,0xcccc,0xff00] [[0xfaf0,0xaaaa,0xcccc,0xff00],[0xfa00,0xfff0,0xaaaa,0xcccc],[0xaaa0,0xfafa,0xcccc,0xff00],[0xffaa,0xfafa,0xfff0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_372 (AllBlocked.cons no_3_355 (AllBlocked.cons no_3_214 (AllBlocked.cons no_3_504 (AllBlocked.nil)))))
private theorem no_4_334 : search 4 [0xfc00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfc00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x2aa,0xcccc,0xf0f0,0xff00],[0xfeaa,0xcccc,0xf0f0,0xff00],[0xfccc,0xaaaa,0xf0f0,0xff00],[0xffcc,0xfc00,0xaaaa,0xf0f0],[0xfcf0,0xaaaa,0xcccc,0xff00],[0xfff0,0xfc00,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_19 (AllBlocked.cons no_3_453 (AllBlocked.cons no_3_408 (AllBlocked.cons no_3_533 (AllBlocked.cons no_3_420 (AllBlocked.cons no_3_557 (AllBlocked.nil)))))))
private theorem no_4_335 : search 4 [0xfccc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfccc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfff0,0xfccc,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_559 (AllBlocked.nil))
private theorem no_4_336 : search 4 [0xfccc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xfccc,0xaaaa,0xf0f0,0xff00] [[0xf0,0xfccc,0xaaaa,0xff00],[0xf00,0xfccc,0xaaaa,0xf0f0],[0xfff0,0xfccc,0xaaaa],[0xfff0,0xfccc,0xaaaa,0xff00],[0xfff0,0xfccc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_17 (AllBlocked.cons no_3_50 (AllBlocked.cons no_3_558 (AllBlocked.cons no_3_561 (AllBlocked.cons no_3_560 (AllBlocked.nil))))))
private theorem no_4_337 : search 4 [0xfccc,0xf000,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xfccc,0xf000,0xaaaa,0xf0f0,0xff00] [[0xccc,0xaaaa,0xf0f0,0xff00],[0xf0,0xfccc,0xaaaa,0xff00],[0xf00,0xfccc,0xaaaa,0xf0f0],[0xaaa,0xfccc,0xf0f0,0xff00],[0xfaaa,0xfccc,0xf0f0,0xff00],[0xfff0,0xfccc,0xf000,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_42 (AllBlocked.cons no_3_17 (AllBlocked.cons no_3_50 (AllBlocked.cons no_3_32 (AllBlocked.cons no_3_361 (AllBlocked.cons no_3_562 (AllBlocked.nil)))))))
private theorem no_4_338 : search 4 [0xfcf0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfcf0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xffcc,0xfcf0,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_536 (AllBlocked.nil))
private theorem no_4_339 : search 4 [0xfcf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfcf0,0xaaaa,0xcccc,0xff00] [[0xcc,0xfcf0,0xaaaa,0xff00],[0x3300,0xfcf0,0xaaaa,0xcccc],[0xffcc,0xfcf0,0xaaaa],[0xffcc,0xfcf0,0xaaaa,0xff00],[0xffcc,0xfcf0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_12 (AllBlocked.cons no_3_96 (AllBlocked.cons no_3_534 (AllBlocked.cons no_3_537 (AllBlocked.cons no_3_535 (AllBlocked.nil))))))
private theorem no_4_340 : search 4 [0xfcf0,0xcc00,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfcf0,0xcc00,0xaaaa,0xcccc,0xff00] [[0x30f0,0xaaaa,0xcccc,0xff00],[0xcc,0xfcf0,0xaaaa,0xff00],[0x3300,0xfcf0,0xaaaa,0xcccc],[0x22aa,0xfcf0,0xcccc,0xff00],[0xeeaa,0xfcf0,0xcccc,0xff00],[0xffcc,0xfcf0,0xcc00,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_88 (AllBlocked.cons no_3_12 (AllBlocked.cons no_3_96 (AllBlocked.cons no_3_72 (AllBlocked.cons no_3_284 (AllBlocked.cons no_3_538 (AllBlocked.nil)))))))
private theorem no_4_341 : search 4 [0xfcfc,0xcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xfcfc,0xcc,0xaaaa,0xf0f0,0xff00] [[0xc0,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_7 (AllBlocked.nil))
private theorem no_4_342 : search 4 [0xfcfc,0xf0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfcfc,0xf0,0xaaaa,0xcccc,0xff00] [[0xc0,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_7 (AllBlocked.nil))
private theorem no_4_343 : search 4 [0xfcfc,0xc0c,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfcfc,0xc0c,0xaaaa,0xcccc,0xff00] [[0xf0f0,0xaaaa,0xcccc,0xff00],[0xc0c0,0xfcfc,0xaaaa,0xff00],[0x3030,0xc0c,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_226 (AllBlocked.cons no_3_81 (AllBlocked.nil))))
private theorem no_4_344 : search 4 [0xfcfc,0x3030,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xfcfc,0x3030,0xaaaa,0xf0f0,0xff00] [[0xcccc,0xaaaa,0xf0f0,0xff00],[0xc0c0,0xfcfc,0xaaaa,0xff00],[0xc0c,0x3030,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_226 (AllBlocked.cons no_3_35 (AllBlocked.nil))))
private theorem no_4_345 : search 4 [0xfcfc,0x4444,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xfcfc,0x4444,0xaaaa,0xf0f0,0xff00] [[0x4040,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_118 (AllBlocked.nil))
private theorem no_4_346 : search 4 [0xfcfc,0x5050,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfcfc,0x5050,0xaaaa,0xcccc,0xff00] [[0x4040,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_118 (AllBlocked.nil))
private theorem no_4_347 : search 4 [0xfcfc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfcfc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xc0c0,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_226 (AllBlocked.nil))
private theorem no_4_348 : search 4 [0xfcfc,0xc0c0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfcfc,0xc0c0,0xaaaa,0xcccc,0xff00] [[0x3c3c,0xaaaa,0xcccc,0xff00],[0xffc0,0xfcfc,0xaaaa,0xcccc],[0xeaea,0xfcfc,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_108 (AllBlocked.cons no_3_514 (AllBlocked.cons no_3_261 (AllBlocked.nil))))
private theorem no_4_349 : search 4 [0xfcfc,0xc0c0,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xfcfc,0xc0c0,0xaaaa,0xf0f0,0xff00] [[0x3c3c,0xaaaa,0xf0f0,0xff00],[0xffc0,0xfcfc,0xaaaa,0xf0f0],[0xeaea,0xfcfc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_109 (AllBlocked.cons no_3_515 (AllBlocked.cons no_3_262 (AllBlocked.nil))))
private theorem no_4_350 : search 4 [0xfcfc,0xc0c0,0xaaaa,0xff00] = false :=
  noNode 3 [0xfcfc,0xc0c0,0xaaaa,0xff00] [[0x3c3c,0xaaaa,0xff00],[0x3c3c,0xfcfc,0xaaaa,0xff00],[0x3c3c,0xc0c0,0xaaaa,0xff00],[0xc0,0xfcfc,0xaaaa,0xff00],[0x3f00,0xfcfc,0xc0c0,0xaaaa],[0xffc0,0xfcfc,0xaaaa],[0xffc0,0xfcfc,0xaaaa,0xff00],[0xffc0,0xfcfc,0xc0c0,0xaaaa],[0x2a2a,0xfcfc,0xc0c0,0xff00],[0x4040,0xfcfc,0xaaaa,0xff00],[0xeaea,0xfcfc,0xff00],[0xeaea,0xfcfc,0xc0c0,0xff00],[0xeaea,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_110 (AllBlocked.cons no_3_112 (AllBlocked.cons no_3_111 (AllBlocked.cons no_3_7 (AllBlocked.cons no_3_117 (AllBlocked.cons no_3_513 (AllBlocked.cons no_3_516 (AllBlocked.cons no_3_517 (AllBlocked.cons no_3_77 (AllBlocked.cons no_3_118 (AllBlocked.cons no_3_263 (AllBlocked.cons no_3_260 (AllBlocked.cons no_3_259 (AllBlocked.nil))))))))))))))
private theorem no_4_351 : search 4 [0xfcfc,0xeeee,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xfcfc,0xeeee,0xaaaa,0xf0f0,0xff00] [[0xecec,0xaaaa,0xf0f0,0xff00],[0xe0e0,0xfcfc,0xaaaa,0xff00],[0xa8a8,0xeeee,0xf0f0,0xff00],[0xfafa,0xfcfc,0xeeee,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_270 (AllBlocked.cons no_3_252 (AllBlocked.cons no_3_206 (AllBlocked.cons no_3_395 (AllBlocked.nil)))))
private theorem no_4_352 : search 4 [0xfcfc,0xfafa,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfcfc,0xfafa,0xaaaa,0xcccc,0xff00] [[0xf8f8,0xaaaa,0xcccc,0xff00],[0xa8a8,0xfafa,0xcccc,0xff00],[0xeeee,0xfcfc,0xfafa,0xff00],[0xc8c8,0xfcfc,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_347 (AllBlocked.cons no_3_207 (AllBlocked.cons no_3_318 (AllBlocked.cons no_3_232 (AllBlocked.nil)))))
private theorem no_4_353 : search 4 [0xfcfc,0xffcc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xfcfc,0xffcc,0xaaaa,0xf0f0,0xff00] [[0xfccc,0xaaaa,0xf0f0,0xff00],[0xfc00,0xffcc,0xaaaa,0xf0f0],[0xf0c0,0xfcfc,0xaaaa,0xff00],[0xfff0,0xfcfc,0xffcc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_408 (AllBlocked.cons no_3_403 (AllBlocked.cons no_3_332 (AllBlocked.cons no_3_563 (AllBlocked.nil)))))
private theorem no_4_354 : search 4 [0xfcfc,0xfff0,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfcfc,0xfff0,0xaaaa,0xcccc,0xff00] [[0xfcf0,0xaaaa,0xcccc,0xff00],[0xfc00,0xfff0,0xaaaa,0xcccc],[0xccc0,0xfcfc,0xaaaa,0xff00],[0xffcc,0xfcfc,0xfff0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_420 (AllBlocked.cons no_3_404 (AllBlocked.cons no_3_239 (AllBlocked.cons no_3_539 (AllBlocked.nil)))))
private theorem no_4_355 : search 4 [0xfefe,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfefe,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfe00,0xaaaa,0xcccc,0xf0f0],[0xfe,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_452 (AllBlocked.cons no_3_18 (AllBlocked.nil)))
private theorem no_4_356 : search 4 [0xff0a,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xff0a,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_357 : search 4 [0xff0c,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xff0c,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_358 : search 4 [0xff22,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xff22,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_359 : search 4 [0xff30,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xff30,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_360 : search 4 [0xff44,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xff44,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_361 : search 4 [0xff50,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xff50,0xaaaa,0xcccc,0xf0f0,0xff00] [] (by decide +kernel) (by decide +kernel)
    (AllBlocked.nil)
private theorem no_4_362 : search 4 [0xff88,0x8888,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xff88,0x8888,0xaaaa,0xcccc,0xf0f0] [[0x7700,0xaaaa,0xcccc,0xf0f0],[0x2222,0xff88,0xcccc,0xf0f0],[0x4444,0xff88,0xaaaa,0xf0f0],[0x7070,0xff88,0xaaaa,0xcccc],[0xf8f8,0xff88,0xaaaa,0xcccc],[0xeeee,0xff88,0x8888,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_190 (AllBlocked.cons no_3_67 (AllBlocked.cons no_3_124 (AllBlocked.cons no_3_186 (AllBlocked.cons no_3_353 (AllBlocked.cons no_3_319 (AllBlocked.nil)))))))
private theorem no_4_363 : search 4 [0xff88,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xff88,0xaaaa,0xcccc,0xf0f0] [[0x2222,0xff88,0xcccc,0xf0f0],[0x4444,0xff88,0xaaaa,0xf0f0],[0xeeee,0xff88,0xf0f0],[0xeeee,0xff88,0xcccc,0xf0f0],[0xeeee,0xff88,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_67 (AllBlocked.cons no_3_124 (AllBlocked.cons no_3_322 (AllBlocked.cons no_3_321 (AllBlocked.cons no_3_320 (AllBlocked.nil))))))
private theorem no_4_364 : search 4 [0xff88,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xff88,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xeeee,0xff88,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_323 (AllBlocked.nil))
private theorem no_4_365 : search 4 [0xffa0,0xa0a0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffa0,0xa0a0,0xaaaa,0xcccc,0xf0f0] [[0x5f00,0xaaaa,0xcccc,0xf0f0],[0xa0a,0xffa0,0xcccc,0xf0f0],[0x4c4c,0xffa0,0xaaaa,0xf0f0],[0xecec,0xffa0,0xaaaa,0xf0f0],[0x5050,0xffa0,0xaaaa,0xcccc],[0xfafa,0xffa0,0xa0a0,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_172 (AllBlocked.cons no_3_27 (AllBlocked.cons no_3_135 (AllBlocked.cons no_3_276 (AllBlocked.cons no_3_142 (AllBlocked.cons no_3_396 (AllBlocked.nil)))))))
private theorem no_4_366 : search 4 [0xffa0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffa0,0xaaaa,0xcccc,0xf0f0] [[0xa0a,0xffa0,0xcccc,0xf0f0],[0x5050,0xffa0,0xaaaa,0xcccc],[0xfafa,0xffa0,0xcccc],[0xfafa,0xffa0,0xcccc,0xf0f0],[0xfafa,0xffa0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_27 (AllBlocked.cons no_3_142 (AllBlocked.cons no_3_398 (AllBlocked.cons no_3_399 (AllBlocked.cons no_3_397 (AllBlocked.nil))))))
private theorem no_4_367 : search 4 [0xffa0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffa0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfafa,0xffa0,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_400 (AllBlocked.nil))
private theorem no_4_368 : search 4 [0xffaa,0xaa,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffaa,0xaa,0xaaaa,0xcccc,0xf0f0] [[0xff00,0xaaaa,0xcccc,0xf0f0],[0xaa00,0xffaa,0xcccc,0xf0f0],[0x5500,0xaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_208 (AllBlocked.cons no_3_149 (AllBlocked.nil))))
private theorem no_4_369 : search 4 [0xffaa,0xa0a,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffaa,0xa0a,0xcccc,0xf0f0,0xff00] [[0xa00,0xffaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_22 (AllBlocked.nil))
private theorem no_4_370 : search 4 [0xffaa,0xf00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffaa,0xf00,0xaaaa,0xcccc,0xf0f0] [[0xa00,0xffaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_22 (AllBlocked.nil))
private theorem no_4_371 : search 4 [0xffaa,0x2222,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffaa,0x2222,0xcccc,0xf0f0,0xff00] [[0x2200,0xffaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_62 (AllBlocked.nil))
private theorem no_4_372 : search 4 [0xffaa,0x3300,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffaa,0x3300,0xaaaa,0xcccc,0xf0f0] [[0x2200,0xffaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_62 (AllBlocked.nil))
private theorem no_4_373 : search 4 [0xffaa,0x5500,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffaa,0x5500,0xcccc,0xf0f0,0xff00] [[0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa00,0xffaa,0xcccc,0xf0f0],[0xaa,0x5500,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_217 (AllBlocked.cons no_3_208 (AllBlocked.cons no_3_2 (AllBlocked.nil))))
private theorem no_4_374 : search 4 [0xffaa,0xaa00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffaa,0xaa00,0xaaaa,0xcccc,0xf0f0] [[0x55aa,0xaaaa,0xcccc,0xf0f0],[0xeecc,0xffaa,0xaaaa,0xf0f0],[0xfaf0,0xffaa,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_158 (AllBlocked.cons no_3_297 (AllBlocked.cons no_3_375 (AllBlocked.nil))))
private theorem no_4_375 : search 4 [0xffaa,0xaa00,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffaa,0xaa00,0xcccc,0xf0f0] [[0x55aa,0xcccc,0xf0f0],[0x55aa,0xffaa,0xcccc,0xf0f0],[0x55aa,0xaa00,0xcccc,0xf0f0],[0x2200,0xffaa,0xcccc,0xf0f0],[0x44cc,0xffaa,0xaa00,0xf0f0],[0xeecc,0xffaa,0xf0f0],[0xeecc,0xffaa,0xcccc,0xf0f0],[0xeecc,0xffaa,0xaa00,0xf0f0],[0xa00,0xffaa,0xcccc,0xf0f0],[0x50f0,0xffaa,0xaa00,0xcccc],[0xfaf0,0xffaa,0xcccc],[0xfaf0,0xffaa,0xcccc,0xf0f0],[0xfaf0,0xffaa,0xaa00,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_159 (AllBlocked.cons no_3_161 (AllBlocked.cons no_3_157 (AllBlocked.cons no_3_62 (AllBlocked.cons no_3_130 (AllBlocked.cons no_3_299 (AllBlocked.cons no_3_298 (AllBlocked.cons no_3_296 (AllBlocked.cons no_3_22 (AllBlocked.cons no_3_148 (AllBlocked.cons no_3_376 (AllBlocked.cons no_3_377 (AllBlocked.cons no_3_374 (AllBlocked.nil))))))))))))))
private theorem no_4_376 : search 4 [0xffaa,0xaa00,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffaa,0xaa00,0xcccc,0xf0f0,0xff00] [[0x55aa,0xcccc,0xf0f0,0xff00],[0xeecc,0xffaa,0xf0f0,0xff00],[0xfaf0,0xffaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_160 (AllBlocked.cons no_3_300 (AllBlocked.cons no_3_378 (AllBlocked.nil))))
private theorem no_4_377 : search 4 [0xffaa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffaa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaa00,0xffaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_208 (AllBlocked.nil))
private theorem no_4_378 : search 4 [0xffaa,0xeeee,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffaa,0xeeee,0xcccc,0xf0f0,0xff00] [[0xeeaa,0xcccc,0xf0f0,0xff00],[0xee00,0xffaa,0xcccc,0xf0f0],[0xcc88,0xeeee,0xf0f0,0xff00],[0xffcc,0xffaa,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_283 (AllBlocked.cons no_3_277 (AllBlocked.cons no_3_237 (AllBlocked.cons no_3_540 (AllBlocked.nil)))))
private theorem no_4_379 : search 4 [0xffaa,0xfafa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffaa,0xfafa,0xcccc,0xf0f0,0xff00] [[0xfaaa,0xcccc,0xf0f0,0xff00],[0xfa00,0xffaa,0xcccc,0xf0f0],[0xf0a0,0xfafa,0xcccc,0xff00],[0xfff0,0xffaa,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_359 (AllBlocked.cons no_3_354 (AllBlocked.cons no_3_330 (AllBlocked.cons no_3_564 (AllBlocked.nil)))))
private theorem no_4_380 : search 4 [0xffaa,0xffcc,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffaa,0xffcc,0xaaaa,0xcccc,0xf0f0] [[0xff88,0xaaaa,0xcccc,0xf0f0],[0xaa88,0xffaa,0xcccc,0xf0f0],[0xeeee,0xffaa,0xffcc,0xf0f0],[0xcc88,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_465 (AllBlocked.cons no_3_213 (AllBlocked.cons no_3_324 (AllBlocked.cons no_3_238 (AllBlocked.nil)))))
private theorem no_4_381 : search 4 [0xffaa,0xfff0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffaa,0xfff0,0xaaaa,0xcccc,0xf0f0] [[0xffa0,0xaaaa,0xcccc,0xf0f0],[0xaaa0,0xffaa,0xcccc,0xf0f0],[0xfafa,0xffaa,0xfff0,0xcccc],[0xf0a0,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_476 (AllBlocked.cons no_3_215 (AllBlocked.cons no_3_401 (AllBlocked.cons no_3_331 (AllBlocked.nil)))))
private theorem no_4_382 : search 4 [0xffc0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffc0,0xaaaa,0xcccc,0xf0f0] [[0xc0c,0xffc0,0xaaaa,0xf0f0],[0x3030,0xffc0,0xaaaa,0xcccc],[0xfcfc,0xffc0,0xaaaa],[0xfcfc,0xffc0,0xaaaa,0xf0f0],[0xfcfc,0xffc0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_39 (AllBlocked.cons no_3_85 (AllBlocked.cons no_3_445 (AllBlocked.cons no_3_447 (AllBlocked.cons no_3_446 (AllBlocked.nil))))))
private theorem no_4_383 : search 4 [0xffc0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffc0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfcfc,0xffc0,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_448 (AllBlocked.nil))
private theorem no_4_384 : search 4 [0xffc0,0xc0c0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffc0,0xc0c0,0xaaaa,0xcccc,0xf0f0] [[0x3f00,0xaaaa,0xcccc,0xf0f0],[0xc0c,0xffc0,0xaaaa,0xf0f0],[0x3030,0xffc0,0xaaaa,0xcccc],[0x2a2a,0xffc0,0xcccc,0xf0f0],[0xeaea,0xffc0,0xcccc,0xf0f0],[0xfcfc,0xffc0,0xc0c0,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_114 (AllBlocked.cons no_3_39 (AllBlocked.cons no_3_85 (AllBlocked.cons no_3_78 (AllBlocked.cons no_3_264 (AllBlocked.cons no_3_449 (AllBlocked.nil)))))))
private theorem no_4_385 : search 4 [0xffcc,0xcc,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffcc,0xcc,0xaaaa,0xcccc,0xf0f0] [[0xff00,0xaaaa,0xcccc,0xf0f0],[0xcc00,0xffcc,0xaaaa,0xf0f0],[0x3300,0xcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_233 (AllBlocked.cons no_3_92 (AllBlocked.nil))))
private theorem no_4_386 : search 4 [0xffcc,0xc0c,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xffcc,0xc0c,0xaaaa,0xf0f0,0xff00] [[0xc00,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_34 (AllBlocked.nil))
private theorem no_4_387 : search 4 [0xffcc,0xf00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffcc,0xf00,0xaaaa,0xcccc,0xf0f0] [[0xc00,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_34 (AllBlocked.nil))
private theorem no_4_388 : search 4 [0xffcc,0x3300,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xffcc,0x3300,0xaaaa,0xf0f0,0xff00] [[0xcccc,0xaaaa,0xf0f0,0xff00],[0xcc00,0xffcc,0xaaaa,0xf0f0],[0xcc,0x3300,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_242 (AllBlocked.cons no_3_233 (AllBlocked.cons no_3_8 (AllBlocked.nil))))
private theorem no_4_389 : search 4 [0xffcc,0x4444,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xffcc,0x4444,0xaaaa,0xf0f0,0xff00] [[0x4400,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_119 (AllBlocked.nil))
private theorem no_4_390 : search 4 [0xffcc,0x5500,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffcc,0x5500,0xaaaa,0xcccc,0xf0f0] [[0x4400,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_119 (AllBlocked.nil))
private theorem no_4_391 : search 4 [0xffcc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffcc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xcc00,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_233 (AllBlocked.nil))
private theorem no_4_392 : search 4 [0xffcc,0xcc00,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffcc,0xcc00,0xaaaa,0xcccc,0xf0f0] [[0x33cc,0xaaaa,0xcccc,0xf0f0],[0xfcf0,0xffcc,0xaaaa,0xcccc],[0xeeaa,0xffcc,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_100 (AllBlocked.cons no_3_424 (AllBlocked.cons no_3_287 (AllBlocked.nil))))
private theorem no_4_393 : search 4 [0xffcc,0xcc00,0xaaaa,0xf0f0] = false :=
  noNode 3 [0xffcc,0xcc00,0xaaaa,0xf0f0] [[0x33cc,0xaaaa,0xf0f0],[0x33cc,0xffcc,0xaaaa,0xf0f0],[0x33cc,0xcc00,0xaaaa,0xf0f0],[0xc00,0xffcc,0xaaaa,0xf0f0],[0x30f0,0xffcc,0xcc00,0xaaaa],[0xfcf0,0xffcc,0xaaaa],[0xfcf0,0xffcc,0xaaaa,0xf0f0],[0xfcf0,0xffcc,0xcc00,0xaaaa],[0x22aa,0xffcc,0xcc00,0xf0f0],[0x4400,0xffcc,0xaaaa,0xf0f0],[0xeeaa,0xffcc,0xf0f0],[0xeeaa,0xffcc,0xcc00,0xf0f0],[0xeeaa,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_101 (AllBlocked.cons no_3_104 (AllBlocked.cons no_3_103 (AllBlocked.cons no_3_34 (AllBlocked.cons no_3_91 (AllBlocked.cons no_3_423 (AllBlocked.cons no_3_425 (AllBlocked.cons no_3_427 (AllBlocked.cons no_3_73 (AllBlocked.cons no_3_119 (AllBlocked.cons no_3_288 (AllBlocked.cons no_3_286 (AllBlocked.cons no_3_285 (AllBlocked.nil))))))))))))))
private theorem no_4_394 : search 4 [0xffcc,0xcc00,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xffcc,0xcc00,0xaaaa,0xf0f0,0xff00] [[0x33cc,0xaaaa,0xf0f0,0xff00],[0xfcf0,0xffcc,0xaaaa,0xff00],[0xeeaa,0xffcc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_102 (AllBlocked.cons no_3_426 (AllBlocked.cons no_3_289 (AllBlocked.nil))))
private theorem no_4_395 : search 4 [0xffcc,0xeeee,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xffcc,0xeeee,0xaaaa,0xf0f0,0xff00] [[0xeecc,0xaaaa,0xf0f0,0xff00],[0xee00,0xffcc,0xaaaa,0xf0f0],[0xaa88,0xeeee,0xf0f0,0xff00],[0xffaa,0xffcc,0xeeee,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_294 (AllBlocked.cons no_3_278 (AllBlocked.cons no_3_212 (AllBlocked.cons no_3_505 (AllBlocked.nil)))))
private theorem no_4_396 : search 4 [0xffcc,0xfcfc,0xaaaa,0xf0f0,0xff00] = false :=
  noNode 3 [0xffcc,0xfcfc,0xaaaa,0xf0f0,0xff00] [[0xfccc,0xaaaa,0xf0f0,0xff00],[0xfc00,0xffcc,0xaaaa,0xf0f0],[0xf0c0,0xfcfc,0xaaaa,0xff00],[0xfff0,0xffcc,0xfcfc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_408 (AllBlocked.cons no_3_403 (AllBlocked.cons no_3_332 (AllBlocked.cons no_3_565 (AllBlocked.nil)))))
private theorem no_4_397 : search 4 [0xffcc,0xffaa,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffcc,0xffaa,0xaaaa,0xcccc,0xf0f0] [[0xff88,0xaaaa,0xcccc,0xf0f0],[0xaa88,0xffaa,0xcccc,0xf0f0],[0xeeee,0xffcc,0xffaa,0xf0f0],[0xcc88,0xffcc,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_465 (AllBlocked.cons no_3_213 (AllBlocked.cons no_3_325 (AllBlocked.cons no_3_238 (AllBlocked.nil)))))
private theorem no_4_398 : search 4 [0xffcc,0xfff0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xffcc,0xfff0,0xaaaa,0xcccc,0xf0f0] [[0xffc0,0xaaaa,0xcccc,0xf0f0],[0xccc0,0xffcc,0xaaaa,0xf0f0],[0xfcfc,0xffcc,0xfff0,0xaaaa],[0xf0c0,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_510 (AllBlocked.cons no_3_240 (AllBlocked.cons no_3_450 (AllBlocked.cons no_3_333 (AllBlocked.nil)))))
private theorem no_4_399 : search 4 [0xffee,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xffee,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xf0e0,0xaaaa,0xcccc,0xff00],[0xf0e,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_334 (AllBlocked.cons no_3_51 (AllBlocked.nil)))
private theorem no_4_400 : search 4 [0xfff0,0xf0,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xfff0,0xf0,0xaaaa,0xcccc,0xf0f0] [[0xff00,0xaaaa,0xcccc,0xf0f0],[0xf000,0xfff0,0xaaaa,0xcccc],[0xf00,0xf0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_456 (AllBlocked.cons no_3_326 (AllBlocked.cons no_3_46 (AllBlocked.nil))))
private theorem no_4_401 : search 4 [0xfff0,0xf00,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfff0,0xf00,0xaaaa,0xcccc,0xff00] [[0xf0f0,0xaaaa,0xcccc,0xff00],[0xf000,0xfff0,0xaaaa,0xcccc],[0xf0,0xf00,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_335 (AllBlocked.cons no_3_326 (AllBlocked.cons no_3_13 (AllBlocked.nil))))
private theorem no_4_402 : search 4 [0xfff0,0x3030,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfff0,0x3030,0xaaaa,0xcccc,0xff00] [[0x3000,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_80 (AllBlocked.nil))
private theorem no_4_403 : search 4 [0xfff0,0x3300,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xfff0,0x3300,0xaaaa,0xcccc,0xf0f0] [[0x3000,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_80 (AllBlocked.nil))
private theorem no_4_404 : search 4 [0xfff0,0x5050,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfff0,0x5050,0xaaaa,0xcccc,0xff00] [[0x5000,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_137 (AllBlocked.nil))
private theorem no_4_405 : search 4 [0xfff0,0x5500,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xfff0,0x5500,0xaaaa,0xcccc,0xf0f0] [[0x5000,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_137 (AllBlocked.nil))
private theorem no_4_406 : search 4 [0xfff0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfff0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xf000,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_326 (AllBlocked.nil))
private theorem no_4_407 : search 4 [0xfff0,0xf000,0xaaaa,0xcccc] = false :=
  noNode 3 [0xfff0,0xf000,0xaaaa,0xcccc] [[0xff0,0xaaaa,0xcccc],[0xff0,0xfff0,0xaaaa,0xcccc],[0xff0,0xf000,0xaaaa,0xcccc],[0xaaa,0xfff0,0xf000,0xcccc],[0x5000,0xfff0,0xaaaa,0xcccc],[0xfaaa,0xfff0,0xcccc],[0xfaaa,0xfff0,0xf000,0xcccc],[0xfaaa,0xfff0,0xaaaa,0xcccc],[0xccc,0xfff0,0xf000,0xaaaa],[0x3000,0xfff0,0xaaaa,0xcccc],[0xfccc,0xfff0,0xaaaa],[0xfccc,0xfff0,0xf000,0xaaaa],[0xfccc,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_54 (AllBlocked.cons no_3_58 (AllBlocked.cons no_3_57 (AllBlocked.cons no_3_33 (AllBlocked.cons no_3_137 (AllBlocked.cons no_3_363 (AllBlocked.cons no_3_366 (AllBlocked.cons no_3_362 (AllBlocked.cons no_3_45 (AllBlocked.cons no_3_80 (AllBlocked.cons no_3_411 (AllBlocked.cons no_3_415 (AllBlocked.cons no_3_412 (AllBlocked.nil))))))))))))))
private theorem no_4_408 : search 4 [0xfff0,0xf000,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xfff0,0xf000,0xaaaa,0xcccc,0xf0f0] [[0xff0,0xaaaa,0xcccc,0xf0f0],[0xfaaa,0xfff0,0xcccc,0xf0f0],[0xfccc,0xfff0,0xaaaa,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_55 (AllBlocked.cons no_3_364 (AllBlocked.cons no_3_413 (AllBlocked.nil))))
private theorem no_4_409 : search 4 [0xfff0,0xf000,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfff0,0xf000,0xaaaa,0xcccc,0xff00] [[0xff0,0xaaaa,0xcccc,0xff00],[0xfaaa,0xfff0,0xcccc,0xff00],[0xfccc,0xfff0,0xaaaa,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_56 (AllBlocked.cons no_3_365 (AllBlocked.cons no_3_414 (AllBlocked.nil))))
private theorem no_4_410 : search 4 [0xfff0,0xfafa,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfff0,0xfafa,0xaaaa,0xcccc,0xff00] [[0xfaf0,0xaaaa,0xcccc,0xff00],[0xfa00,0xfff0,0xaaaa,0xcccc],[0xaaa0,0xfafa,0xcccc,0xff00],[0xffaa,0xfff0,0xfafa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_372 (AllBlocked.cons no_3_355 (AllBlocked.cons no_3_214 (AllBlocked.cons no_3_506 (AllBlocked.nil)))))
private theorem no_4_411 : search 4 [0xfff0,0xfcfc,0xaaaa,0xcccc,0xff00] = false :=
  noNode 3 [0xfff0,0xfcfc,0xaaaa,0xcccc,0xff00] [[0xfcf0,0xaaaa,0xcccc,0xff00],[0xfc00,0xfff0,0xaaaa,0xcccc],[0xccc0,0xfcfc,0xaaaa,0xff00],[0xffcc,0xfff0,0xfcfc,0xaaaa]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_420 (AllBlocked.cons no_3_404 (AllBlocked.cons no_3_239 (AllBlocked.cons no_3_541 (AllBlocked.nil)))))
private theorem no_4_412 : search 4 [0xfff0,0xffaa,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xfff0,0xffaa,0xaaaa,0xcccc,0xf0f0] [[0xffa0,0xaaaa,0xcccc,0xf0f0],[0xaaa0,0xffaa,0xcccc,0xf0f0],[0xfafa,0xfff0,0xffaa,0xcccc],[0xf0a0,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_476 (AllBlocked.cons no_3_215 (AllBlocked.cons no_3_402 (AllBlocked.cons no_3_331 (AllBlocked.nil)))))
private theorem no_4_413 : search 4 [0xfff0,0xffcc,0xaaaa,0xcccc,0xf0f0] = false :=
  noNode 3 [0xfff0,0xffcc,0xaaaa,0xcccc,0xf0f0] [[0xffc0,0xaaaa,0xcccc,0xf0f0],[0xccc0,0xffcc,0xaaaa,0xf0f0],[0xfcfc,0xfff0,0xffcc,0xaaaa],[0xf0c0,0xfff0,0xaaaa,0xcccc]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_510 (AllBlocked.cons no_3_240 (AllBlocked.cons no_3_451 (AllBlocked.cons no_3_333 (AllBlocked.nil)))))
private theorem no_4_414 : search 4 [0xfffa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfffa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xccc8,0xaaaa,0xf0f0,0xff00],[0x3332,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_241 (AllBlocked.cons no_3_97 (AllBlocked.nil)))
private theorem no_4_415 : search 4 [0xfffc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 3 [0xfffc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaaa8,0xcccc,0xf0f0,0xff00],[0x5554,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_3_216 (AllBlocked.cons no_3_154 (AllBlocked.nil)))
private theorem no_5_0 : search 5 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaa00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa00,0xaa,0xcccc,0xf0f0,0xff00],[0x88,0xaaaa,0xcccc,0xf0f0,0xff00],[0x22,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc44,0xaaaa,0xcccc,0xf0f0,0xff00],[0xccee,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf050,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf0fa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffaa,0xaa,0xaaaa,0xcccc,0xf0f0],[0x2222,0xaa,0xcccc,0xf0f0,0xff00],[0xeeee,0xaa,0xcccc,0xf0f0,0xff00],[0xa0a,0xaa,0xcccc,0xf0f0,0xff00],[0xfafa,0xaa,0xcccc,0xf0f0,0xff00],[0xaa00,0xaa,0xcccc,0xf0f0,0xff00],[0x5500,0xaa,0xcccc,0xf0f0],[0x5500,0xaa,0xcccc,0xf0f0,0xff00],[0x5500,0xaa,0xaaaa,0xcccc,0xf0f0],[0xffaa,0xaa,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_217 (AllBlocked.cons no_4_215 (AllBlocked.cons no_4_6 (AllBlocked.cons no_4_2 (AllBlocked.cons no_4_252 (AllBlocked.cons no_4_255 (AllBlocked.cons no_4_7 (AllBlocked.cons no_4_0 (AllBlocked.cons no_4_299 (AllBlocked.cons no_4_302 (AllBlocked.cons no_4_377 (AllBlocked.cons no_4_368 (AllBlocked.cons no_4_92 (AllBlocked.cons no_4_278 (AllBlocked.cons no_4_48 (AllBlocked.cons no_4_320 (AllBlocked.cons no_4_215 (AllBlocked.cons no_4_172 (AllBlocked.cons no_4_173 (AllBlocked.cons no_4_171 (AllBlocked.cons no_4_368 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_1 : search 5 [0xcc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xcc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x88,0xaaaa,0xcccc,0xf0f0,0xff00],[0x44,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa22,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaaee,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc00,0xcc,0xaaaa,0xf0f0,0xff00],[0xc0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf030,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf0fc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffcc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffcc,0xcc,0xaaaa,0xcccc,0xf0f0],[0x4444,0xcc,0xaaaa,0xf0f0,0xff00],[0xeeee,0xcc,0xaaaa,0xf0f0,0xff00],[0xc0c,0xcc,0xaaaa,0xf0f0,0xff00],[0xfcfc,0xcc,0xaaaa,0xf0f0,0xff00],[0xcc00,0xcc,0xaaaa,0xf0f0,0xff00],[0x3300,0xcc,0xaaaa,0xf0f0],[0x3300,0xcc,0xaaaa,0xf0f0,0xff00],[0x3300,0xcc,0xaaaa,0xcccc,0xf0f0],[0xffcc,0xcc,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_6 (AllBlocked.cons no_4_4 (AllBlocked.cons no_4_222 (AllBlocked.cons no_4_225 (AllBlocked.cons no_4_247 (AllBlocked.cons no_4_245 (AllBlocked.cons no_4_18 (AllBlocked.cons no_4_1 (AllBlocked.cons no_4_298 (AllBlocked.cons no_4_303 (AllBlocked.cons no_4_391 (AllBlocked.cons no_4_385 (AllBlocked.cons no_4_140 (AllBlocked.cons no_4_279 (AllBlocked.cons no_4_62 (AllBlocked.cons no_4_341 (AllBlocked.cons no_4_245 (AllBlocked.cons no_4_124 (AllBlocked.cons no_4_125 (AllBlocked.cons no_4_123 (AllBlocked.cons no_4_385 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_2 : search 5 [0xf0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xf0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xa0,0xaaaa,0xcccc,0xf0f0,0xff00],[0x50,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa0a,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaafa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0,0xaaaa,0xcccc,0xf0f0,0xff00],[0x30,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc0c,0xaaaa,0xcccc,0xf0f0,0xff00],[0xccfc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf000,0xf0,0xaaaa,0xcccc,0xff00],[0xfff0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfff0,0xf0,0xaaaa,0xcccc,0xf0f0],[0x5050,0xf0,0xaaaa,0xcccc,0xff00],[0xfafa,0xf0,0xaaaa,0xcccc,0xff00],[0x3030,0xf0,0xaaaa,0xcccc,0xff00],[0xfcfc,0xf0,0xaaaa,0xcccc,0xff00],[0xf000,0xf0,0xaaaa,0xcccc,0xff00],[0xf00,0xf0,0xaaaa,0xcccc],[0xf00,0xf0,0xaaaa,0xcccc,0xff00],[0xf00,0xf0,0xaaaa,0xcccc,0xf0f0],[0xfff0,0xf0,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_7 (AllBlocked.cons no_4_5 (AllBlocked.cons no_4_221 (AllBlocked.cons no_4_226 (AllBlocked.cons no_4_18 (AllBlocked.cons no_4_3 (AllBlocked.cons no_4_251 (AllBlocked.cons no_4_256 (AllBlocked.cons no_4_294 (AllBlocked.cons no_4_292 (AllBlocked.cons no_4_406 (AllBlocked.cons no_4_400 (AllBlocked.cons no_4_157 (AllBlocked.cons no_4_321 (AllBlocked.cons no_4_109 (AllBlocked.cons no_4_342 (AllBlocked.cons no_4_292 (AllBlocked.cons no_4_76 (AllBlocked.cons no_4_78 (AllBlocked.cons no_4_77 (AllBlocked.cons no_4_400 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_3 : search 5 [0xa0a,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xa0a,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xa0a0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0a0,0xa0a,0xcccc,0xf0f0,0xff00],[0x808,0xaaaa,0xcccc,0xf0f0,0xff00],[0x202,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc4c4,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcece,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfafa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfafa,0xa0a,0xaaaa,0xcccc,0xff00],[0xa00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf500,0xaaaa,0xcccc,0xf0f0,0xff00],[0xff0a,0xaaaa,0xcccc,0xf0f0,0xff00],[0x2222,0xa0a,0xcccc,0xf0f0,0xff00],[0xeeee,0xa0a,0xcccc,0xf0f0,0xff00],[0xa0a0,0xa0a,0xcccc,0xf0f0,0xff00],[0x5050,0xa0a,0xcccc,0xff00],[0x5050,0xa0a,0xcccc,0xf0f0,0xff00],[0x5050,0xa0a,0xaaaa,0xcccc,0xff00],[0xfafa,0xa0a,0xaaaa,0xcccc,0xff00],[0xaa,0xa0a,0xcccc,0xf0f0,0xff00],[0xffaa,0xa0a,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_207 (AllBlocked.cons no_4_205 (AllBlocked.cons no_4_46 (AllBlocked.cons no_4_42 (AllBlocked.cons no_4_243 (AllBlocked.cons no_4_257 (AllBlocked.cons no_4_329 (AllBlocked.cons no_4_322 (AllBlocked.cons no_4_47 (AllBlocked.cons no_4_0 (AllBlocked.cons no_4_308 (AllBlocked.cons no_4_356 (AllBlocked.cons no_4_93 (AllBlocked.cons no_4_280 (AllBlocked.cons no_4_205 (AllBlocked.cons no_4_160 (AllBlocked.cons no_4_159 (AllBlocked.cons no_4_158 (AllBlocked.cons no_4_322 (AllBlocked.cons no_4_8 (AllBlocked.cons no_4_369 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_4 : search 5 [0xc0c,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xc0c,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x808,0xaaaa,0xcccc,0xf0f0,0xff00],[0x404,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa2a2,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaeae,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c0,0xc0c,0xaaaa,0xf0f0,0xff00],[0xfcfc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfcfc,0xc0c,0xaaaa,0xcccc,0xff00],[0xc00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf300,0xaaaa,0xcccc,0xf0f0,0xff00],[0xff0c,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4444,0xc0c,0xaaaa,0xf0f0,0xff00],[0xeeee,0xc0c,0xaaaa,0xf0f0,0xff00],[0xc0c0,0xc0c,0xaaaa,0xf0f0,0xff00],[0x3030,0xc0c,0xaaaa,0xff00],[0x3030,0xc0c,0xaaaa,0xf0f0,0xff00],[0x3030,0xc0c,0xaaaa,0xcccc,0xff00],[0xfcfc,0xc0c,0xaaaa,0xcccc,0xff00],[0xcc,0xc0c,0xaaaa,0xf0f0,0xff00],[0xffcc,0xc0c,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_46 (AllBlocked.cons no_4_44 (AllBlocked.cons no_4_213 (AllBlocked.cons no_4_227 (AllBlocked.cons no_4_237 (AllBlocked.cons no_4_235 (AllBlocked.cons no_4_347 (AllBlocked.cons no_4_343 (AllBlocked.cons no_4_61 (AllBlocked.cons no_4_1 (AllBlocked.cons no_4_305 (AllBlocked.cons no_4_357 (AllBlocked.cons no_4_141 (AllBlocked.cons no_4_281 (AllBlocked.cons no_4_235 (AllBlocked.cons no_4_112 (AllBlocked.cons no_4_111 (AllBlocked.cons no_4_110 (AllBlocked.cons no_4_343 (AllBlocked.cons no_4_19 (AllBlocked.cons no_4_386 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_5 : search 5 [0xf00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xf00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xa00,0xaaaa,0xcccc,0xf0f0,0xff00],[0x500,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0aa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xafaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc00,0xaaaa,0xcccc,0xf0f0,0xff00],[0x300,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0cc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcfcc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfff0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfff0,0xf00,0xaaaa,0xcccc,0xff00],[0xf000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf000,0xf00,0xaaaa,0xcccc,0xf0f0],[0x5500,0xf00,0xaaaa,0xcccc,0xf0f0],[0xffaa,0xf00,0xaaaa,0xcccc,0xf0f0],[0x3300,0xf00,0xaaaa,0xcccc,0xf0f0],[0xffcc,0xf00,0xaaaa,0xcccc,0xf0f0],[0xf000,0xf00,0xaaaa,0xcccc,0xf0f0],[0xf0,0xf00,0xaaaa,0xcccc],[0xf0,0xf00,0xaaaa,0xcccc,0xff00],[0xf0,0xf00,0xaaaa,0xcccc,0xf0f0],[0xfff0,0xf00,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_47 (AllBlocked.cons no_4_45 (AllBlocked.cons no_4_211 (AllBlocked.cons no_4_229 (AllBlocked.cons no_4_61 (AllBlocked.cons no_4_43 (AllBlocked.cons no_4_241 (AllBlocked.cons no_4_259 (AllBlocked.cons no_4_406 (AllBlocked.cons no_4_401 (AllBlocked.cons no_4_294 (AllBlocked.cons no_4_293 (AllBlocked.cons no_4_174 (AllBlocked.cons no_4_370 (AllBlocked.cons no_4_126 (AllBlocked.cons no_4_387 (AllBlocked.cons no_4_293 (AllBlocked.cons no_4_30 (AllBlocked.cons no_4_32 (AllBlocked.cons no_4_31 (AllBlocked.cons no_4_401 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_6 : search 5 [0x2222,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0x2222,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[0x8888,0x2222,0xcccc,0xf0f0,0xff00],[0xeeee,0xaaaa,0xcccc,0xf0f0,0xff00],[0xeeee,0x2222,0xaaaa,0xf0f0,0xff00],[0x2020,0xaaaa,0xcccc,0xf0f0,0xff00],[0x202,0xaaaa,0xcccc,0xf0f0,0xff00],[0xd0d0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf2f2,0xaaaa,0xcccc,0xf0f0,0xff00],[0x2200,0xaaaa,0xcccc,0xf0f0,0xff00],[0x22,0xaaaa,0xcccc,0xf0f0,0xff00],[0xdd00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xff22,0xaaaa,0xcccc,0xf0f0,0xff00],[0x8888,0x2222,0xcccc,0xf0f0,0xff00],[0x4444,0x2222,0xf0f0,0xff00],[0x4444,0x2222,0xcccc,0xf0f0,0xff00],[0x4444,0x2222,0xaaaa,0xf0f0,0xff00],[0xeeee,0x2222,0xaaaa,0xf0f0,0xff00],[0xa0a,0x2222,0xcccc,0xf0f0,0xff00],[0xfafa,0x2222,0xcccc,0xf0f0,0xff00],[0xaa,0x2222,0xcccc,0xf0f0,0xff00],[0xffaa,0x2222,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_196 (AllBlocked.cons no_4_194 (AllBlocked.cons no_4_287 (AllBlocked.cons no_4_282 (AllBlocked.cons no_4_90 (AllBlocked.cons no_4_42 (AllBlocked.cons no_4_260 (AllBlocked.cons no_4_304 (AllBlocked.cons no_4_91 (AllBlocked.cons no_4_2 (AllBlocked.cons no_4_262 (AllBlocked.cons no_4_358 (AllBlocked.cons no_4_194 (AllBlocked.cons no_4_144 (AllBlocked.cons no_4_143 (AllBlocked.cons no_4_142 (AllBlocked.cons no_4_282 (AllBlocked.cons no_4_49 (AllBlocked.cons no_4_323 (AllBlocked.cons no_4_9 (AllBlocked.cons no_4_371 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_7 : search 5 [0x3030,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0x3030,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x2020,0xaaaa,0xcccc,0xf0f0,0xff00],[0x1010,0xaaaa,0xcccc,0xf0f0,0xff00],[0x8a8a,0xaaaa,0xcccc,0xf0f0,0xff00],[0xbaba,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfcfc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfcfc,0x3030,0xaaaa,0xf0f0,0xff00],[0xc0c0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c0,0x3030,0xaaaa,0xcccc,0xff00],[0x3000,0xaaaa,0xcccc,0xf0f0,0xff00],[0x30,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcf00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xff30,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5050,0x3030,0xaaaa,0xcccc,0xff00],[0xfafa,0x3030,0xaaaa,0xcccc,0xff00],[0xc0c0,0x3030,0xaaaa,0xcccc,0xff00],[0xc0c,0x3030,0xaaaa,0xff00],[0xc0c,0x3030,0xaaaa,0xf0f0,0xff00],[0xc0c,0x3030,0xaaaa,0xcccc,0xff00],[0xfcfc,0x3030,0xaaaa,0xf0f0,0xff00],[0xf0,0x3030,0xaaaa,0xcccc,0xff00],[0xfff0,0x3030,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_90 (AllBlocked.cons no_4_88 (AllBlocked.cons no_4_202 (AllBlocked.cons no_4_231 (AllBlocked.cons no_4_347 (AllBlocked.cons no_4_344 (AllBlocked.cons no_4_237 (AllBlocked.cons no_4_236 (AllBlocked.cons no_4_108 (AllBlocked.cons no_4_3 (AllBlocked.cons no_4_258 (AllBlocked.cons no_4_359 (AllBlocked.cons no_4_161 (AllBlocked.cons no_4_324 (AllBlocked.cons no_4_236 (AllBlocked.cons no_4_65 (AllBlocked.cons no_4_64 (AllBlocked.cons no_4_63 (AllBlocked.cons no_4_344 (AllBlocked.cons no_4_33 (AllBlocked.cons no_4_402 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_8 : search 5 [0x3300,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0x3300,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x2200,0xaaaa,0xcccc,0xf0f0,0xff00],[0x1100,0xaaaa,0xcccc,0xf0f0,0xff00],[0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xbbaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffcc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffcc,0x3300,0xaaaa,0xf0f0,0xff00],[0x3000,0xaaaa,0xcccc,0xf0f0,0xff00],[0x300,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0f0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf3f0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc00,0x3300,0xaaaa,0xcccc,0xf0f0],[0x5500,0x3300,0xaaaa,0xcccc,0xf0f0],[0xffaa,0x3300,0xaaaa,0xcccc,0xf0f0],[0xcc00,0x3300,0xaaaa,0xcccc,0xf0f0],[0xcc,0x3300,0xaaaa,0xf0f0],[0xcc,0x3300,0xaaaa,0xf0f0,0xff00],[0xcc,0x3300,0xaaaa,0xcccc,0xf0f0],[0xffcc,0x3300,0xaaaa,0xf0f0,0xff00],[0xf00,0x3300,0xaaaa,0xcccc,0xf0f0],[0xfff0,0x3300,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_91 (AllBlocked.cons no_4_89 (AllBlocked.cons no_4_200 (AllBlocked.cons no_4_233 (AllBlocked.cons no_4_391 (AllBlocked.cons no_4_388 (AllBlocked.cons no_4_108 (AllBlocked.cons no_4_43 (AllBlocked.cons no_4_242 (AllBlocked.cons no_4_306 (AllBlocked.cons no_4_247 (AllBlocked.cons no_4_246 (AllBlocked.cons no_4_175 (AllBlocked.cons no_4_372 (AllBlocked.cons no_4_246 (AllBlocked.cons no_4_21 (AllBlocked.cons no_4_22 (AllBlocked.cons no_4_20 (AllBlocked.cons no_4_388 (AllBlocked.cons no_4_79 (AllBlocked.cons no_4_403 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_9 : search 5 [0x4444,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0x4444,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xeeee,0xaaaa,0xcccc,0xf0f0,0xff00],[0xeeee,0x4444,0xcccc,0xf0f0,0xff00],[0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[0x8888,0x4444,0xaaaa,0xf0f0,0xff00],[0x4040,0xaaaa,0xcccc,0xf0f0,0xff00],[0x404,0xaaaa,0xcccc,0xf0f0,0xff00],[0xb0b0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf4f4,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4400,0xaaaa,0xcccc,0xf0f0,0xff00],[0x44,0xaaaa,0xcccc,0xf0f0,0xff00],[0xbb00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xff44,0xaaaa,0xcccc,0xf0f0,0xff00],[0x8888,0x4444,0xaaaa,0xf0f0,0xff00],[0x2222,0x4444,0xf0f0,0xff00],[0x2222,0x4444,0xcccc,0xf0f0,0xff00],[0x2222,0x4444,0xaaaa,0xf0f0,0xff00],[0xeeee,0x4444,0xcccc,0xf0f0,0xff00],[0xc0c,0x4444,0xaaaa,0xf0f0,0xff00],[0xfcfc,0x4444,0xaaaa,0xf0f0,0xff00],[0xcc,0x4444,0xaaaa,0xf0f0,0xff00],[0xffcc,0x4444,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_287 (AllBlocked.cons no_4_283 (AllBlocked.cons no_4_196 (AllBlocked.cons no_4_195 (AllBlocked.cons no_4_138 (AllBlocked.cons no_4_44 (AllBlocked.cons no_4_230 (AllBlocked.cons no_4_307 (AllBlocked.cons no_4_139 (AllBlocked.cons no_4_4 (AllBlocked.cons no_4_232 (AllBlocked.cons no_4_360 (AllBlocked.cons no_4_195 (AllBlocked.cons no_4_96 (AllBlocked.cons no_4_95 (AllBlocked.cons no_4_94 (AllBlocked.cons no_4_283 (AllBlocked.cons no_4_66 (AllBlocked.cons no_4_345 (AllBlocked.cons no_4_23 (AllBlocked.cons no_4_389 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_10 : search 5 [0x5050,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0x5050,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfafa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfafa,0x5050,0xcccc,0xf0f0,0xff00],[0x4040,0xaaaa,0xcccc,0xf0f0,0xff00],[0x1010,0xaaaa,0xcccc,0xf0f0,0xff00],[0x8c8c,0xaaaa,0xcccc,0xf0f0,0xff00],[0xdcdc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0a0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0a0,0x5050,0xaaaa,0xcccc,0xff00],[0x5000,0xaaaa,0xcccc,0xf0f0,0xff00],[0x50,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaf00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xff50,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0a0,0x5050,0xaaaa,0xcccc,0xff00],[0xa0a,0x5050,0xcccc,0xff00],[0xa0a,0x5050,0xcccc,0xf0f0,0xff00],[0xa0a,0x5050,0xaaaa,0xcccc,0xff00],[0xfafa,0x5050,0xcccc,0xf0f0,0xff00],[0x3030,0x5050,0xaaaa,0xcccc,0xff00],[0xfcfc,0x5050,0xaaaa,0xcccc,0xff00],[0xf0,0x5050,0xaaaa,0xcccc,0xff00],[0xfff0,0x5050,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_329 (AllBlocked.cons no_4_325 (AllBlocked.cons no_4_138 (AllBlocked.cons no_4_88 (AllBlocked.cons no_4_203 (AllBlocked.cons no_4_261 (AllBlocked.cons no_4_207 (AllBlocked.cons no_4_206 (AllBlocked.cons no_4_156 (AllBlocked.cons no_4_5 (AllBlocked.cons no_4_228 (AllBlocked.cons no_4_361 (AllBlocked.cons no_4_206 (AllBlocked.cons no_4_52 (AllBlocked.cons no_4_51 (AllBlocked.cons no_4_50 (AllBlocked.cons no_4_325 (AllBlocked.cons no_4_113 (AllBlocked.cons no_4_346 (AllBlocked.cons no_4_34 (AllBlocked.cons no_4_404 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_11 : search 5 [0x5500,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0x5500,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xffaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffaa,0x5500,0xcccc,0xf0f0,0xff00],[0x4400,0xaaaa,0xcccc,0xf0f0,0xff00],[0x1100,0xaaaa,0xcccc,0xf0f0,0xff00],[0x88cc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xddcc,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5000,0xaaaa,0xcccc,0xf0f0,0xff00],[0x500,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0f0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf5f0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa00,0x5500,0xaaaa,0xcccc,0xf0f0],[0xaa00,0x5500,0xaaaa,0xcccc,0xf0f0],[0xaa,0x5500,0xcccc,0xf0f0],[0xaa,0x5500,0xcccc,0xf0f0,0xff00],[0xaa,0x5500,0xaaaa,0xcccc,0xf0f0],[0xffaa,0x5500,0xcccc,0xf0f0,0xff00],[0x3300,0x5500,0xaaaa,0xcccc,0xf0f0],[0xffcc,0x5500,0xaaaa,0xcccc,0xf0f0],[0xf00,0x5500,0xaaaa,0xcccc,0xf0f0],[0xfff0,0x5500,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_377 (AllBlocked.cons no_4_373 (AllBlocked.cons no_4_139 (AllBlocked.cons no_4_89 (AllBlocked.cons no_4_201 (AllBlocked.cons no_4_263 (AllBlocked.cons no_4_156 (AllBlocked.cons no_4_45 (AllBlocked.cons no_4_212 (AllBlocked.cons no_4_309 (AllBlocked.cons no_4_217 (AllBlocked.cons no_4_216 (AllBlocked.cons no_4_216 (AllBlocked.cons no_4_11 (AllBlocked.cons no_4_12 (AllBlocked.cons no_4_10 (AllBlocked.cons no_4_373 (AllBlocked.cons no_4_127 (AllBlocked.cons no_4_390 (AllBlocked.cons no_4_80 (AllBlocked.cons no_4_405 (AllBlocked.nil))))))))))))))))))))))
private theorem no_5_12 : search 5 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x2222,0xaaaa,0xcccc,0xf0f0,0xff00],[0x2222,0x8888,0xcccc,0xf0f0,0xff00],[0x4444,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4444,0x8888,0xaaaa,0xf0f0,0xff00],[0x8080,0xaaaa,0xcccc,0xf0f0,0xff00],[0x808,0xaaaa,0xcccc,0xf0f0,0xff00],[0x7070,0xaaaa,0xcccc,0xff00],[0x7070,0xaaaa,0xcccc,0xf0f0,0xff00],[0x7070,0x8888,0xaaaa,0xcccc,0xff00],[0xf8f8,0xaaaa,0xcccc,0xff00],[0xf8f8,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf8f8,0x8888,0xaaaa,0xcccc,0xff00],[0x8800,0xaaaa,0xcccc,0xf0f0,0xff00],[0x88,0xaaaa,0xcccc,0xf0f0,0xff00],[0x7700,0xaaaa,0xcccc,0xf0f0],[0x7700,0xaaaa,0xcccc,0xf0f0,0xff00],[0x7700,0x8888,0xaaaa,0xcccc,0xf0f0],[0xff88,0xaaaa,0xcccc,0xf0f0],[0xff88,0xaaaa,0xcccc,0xf0f0,0xff00],[0xff88,0x8888,0xaaaa,0xcccc,0xf0f0],[0x2222,0x8888,0xcccc,0xf0f0,0xff00],[0x4444,0x8888,0xaaaa,0xf0f0,0xff00],[0xeeee,0x8888,0xf0f0,0xff00],[0xeeee,0x8888,0xcccc,0xf0f0,0xff00],[0xeeee,0x8888,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_98 (AllBlocked.cons no_4_97 (AllBlocked.cons no_4_146 (AllBlocked.cons no_4_145 (AllBlocked.cons no_4_192 (AllBlocked.cons no_4_46 (AllBlocked.cons no_4_188 (AllBlocked.cons no_4_187 (AllBlocked.cons no_4_186 (AllBlocked.cons no_4_312 (AllBlocked.cons no_4_311 (AllBlocked.cons no_4_310 (AllBlocked.cons no_4_193 (AllBlocked.cons no_4_6 (AllBlocked.cons no_4_190 (AllBlocked.cons no_4_191 (AllBlocked.cons no_4_189 (AllBlocked.cons no_4_363 (AllBlocked.cons no_4_364 (AllBlocked.cons no_4_362 (AllBlocked.cons no_4_97 (AllBlocked.cons no_4_145 (AllBlocked.cons no_4_286 (AllBlocked.cons no_4_285 (AllBlocked.cons no_4_284 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_13 : search 5 [0xa0a0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xa0a0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xa0a,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0a,0xa0a0,0xcccc,0xf0f0,0xff00],[0x8080,0xaaaa,0xcccc,0xf0f0,0xff00],[0x2020,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4c4c,0xaaaa,0xf0f0,0xff00],[0x4c4c,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4c4c,0xa0a0,0xaaaa,0xf0f0,0xff00],[0xecec,0xaaaa,0xf0f0,0xff00],[0xecec,0xaaaa,0xcccc,0xf0f0,0xff00],[0xecec,0xa0a0,0xaaaa,0xf0f0,0xff00],[0x5050,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5050,0xa0a0,0xaaaa,0xcccc,0xff00],[0xa000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5f00,0xaaaa,0xcccc,0xf0f0],[0x5f00,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5f00,0xa0a0,0xaaaa,0xcccc,0xf0f0],[0xffa0,0xaaaa,0xcccc,0xf0f0],[0xffa0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffa0,0xa0a0,0xaaaa,0xcccc,0xf0f0],[0xa0a,0xa0a0,0xcccc,0xf0f0,0xff00],[0x5050,0xa0a0,0xaaaa,0xcccc,0xff00],[0xfafa,0xa0a0,0xcccc,0xff00],[0xfafa,0xa0a0,0xcccc,0xf0f0,0xff00],[0xfafa,0xa0a0,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_54 (AllBlocked.cons no_4_53 (AllBlocked.cons no_4_192 (AllBlocked.cons no_4_90 (AllBlocked.cons no_4_155 (AllBlocked.cons no_4_154 (AllBlocked.cons no_4_153 (AllBlocked.cons no_4_270 (AllBlocked.cons no_4_269 (AllBlocked.cons no_4_268 (AllBlocked.cons no_4_163 (AllBlocked.cons no_4_162 (AllBlocked.cons no_4_204 (AllBlocked.cons no_4_7 (AllBlocked.cons no_4_184 (AllBlocked.cons no_4_185 (AllBlocked.cons no_4_183 (AllBlocked.cons no_4_366 (AllBlocked.cons no_4_367 (AllBlocked.cons no_4_365 (AllBlocked.cons no_4_53 (AllBlocked.cons no_4_162 (AllBlocked.cons no_4_328 (AllBlocked.cons no_4_327 (AllBlocked.cons no_4_326 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_14 : search 5 [0xaa00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xaa00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa,0xaa00,0xcccc,0xf0f0,0xff00],[0x8800,0xaaaa,0xcccc,0xf0f0,0xff00],[0x2200,0xaaaa,0xcccc,0xf0f0,0xff00],[0x44cc,0xaaaa,0xf0f0,0xff00],[0x44cc,0xaaaa,0xcccc,0xf0f0,0xff00],[0x44cc,0xaa00,0xaaaa,0xf0f0,0xff00],[0xeecc,0xaaaa,0xf0f0,0xff00],[0xeecc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xeecc,0xaa00,0xaaaa,0xf0f0,0xff00],[0xa000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa00,0xaaaa,0xcccc,0xf0f0,0xff00],[0x50f0,0xaaaa,0xcccc,0xff00],[0x50f0,0xaaaa,0xcccc,0xf0f0,0xff00],[0x50f0,0xaa00,0xaaaa,0xcccc,0xff00],[0xfaf0,0xaaaa,0xcccc,0xff00],[0xfaf0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfaf0,0xaa00,0xaaaa,0xcccc,0xff00],[0x5500,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5500,0xaa00,0xaaaa,0xcccc,0xf0f0],[0xaa,0xaa00,0xcccc,0xf0f0,0xff00],[0x5500,0xaa00,0xaaaa,0xcccc,0xf0f0],[0xffaa,0xaa00,0xcccc,0xf0f0],[0xffaa,0xaa00,0xcccc,0xf0f0,0xff00],[0xffaa,0xaa00,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_14 (AllBlocked.cons no_4_13 (AllBlocked.cons no_4_193 (AllBlocked.cons no_4_91 (AllBlocked.cons no_4_152 (AllBlocked.cons no_4_151 (AllBlocked.cons no_4_150 (AllBlocked.cons no_4_277 (AllBlocked.cons no_4_276 (AllBlocked.cons no_4_275 (AllBlocked.cons no_4_204 (AllBlocked.cons no_4_47 (AllBlocked.cons no_4_169 (AllBlocked.cons no_4_168 (AllBlocked.cons no_4_167 (AllBlocked.cons no_4_319 (AllBlocked.cons no_4_318 (AllBlocked.cons no_4_317 (AllBlocked.cons no_4_177 (AllBlocked.cons no_4_176 (AllBlocked.cons no_4_13 (AllBlocked.cons no_4_176 (AllBlocked.cons no_4_375 (AllBlocked.cons no_4_376 (AllBlocked.cons no_4_374 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_15 : search 5 [0xc0c0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xc0c0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xc0c,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c,0xc0c0,0xaaaa,0xf0f0,0xff00],[0x3030,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3030,0xc0c0,0xaaaa,0xcccc,0xff00],[0xc000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3f00,0xaaaa,0xcccc,0xf0f0],[0x3f00,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3f00,0xc0c0,0xaaaa,0xcccc,0xf0f0],[0xffc0,0xaaaa,0xcccc,0xf0f0],[0xffc0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffc0,0xc0c0,0xaaaa,0xcccc,0xf0f0],[0x8080,0xaaaa,0xcccc,0xf0f0,0xff00],[0x2a2a,0xcccc,0xf0f0,0xff00],[0x2a2a,0xc0c0,0xcccc,0xf0f0,0xff00],[0x2a2a,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4040,0xaaaa,0xcccc,0xf0f0,0xff00],[0xeaea,0xcccc,0xf0f0,0xff00],[0xeaea,0xc0c0,0xcccc,0xf0f0,0xff00],[0xeaea,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c,0xc0c0,0xaaaa,0xf0f0,0xff00],[0x3030,0xc0c0,0xaaaa,0xcccc,0xff00],[0xfcfc,0xc0c0,0xaaaa,0xff00],[0xfcfc,0xc0c0,0xaaaa,0xf0f0,0xff00],[0xfcfc,0xc0c0,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_67 (AllBlocked.cons no_4_68 (AllBlocked.cons no_4_114 (AllBlocked.cons no_4_115 (AllBlocked.cons no_4_234 (AllBlocked.cons no_4_18 (AllBlocked.cons no_4_135 (AllBlocked.cons no_4_136 (AllBlocked.cons no_4_137 (AllBlocked.cons no_4_382 (AllBlocked.cons no_4_383 (AllBlocked.cons no_4_384 (AllBlocked.cons no_4_192 (AllBlocked.cons no_4_107 (AllBlocked.cons no_4_106 (AllBlocked.cons no_4_105 (AllBlocked.cons no_4_138 (AllBlocked.cons no_4_267 (AllBlocked.cons no_4_266 (AllBlocked.cons no_4_265 (AllBlocked.cons no_4_68 (AllBlocked.cons no_4_115 (AllBlocked.cons no_4_350 (AllBlocked.cons no_4_349 (AllBlocked.cons no_4_348 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_16 : search 5 [0xcc00,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xcc00,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xcc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc,0xcc00,0xaaaa,0xf0f0,0xff00],[0xc000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc00,0xaaaa,0xcccc,0xf0f0,0xff00],[0x30f0,0xaaaa,0xcccc,0xff00],[0x30f0,0xaaaa,0xcccc,0xf0f0,0xff00],[0x30f0,0xcc00,0xaaaa,0xcccc,0xff00],[0xfcf0,0xaaaa,0xcccc,0xff00],[0xfcf0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfcf0,0xcc00,0xaaaa,0xcccc,0xff00],[0x3300,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3300,0xcc00,0xaaaa,0xcccc,0xf0f0],[0x8800,0xaaaa,0xcccc,0xf0f0,0xff00],[0x22aa,0xcccc,0xf0f0,0xff00],[0x22aa,0xcc00,0xcccc,0xf0f0,0xff00],[0x22aa,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4400,0xaaaa,0xcccc,0xf0f0,0xff00],[0xeeaa,0xcccc,0xf0f0,0xff00],[0xeeaa,0xcc00,0xcccc,0xf0f0,0xff00],[0xeeaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc,0xcc00,0xaaaa,0xf0f0,0xff00],[0x3300,0xcc00,0xaaaa,0xcccc,0xf0f0],[0xffcc,0xcc00,0xaaaa,0xf0f0],[0xffcc,0xcc00,0xaaaa,0xf0f0,0xff00],[0xffcc,0xcc00,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_24 (AllBlocked.cons no_4_25 (AllBlocked.cons no_4_234 (AllBlocked.cons no_4_61 (AllBlocked.cons no_4_120 (AllBlocked.cons no_4_119 (AllBlocked.cons no_4_121 (AllBlocked.cons no_4_339 (AllBlocked.cons no_4_338 (AllBlocked.cons no_4_340 (AllBlocked.cons no_4_128 (AllBlocked.cons no_4_129 (AllBlocked.cons no_4_193 (AllBlocked.cons no_4_104 (AllBlocked.cons no_4_103 (AllBlocked.cons no_4_102 (AllBlocked.cons no_4_139 (AllBlocked.cons no_4_274 (AllBlocked.cons no_4_273 (AllBlocked.cons no_4_272 (AllBlocked.cons no_4_25 (AllBlocked.cons no_4_129 (AllBlocked.cons no_4_393 (AllBlocked.cons no_4_394 (AllBlocked.cons no_4_392 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_17 : search 5 [0xeeee,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xeeee,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xe0e0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xe0e,0xaaaa,0xcccc,0xf0f0,0xff00],[0x1010,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfefe,0xaaaa,0xcccc,0xf0f0,0xff00],[0xee00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xee,0xaaaa,0xcccc,0xf0f0,0xff00],[0x1100,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffee,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4444,0xeeee,0xcccc,0xf0f0,0xff00],[0x4444,0xaaaa,0xcccc,0xf0f0,0xff00],[0x8888,0xeeee,0xf0f0,0xff00],[0x8888,0xeeee,0xcccc,0xf0f0,0xff00],[0x8888,0xeeee,0xaaaa,0xf0f0,0xff00],[0x2222,0xeeee,0xaaaa,0xf0f0,0xff00],[0x4444,0xeeee,0xcccc,0xf0f0,0xff00],[0xa0a,0xeeee,0xcccc,0xf0f0,0xff00],[0xfafa,0xeeee,0xcccc,0xf0f0,0xff00],[0xaa,0xeeee,0xcccc,0xf0f0,0xff00],[0xffaa,0xeeee,0xcccc,0xf0f0,0xff00],[0x2222,0xeeee,0xaaaa,0xf0f0,0xff00],[0x2222,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c,0xeeee,0xaaaa,0xf0f0,0xff00],[0xfcfc,0xeeee,0xaaaa,0xf0f0,0xff00],[0xcc,0xeeee,0xaaaa,0xf0f0,0xff00],[0xffcc,0xeeee,0xaaaa,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_264 (AllBlocked.cons no_4_75 (AllBlocked.cons no_4_88 (AllBlocked.cons no_4_355 (AllBlocked.cons no_4_271 (AllBlocked.cons no_4_29 (AllBlocked.cons no_4_89 (AllBlocked.cons no_4_399 (AllBlocked.cons no_4_147 (AllBlocked.cons no_4_146 (AllBlocked.cons no_4_199 (AllBlocked.cons no_4_198 (AllBlocked.cons no_4_197 (AllBlocked.cons no_4_99 (AllBlocked.cons no_4_147 (AllBlocked.cons no_4_55 (AllBlocked.cons no_4_330 (AllBlocked.cons no_4_15 (AllBlocked.cons no_4_378 (AllBlocked.cons no_4_99 (AllBlocked.cons no_4_98 (AllBlocked.cons no_4_69 (AllBlocked.cons no_4_351 (AllBlocked.cons no_4_26 (AllBlocked.cons no_4_395 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_18 : search 5 [0xf000,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xf000,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xf0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf0,0xf000,0xaaaa,0xcccc,0xff00],[0xf00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf00,0xf000,0xaaaa,0xcccc,0xf0f0],[0xa000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaaa,0xcccc,0xf0f0,0xff00],[0xaaa,0xf000,0xcccc,0xf0f0,0xff00],[0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfaaa,0xcccc,0xf0f0,0xff00],[0xfaaa,0xf000,0xcccc,0xf0f0,0xff00],[0xfaaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xccc,0xaaaa,0xf0f0,0xff00],[0xccc,0xf000,0xaaaa,0xf0f0,0xff00],[0xccc,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfccc,0xaaaa,0xf0f0,0xff00],[0xfccc,0xf000,0xaaaa,0xf0f0,0xff00],[0xfccc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf0,0xf000,0xaaaa,0xcccc,0xff00],[0xf00,0xf000,0xaaaa,0xcccc,0xf0f0],[0xfff0,0xf000,0xaaaa,0xcccc],[0xfff0,0xf000,0xaaaa,0xcccc,0xff00],[0xfff0,0xf000,0xaaaa,0xcccc,0xf0f0]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_35 (AllBlocked.cons no_4_36 (AllBlocked.cons no_4_81 (AllBlocked.cons no_4_82 (AllBlocked.cons no_4_204 (AllBlocked.cons no_4_59 (AllBlocked.cons no_4_60 (AllBlocked.cons no_4_58 (AllBlocked.cons no_4_156 (AllBlocked.cons no_4_315 (AllBlocked.cons no_4_316 (AllBlocked.cons no_4_314 (AllBlocked.cons no_4_234 (AllBlocked.cons no_4_73 (AllBlocked.cons no_4_74 (AllBlocked.cons no_4_72 (AllBlocked.cons no_4_108 (AllBlocked.cons no_4_336 (AllBlocked.cons no_4_337 (AllBlocked.cons no_4_335 (AllBlocked.cons no_4_36 (AllBlocked.cons no_4_82 (AllBlocked.cons no_4_407 (AllBlocked.cons no_4_409 (AllBlocked.cons no_4_408 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_19 : search 5 [0xfafa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xfafa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfa00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfa,0xaaaa,0xcccc,0xf0f0,0xff00],[0x500,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfffa,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5050,0xfafa,0xcccc,0xf0f0,0xff00],[0x5050,0xaaaa,0xcccc,0xf0f0,0xff00],[0x2222,0xfafa,0xcccc,0xf0f0,0xff00],[0xeeee,0xfafa,0xcccc,0xf0f0,0xff00],[0xa0a0,0xfafa,0xcccc,0xff00],[0xa0a0,0xfafa,0xcccc,0xf0f0,0xff00],[0xa0a0,0xfafa,0xaaaa,0xcccc,0xff00],[0xa0a,0xfafa,0xaaaa,0xcccc,0xff00],[0x5050,0xfafa,0xcccc,0xf0f0,0xff00],[0xaa,0xfafa,0xcccc,0xf0f0,0xff00],[0xffaa,0xfafa,0xcccc,0xf0f0,0xff00],[0xc8c8,0xaaaa,0xcccc,0xf0f0,0xff00],[0x404,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3232,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfefe,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3030,0xfafa,0xaaaa,0xcccc,0xff00],[0xfcfc,0xfafa,0xaaaa,0xcccc,0xff00],[0xa0a,0xfafa,0xaaaa,0xcccc,0xff00],[0xa0a,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf0,0xfafa,0xaaaa,0xcccc,0xff00],[0xfff0,0xfafa,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_313 (AllBlocked.cons no_4_40 (AllBlocked.cons no_4_45 (AllBlocked.cons no_4_414 (AllBlocked.cons no_4_164 (AllBlocked.cons no_4_163 (AllBlocked.cons no_4_100 (AllBlocked.cons no_4_288 (AllBlocked.cons no_4_210 (AllBlocked.cons no_4_209 (AllBlocked.cons no_4_208 (AllBlocked.cons no_4_56 (AllBlocked.cons no_4_164 (AllBlocked.cons no_4_16 (AllBlocked.cons no_4_379 (AllBlocked.cons no_4_244 (AllBlocked.cons no_4_44 (AllBlocked.cons no_4_122 (AllBlocked.cons no_4_355 (AllBlocked.cons no_4_116 (AllBlocked.cons no_4_352 (AllBlocked.cons no_4_56 (AllBlocked.cons no_4_54 (AllBlocked.cons no_4_37 (AllBlocked.cons no_4_410 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_20 : search 5 [0xfcfc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xfcfc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xfc00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfc,0xaaaa,0xcccc,0xf0f0,0xff00],[0x300,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfffc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00],[0x202,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5454,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfefe,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4444,0xfcfc,0xaaaa,0xf0f0,0xff00],[0xeeee,0xfcfc,0xaaaa,0xf0f0,0xff00],[0x5050,0xfcfc,0xaaaa,0xcccc,0xff00],[0xfafa,0xfcfc,0xaaaa,0xcccc,0xff00],[0x3030,0xfcfc,0xaaaa,0xf0f0,0xff00],[0x3030,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c0,0xfcfc,0xaaaa,0xff00],[0xc0c0,0xfcfc,0xaaaa,0xf0f0,0xff00],[0xc0c0,0xfcfc,0xaaaa,0xcccc,0xff00],[0xc0c,0xfcfc,0xaaaa,0xcccc,0xff00],[0x3030,0xfcfc,0xaaaa,0xf0f0,0xff00],[0xcc,0xfcfc,0xaaaa,0xf0f0,0xff00],[0xffcc,0xfcfc,0xaaaa,0xf0f0,0xff00],[0xc0c,0xfcfc,0xaaaa,0xcccc,0xff00],[0xc0c,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf0,0xfcfc,0xaaaa,0xcccc,0xff00],[0xfff0,0xfcfc,0xaaaa,0xcccc,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_334 (AllBlocked.cons no_4_41 (AllBlocked.cons no_4_43 (AllBlocked.cons no_4_415 (AllBlocked.cons no_4_214 (AllBlocked.cons no_4_42 (AllBlocked.cons no_4_170 (AllBlocked.cons no_4_355 (AllBlocked.cons no_4_148 (AllBlocked.cons no_4_289 (AllBlocked.cons no_4_165 (AllBlocked.cons no_4_331 (AllBlocked.cons no_4_117 (AllBlocked.cons no_4_114 (AllBlocked.cons no_4_240 (AllBlocked.cons no_4_239 (AllBlocked.cons no_4_238 (AllBlocked.cons no_4_70 (AllBlocked.cons no_4_117 (AllBlocked.cons no_4_27 (AllBlocked.cons no_4_396 (AllBlocked.cons no_4_70 (AllBlocked.cons no_4_67 (AllBlocked.cons no_4_38 (AllBlocked.cons no_4_411 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_21 : search 5 [0xffaa,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xffaa,0xaaaa,0xcccc,0xf0f0,0xff00] [[0x5500,0xffaa,0xcccc,0xf0f0,0xff00],[0x5500,0xaaaa,0xcccc,0xf0f0,0xff00],[0x2222,0xffaa,0xcccc,0xf0f0,0xff00],[0xeeee,0xffaa,0xcccc,0xf0f0,0xff00],[0xa0a,0xffaa,0xcccc,0xf0f0,0xff00],[0xfafa,0xffaa,0xcccc,0xf0f0,0xff00],[0xaa00,0xffaa,0xcccc,0xf0f0],[0xaa00,0xffaa,0xcccc,0xf0f0,0xff00],[0xaa00,0xffaa,0xaaaa,0xcccc,0xf0f0],[0xaa,0xffaa,0xaaaa,0xcccc,0xf0f0],[0x5500,0xffaa,0xcccc,0xf0f0,0xff00],[0xcc88,0xaaaa,0xcccc,0xf0f0,0xff00],[0x44,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3322,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffee,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3300,0xffaa,0xaaaa,0xcccc,0xf0f0],[0xffcc,0xffaa,0xaaaa,0xcccc,0xf0f0],[0xf0a0,0xaaaa,0xcccc,0xf0f0,0xff00],[0x50,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf0a,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfffa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf00,0xffaa,0xaaaa,0xcccc,0xf0f0],[0xfff0,0xffaa,0xaaaa,0xcccc,0xf0f0],[0xaa,0xffaa,0xaaaa,0xcccc,0xf0f0],[0xaa,0xaaaa,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_178 (AllBlocked.cons no_4_177 (AllBlocked.cons no_4_101 (AllBlocked.cons no_4_290 (AllBlocked.cons no_4_57 (AllBlocked.cons no_4_332 (AllBlocked.cons no_4_219 (AllBlocked.cons no_4_220 (AllBlocked.cons no_4_218 (AllBlocked.cons no_4_17 (AllBlocked.cons no_4_178 (AllBlocked.cons no_4_253 (AllBlocked.cons no_4_4 (AllBlocked.cons no_4_133 (AllBlocked.cons no_4_399 (AllBlocked.cons no_4_130 (AllBlocked.cons no_4_397 (AllBlocked.cons no_4_300 (AllBlocked.cons no_4_5 (AllBlocked.cons no_4_86 (AllBlocked.cons no_4_414 (AllBlocked.cons no_4_83 (AllBlocked.cons no_4_412 (AllBlocked.cons no_4_17 (AllBlocked.cons no_4_14 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_22 : search 5 [0xffcc,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xffcc,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaa88,0xaaaa,0xcccc,0xf0f0,0xff00],[0x22,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5544,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffee,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4444,0xffcc,0xaaaa,0xf0f0,0xff00],[0xeeee,0xffcc,0xaaaa,0xf0f0,0xff00],[0x5500,0xffcc,0xaaaa,0xcccc,0xf0f0],[0xffaa,0xffcc,0xaaaa,0xcccc,0xf0f0],[0x3300,0xffcc,0xaaaa,0xf0f0,0xff00],[0x3300,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c,0xffcc,0xaaaa,0xf0f0,0xff00],[0xfcfc,0xffcc,0xaaaa,0xf0f0,0xff00],[0xcc00,0xffcc,0xaaaa,0xf0f0],[0xcc00,0xffcc,0xaaaa,0xf0f0,0xff00],[0xcc00,0xffcc,0xaaaa,0xcccc,0xf0f0],[0xcc,0xffcc,0xaaaa,0xcccc,0xf0f0],[0x3300,0xffcc,0xaaaa,0xf0f0,0xff00],[0xf0c0,0xaaaa,0xcccc,0xf0f0,0xff00],[0x30,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf0c,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfffc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf00,0xffcc,0xaaaa,0xcccc,0xf0f0],[0xfff0,0xffcc,0xaaaa,0xcccc,0xf0f0],[0xcc,0xffcc,0xaaaa,0xcccc,0xf0f0],[0xcc,0xaaaa,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_223 (AllBlocked.cons no_4_2 (AllBlocked.cons no_4_181 (AllBlocked.cons no_4_399 (AllBlocked.cons no_4_149 (AllBlocked.cons no_4_291 (AllBlocked.cons no_4_179 (AllBlocked.cons no_4_380 (AllBlocked.cons no_4_131 (AllBlocked.cons no_4_128 (AllBlocked.cons no_4_71 (AllBlocked.cons no_4_353 (AllBlocked.cons no_4_249 (AllBlocked.cons no_4_250 (AllBlocked.cons no_4_248 (AllBlocked.cons no_4_28 (AllBlocked.cons no_4_131 (AllBlocked.cons no_4_301 (AllBlocked.cons no_4_3 (AllBlocked.cons no_4_87 (AllBlocked.cons no_4_415 (AllBlocked.cons no_4_84 (AllBlocked.cons no_4_413 (AllBlocked.cons no_4_28 (AllBlocked.cons no_4_24 (AllBlocked.nil))))))))))))))))))))))))))
private theorem no_5_23 : search 5 [0xfff0,0xaaaa,0xcccc,0xf0f0,0xff00] = false :=
  noNode 4 [0xfff0,0xaaaa,0xcccc,0xf0f0,0xff00] [[0xaaa0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5550,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfffa,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5050,0xfff0,0xaaaa,0xcccc,0xff00],[0xfafa,0xfff0,0xaaaa,0xcccc,0xff00],[0x5500,0xfff0,0xaaaa,0xcccc,0xf0f0],[0xffaa,0xfff0,0xaaaa,0xcccc,0xf0f0],[0xccc0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3330,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfffc,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3030,0xfff0,0xaaaa,0xcccc,0xff00],[0xfcfc,0xfff0,0xaaaa,0xcccc,0xff00],[0x3300,0xfff0,0xaaaa,0xcccc,0xf0f0],[0xffcc,0xfff0,0xaaaa,0xcccc,0xf0f0],[0xf00,0xfff0,0xaaaa,0xcccc,0xff00],[0xf00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf000,0xfff0,0xaaaa,0xcccc],[0xf000,0xfff0,0xaaaa,0xcccc,0xff00],[0xf000,0xfff0,0xaaaa,0xcccc,0xf0f0],[0xf0,0xfff0,0xaaaa,0xcccc,0xf0f0],[0xf00,0xfff0,0xaaaa,0xcccc,0xff00],[0xf0,0xfff0,0xaaaa,0xcccc,0xf0f0],[0xf0,0xaaaa,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_4_224 (AllBlocked.cons no_4_0 (AllBlocked.cons no_4_182 (AllBlocked.cons no_4_414 (AllBlocked.cons no_4_166 (AllBlocked.cons no_4_333 (AllBlocked.cons no_4_180 (AllBlocked.cons no_4_381 (AllBlocked.cons no_4_254 (AllBlocked.cons no_4_1 (AllBlocked.cons no_4_134 (AllBlocked.cons no_4_415 (AllBlocked.cons no_4_118 (AllBlocked.cons no_4_354 (AllBlocked.cons no_4_132 (AllBlocked.cons no_4_398 (AllBlocked.cons no_4_85 (AllBlocked.cons no_4_81 (AllBlocked.cons no_4_295 (AllBlocked.cons no_4_297 (AllBlocked.cons no_4_296 (AllBlocked.cons no_4_39 (AllBlocked.cons no_4_85 (AllBlocked.cons no_4_39 (AllBlocked.cons no_4_35 (AllBlocked.nil))))))))))))))))))))))))))
theorem root_cert : search 6 inputs = false :=
  noNode 5 inputs [[0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[0x2222,0xaaaa,0xcccc,0xf0f0,0xff00],[0x4444,0xaaaa,0xcccc,0xf0f0,0xff00],[0xeeee,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0a0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xa0a,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5050,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfafa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0x5500,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffaa,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xc0c,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3030,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfcfc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xcc,0xaaaa,0xcccc,0xf0f0,0xff00],[0x3300,0xaaaa,0xcccc,0xf0f0,0xff00],[0xffcc,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf000,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf0,0xaaaa,0xcccc,0xf0f0,0xff00],[0xf00,0xaaaa,0xcccc,0xf0f0,0xff00],[0xfff0,0xaaaa,0xcccc,0xf0f0,0xff00]] (by decide +kernel) (by decide +kernel)
    (AllBlocked.cons no_5_12 (AllBlocked.cons no_5_6 (AllBlocked.cons no_5_9 (AllBlocked.cons no_5_17 (AllBlocked.cons no_5_13 (AllBlocked.cons no_5_3 (AllBlocked.cons no_5_10 (AllBlocked.cons no_5_19 (AllBlocked.cons no_5_14 (AllBlocked.cons no_5_0 (AllBlocked.cons no_5_11 (AllBlocked.cons no_5_21 (AllBlocked.cons no_5_15 (AllBlocked.cons no_5_4 (AllBlocked.cons no_5_7 (AllBlocked.cons no_5_20 (AllBlocked.cons no_5_16 (AllBlocked.cons no_5_1 (AllBlocked.cons no_5_8 (AllBlocked.cons no_5_22 (AllBlocked.cons no_5_18 (AllBlocked.cons no_5_2 (AllBlocked.cons no_5_5 (AllBlocked.cons no_5_23 (AllBlocked.nil)))))))))))))))))))))))))
end PEqualNP.Outside.L_meta_12339_aux.Threshold

open scoped BigOperators in
theorem PEqualNP.Outside.L_meta_12339 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        Nat.testBit (4276682472 * 2 ^ 32 + 4276650112)
          (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
          Nat.testBit (4276682472 * 2 ^ 32 + 4276650112)
            (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_12339_aux.exact_from_small_certificate
    PEqualNP.Outside.L_meta_12339_aux.Threshold.root_cert
