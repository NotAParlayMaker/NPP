import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9163

inductive Op where | conj | disj | neg deriving DecidableEq
inductive Ref where | literal (b : Bool) | wire (idx : Nat) deriving DecidableEq
inductive Code where | reuse (r : Ref) | mono (o : Op) (n : Nat) | bin (o : Op) (i j : Nat)
def Ref.eval (w : Nat → Bool) : Ref → Bool | .literal b => b | .wire i => w i

def Op.eval : Op → List Bool → Bool
  | .conj, xs => xs.all id
  | .disj, xs => xs.any id
  | .neg, xs => !(xs.head?.getD false)

def Code.eval (w : Nat → Bool) : Code → Bool
  | .reuse r => r.eval w
  | .mono o n => o.eval [w n]
  | .bin o i j => o.eval [w i,w j]

def Code.cost : Code → Nat | .reuse _ => 0 | _ => 1

def invert : Ref → Code
  | .literal v => .reuse (.literal (!v))
  | .wire i => .mono .neg i

def pair (o : Op) (a b : Ref) : Code :=
  match o, a, b with
  | .neg, x, _ => invert x
  | .conj, .literal false, _ | .conj, _, .literal false => .reuse (.literal false)
  | .conj, .literal true, x | .conj, x, .literal true => .reuse x
  | .disj, .literal true, _ | .disj, _, .literal true => .reuse (.literal true)
  | .disj, .literal false, x | .disj, x, .literal false => .reuse x
  | o, .wire i, .wire j => if i = j then .reuse (.wire i) else .bin o i j

def foldGate (o : Op) : List Ref → Code
  | [] => .reuse (.literal (o.eval []))
  | [x] => match o with | .neg => invert x | _ => .reuse x
  | a :: b :: _ => pair o a b

theorem pair_sound (w : Nat → Bool) (o : Op) (a b : Ref) :
    (pair o a b).eval w = o.eval [a.eval w,b.eval w] := by
  cases o <;> cases a with
  | literal v => cases v <;> cases b with
    | literal z => cases z <;> rfl
    | wire j => simp [pair, Code.eval, invert, Op.eval, Ref.eval]
  | wire i => cases b with
    | literal z => cases z <;> simp [pair, Code.eval, invert, Op.eval, Ref.eval]
    | wire j =>
      by_cases h : i = j
      · subst j; simp [pair, Code.eval, invert, Op.eval, Ref.eval]
      · simp [pair, Code.eval, invert, Op.eval, Ref.eval,h]

theorem foldGate_sound (w : Nat → Bool) (o : Op) (xs : List Ref) (len : xs.length ≤ 2) :
    (foldGate o xs).eval w = o.eval (xs.map (Ref.eval w)) := by
  cases xs with
  | nil => rfl
  | cons x xs => cases xs with
    | nil => cases o <;> cases x <;> simp [foldGate, invert, Code.eval, Ref.eval, Op.eval]
    | cons y ys =>
      have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at len; omega)
      subst ys
      exact pair_sound w o x y

theorem forced_and_cost (b : Ref) :
    (foldGate .conj [.literal false,b]).cost = 0 ∧
    (foldGate .conj [b,.literal false]).cost = 0 := by
  cases b with
  | literal v => cases v <;> decide
  | wire _ => exact ⟨rfl,rfl⟩

theorem consumer_cost (o : Op) (b : Ref) :
    (foldGate o [.literal false,b]).cost = 0 ∧
    (o ≠ .neg → (foldGate o [b,.literal false]).cost = 0) := by
  cases o <;> cases b with
  | literal v => cases v <;> decide
  | wire _ => simp [foldGate, pair, invert, Code.cost]

abbrev Gate := Op × List Nat
def lut (w : List Bool) (i : Nat) : Bool := w.getD i false
def getRef (refs : List Ref) (i : Nat) : Ref := refs.getD i (.literal false)
def Gate.value (g : Gate) (w : List Bool) : Bool := g.1.eval (g.2.map (lut w))
def Gate.step (w : List Bool) (g : Gate) : List Bool := w ++ [g.value w]

structure State where
  refs : List Ref
  gates : List Gate

def Code.emit (n : Nat) (c : Code) : List Gate × Ref :=
  match c with
  | .reuse r => ([],r)
  | .mono o i => ([(o,[i])],.wire n)
  | .bin o i j => ([(o,[i,j])],.wire n)

def State.compile (k : Nat) (s : State) (g : Gate) : State :=
  let (gs,r) := (foldGate g.1 (g.2.map (getRef s.refs))).emit (k + s.gates.length)
  ⟨s.refs ++ [r], s.gates ++ gs⟩

def Ref.bounded (n : Nat) : Ref → Prop
  | .literal _ => True
  | .wire i => i < n

def Code.bounded (n : Nat) : Code → Prop
  | .reuse r => r.bounded n
  | .mono _ i => i < n
  | .bin _ i j => i < n ∧ j < n

theorem invert_bounded {n : Nat} {r : Ref} (hr : r.bounded n) :
    (invert r).bounded n := by
  cases r <;> simpa [invert, Code.bounded, Ref.bounded] using hr

theorem pair_bounded {n : Nat} {a b : Ref} (o : Op)
    (ha : a.bounded n) (hb : b.bounded n) : (pair o a b).bounded n := by
  cases o <;> cases a with
  | literal v => cases v <;> cases b with
    | literal z => cases z <;> simp [pair, invert, Code.bounded, Ref.bounded]
    | wire j => simp_all [pair, invert, Code.bounded, Ref.bounded]
  | wire i => cases b with
    | literal z => cases z <;> simp_all [pair, invert, Code.bounded, Ref.bounded]
    | wire j =>
      by_cases h : i = j
      · subst j; simp_all [pair, invert, Code.bounded, Ref.bounded]
      · simp_all [pair, invert, Code.bounded, Ref.bounded]

theorem foldGate_bounded {n : Nat} (o : Op) (xs : List Ref)
    (h : ∀ r ∈ xs, r.bounded n) : (foldGate o xs).bounded n := by
  cases xs with
  | nil => trivial
  | cons x xs => cases xs with
    | nil =>
      have hx := h x (by simp)
      cases o <;> first | exact hx | exact invert_bounded hx
    | cons y ys => exact pair_bounded o (h x (by simp)) (h y (by simp))

theorem getRef_bounded {n : Nat} (refs : List Ref)
    (h : ∀ r ∈ refs, r.bounded n) (i : Nat) : (getRef refs i).bounded n := by
  unfold getRef
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < refs.length
  · rw [List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hi)]
    trivial

theorem lut_append_left {w ys : List Bool} {i : Nat} (hi : i < w.length) :
    lut (w ++ ys) i = lut w i := by
  simp only [lut, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem lut_append_here (w : List Bool) (v : Bool) : lut (w ++ [v]) w.length = v := by
  simp [lut, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem lut_append_past {w : List Bool} {v : Bool} {i : Nat} (hi : w.length < i) :
    lut (w ++ [v]) i = false := by
  have hh : (w ++ [v]).length ≤ i := by simp; omega
  simp only [lut,List.getD_eq_getElem?_getD,List.getElem?_eq_none_iff.mpr hh]
  rfl

theorem Ref.eval_append {r : Ref} {w : List Bool} (h : r.bounded w.length) (ys : List Bool) :
    r.eval (lut (w ++ ys)) = r.eval (lut w) := by
  cases r with
  | literal _ => rfl
  | wire _ => exact lut_append_left h

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl Gate.step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, iy, List.length_cons]
    omega
where iy : ∀ g : Gate, ∀ w : List Bool, (Gate.step w g).length = w.length + 1 :=
  fun _ _ => by simp [Gate.step]

theorem emit_eval (w : List Bool) (c : Code) :
    let (gs,r) := c.emit w.length
    r.eval (lut (gs.foldl Gate.step w)) = c.eval (lut w) := by
  cases c with
  | reuse r => rfl
  | mono o i => simp [Code.emit, Code.eval, lut_append_here, Gate.step, Gate.value, Ref.eval]
  | bin o i j => simp [Code.emit, Code.eval, lut_append_here, Gate.step, Gate.value, Ref.eval]

theorem Ref.bounded_le {n m : Nat} {r : Ref} (h : r.bounded n) (hnm : n ≤ m) :
    r.bounded m := by
  cases r with
  | literal _ => trivial
  | wire _ => exact Nat.lt_of_lt_of_le h hnm

theorem emit_count (n : Nat) (c : Code) : (c.emit n).1.length = c.cost := by
  cases c <;> rfl

theorem emit_ref_bounded (w : List Bool) {c : Code} (hc : c.bounded w.length) :
    let (gs,r) := c.emit w.length
    r.bounded (gs.foldl Gate.step w).length := by
  cases c with
  | reuse r => exact hc
  | mono o i => simp [Code.emit, Gate.step, Ref.bounded]
  | bin o i j => simp [Code.emit, Gate.step, Ref.bounded]

def Sim (s : State) (x w : List Bool) : Prop :=
  s.refs.length = w.length ∧
  (∀ r ∈ s.refs, r.bounded (s.gates.foldl Gate.step x).length) ∧
  ∀ i, (getRef s.refs i).eval (lut (s.gates.foldl Gate.step x)) = lut w i

theorem sim_compile {x w : List Bool} {s : State} {g : Gate}
    (hs : Sim s x w) (ha : g.2.length ≤ 2) :
    Sim (s.compile x.length g) x (Gate.step w g) := by
  let y := s.gates.foldl Gate.step x
  let c := foldGate g.1 (g.2.map (getRef s.refs))
  let e := c.emit y.length
  have tlen : y.length = x.length + s.gates.length := fold_length s.gates x
  change Sim ⟨s.refs ++ [(c.emit (x.length + s.gates.length)).2],
    s.gates ++ (c.emit (x.length + s.gates.length)).1⟩ x (Gate.step w g)
  rw [← tlen]
  change Sim ⟨s.refs ++ [e.2], s.gates ++ e.1⟩ x (Gate.step w g)
  have hcBound : c.bounded y.length := by
    apply foldGate_bounded
    intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact getRef_bounded s.refs hs.2.1 i
  have hlenGe : y.length ≤ (e.1.foldl Gate.step y).length := by
    rw [fold_length e.1 y]
    exact Nat.le_add_right y.length e.1.length
  have he : e.2.eval (lut (e.1.foldl Gate.step y)) = c.eval (lut y) := emit_eval y c
  have hy : (s.gates ++ e.1).foldl Gate.step x = e.1.foldl Gate.step y := by
    rw [List.foldl_append]
  refine ⟨by simp [Gate.step,hs.1], ?_, ?_⟩
  · intro r hr
    have hr' : r ∈ s.refs ∨ r = e.2 := by simpa using hr
    rw [hy]
    rcases hr' with hr'|rfl
    · exact Ref.bounded_le (hs.2.1 r hr') hlenGe
    · exact emit_ref_bounded y hcBound
  · intro i
    change (getRef (s.refs ++ [e.2]) i).eval (lut ((s.gates ++ e.1).foldl Gate.step x)) =
      lut (Gate.step w g) i
    rw [hy]
    rcases Nat.lt_trichotomy i w.length with hi|rfl|hi
    · have hj : i < s.refs.length := hs.1 ▸ hi
      have hget : getRef (s.refs ++ [e.2]) i = getRef s.refs i := by
        simp only [getRef,List.getD_eq_getElem?_getD,List.getElem?_append_left hj]
      rw [hget]
      have refOld := getRef_bounded s.refs hs.2.1 i
      have stable (z : List Bool) :
          (getRef s.refs i).eval (lut (y ++ z)) = (getRef s.refs i).eval (lut y) :=
        Ref.eval_append refOld z
      have heold : (getRef s.refs i).eval (lut (e.1.foldl Gate.step y)) =
          (getRef s.refs i).eval (lut y) := by
        cases hcode : c <;> simp [e, hcode, Code.emit, Gate.step, stable]
      rw [heold]
      change (getRef s.refs i).eval (lut y) = lut (w ++ [g.value w]) i
      rw [lut_append_left hi]
      exact hs.2.2 i
    · have hget : getRef (s.refs ++ [e.2]) w.length = e.2 := by
        rw [← hs.1]
        simp [getRef, List.getD_eq_getElem?_getD,List.getElem?_append_right]
      rw [hget,show lut (Gate.step w g) w.length = g.value w from lut_append_here w (g.value w)]
      change e.2.eval (lut (e.1.foldl Gate.step y)) = g.value w
      rw [he]
      change (foldGate g.1 (g.2.map (getRef s.refs))).eval (lut y) = g.value w
      rw [foldGate_sound _ _ _ (by simpa using ha)]
      simp only [Gate.value,List.map_map,Function.comp_apply]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hs.2.2 i
    · have hge : (s.refs ++ [e.2]).length ≤ i := by simp [hs.1]; omega
      unfold Gate.step
      rw [lut_append_past hi]
      simp [getRef,List.getD_eq_getElem?_getD,List.getElem?_eq_none_iff.mpr hge,Ref.eval]

theorem sim_all {gs : List Gate} {x w : List Bool} {s : State}
    (hs : Sim s x w) (ha : ∀ g ∈ gs, g.2.length ≤ 2) :
    Sim (gs.foldl (State.compile x.length) s) x (gs.foldl Gate.step w) := by
  induction gs generalizing s w with
  | nil => exact hs
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (sim_compile hs (ha g (by simp)))
    intro y hy
    exact ha y (by simp [hy])

def State.simplified (s : State) (g : Gate) : Code :=
  foldGate g.1 (g.2.map (getRef s.refs))

theorem Code.cost_le_one (c : Code) : c.cost ≤ 1 := by
  cases c <;> simp [Code.cost]

theorem compile_count (s : State) (n : Nat) (g : Gate) :
    (s.compile n g).gates.length = s.gates.length + (s.simplified g).cost := by
  simp only [State.compile, State.simplified, List.length_append, emit_count]

def dropCount (n : Nat) (s : State) : List Gate → Nat
  | [] => 0
  | g :: gs => (1 - (s.simplified g).cost) + dropCount n (s.compile n g) gs

theorem count_conservation (n : Nat) (s : State) (gs : List Gate) :
    (gs.foldl (State.compile n) s).gates.length + dropCount n s gs =
      s.gates.length + gs.length := by
  induction gs generalizing s with
  | nil => simp [dropCount]
  | cons g gs ih =>
    simp only [List.foldl_cons, dropCount, List.length_cons]
    have hi := ih (s.compile n g)
    rw [compile_count] at hi
    have hh := (s.simplified g).cost_le_one
    omega

theorem compile_drops (n i : Nat) (s : State) (gs : List Gate) (hi : i < gs.length)
    (hFold : (((gs.take i).foldl (State.compile n) s).simplified gs[i]).cost = 0) :
    1 ≤ dropCount n s gs := by
  induction gs generalizing s i with
  | nil => simp at hi
  | cons g gs ih =>
    cases i with
    | zero =>
      have h0 : (s.simplified g).cost = 0 := by simpa using hFold
      simp [dropCount, h0]
    | succ i =>
      have hi' : i < gs.length := by simpa using hi
      have h1 : ((((gs.take i).foldl (State.compile n) (s.compile n g))).simplified gs[i]).cost = 0 := by
        simpa [List.take_succ_cons,List.foldl_cons] using hFold
      have hh := ih i (s.compile n g) hi' h1
      simp only [dropCount]
      omega

theorem compile_drops_two (n i j : Nat) (s : State) (gs : List Gate) (hi : i < gs.length)
    (hj : j < gs.length) (hij : i < j)
    (hFoldI : (((gs.take i).foldl (State.compile n) s).simplified gs[i]).cost = 0)
    (hFoldJ : (((gs.take j).foldl (State.compile n) s).simplified gs[j]).cost = 0) :
    2 ≤ dropCount n s gs := by
  induction gs generalizing s i j with
  | nil => simp at hi
  | cons g gs ih =>
    cases j with
    | zero => omega
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have hJ : (((gs.take j).foldl (State.compile n) (s.compile n g)).simplified gs[j]).cost = 0 := by
        simpa [List.take_succ_cons,List.foldl_cons] using hFoldJ
      cases i with
      | zero =>
        have hI : (s.simplified g).cost = 0 := by simpa using hFoldI
        have h2 := compile_drops n j (s.compile n g) gs hj' hJ
        simp only [dropCount,hI,Nat.sub_zero]
        omega
      | succ i =>
        have hi' : i < gs.length := by simpa using hi
        have hI : (((gs.take i).foldl (State.compile n) (s.compile n g)).simplified gs[i]).cost = 0 := by
          simpa [List.take_succ_cons,List.foldl_cons] using hFoldI
        have h2 := ih i j (s.compile n g) hi' hj' (by omega) hI hJ
        simp only [dropCount]
        omega

theorem compile_budget_13 (n i j : Nat) (s : State) (gs : List Gate)
    (hempty : s.gates = []) (h15 : gs.length ≤ 15) (hi : i < gs.length)
    (hj : j < gs.length) (hij : i < j)
    (hFoldI : (((gs.take i).foldl (State.compile n) s).simplified gs[i]).cost = 0)
    (hFoldJ : (((gs.take j).foldl (State.compile n) s).simplified gs[j]).cost = 0) :
    (gs.foldl (State.compile n) s).gates.length ≤ 13 := by
  have h2 := compile_drops_two n i j s gs hi hj hij hFoldI hFoldJ
  have hq := count_conservation n s gs
  rw [hempty] at hq
  simp at hq
  omega

def finput (n pin : Nat) : Nat → Ref := fun i =>
  if i = pin then .literal false else if i < pin then .wire i else .wire (i-1)

def initial (n pin : Nat) : State :=
  ⟨(List.range (n + 1)).map (finput n pin), []⟩

def pinFalse (x : List Bool) (pin : Nat) : List Bool :=
  x.take pin ++ false :: x.drop pin

theorem initial_sim (x : List Bool) (pin : Nat) (hp : pin ≤ x.length) :
    Sim (initial x.length pin) x (pinFalse x pin) := by
  have ht : (x.take pin).length = pin := by simpa [Nat.min_eq_left hp]
  have hd : (x.drop pin).length = x.length - pin := List.length_drop
  have hlen : (pinFalse x pin).length = x.length + 1 := by
    simp [pinFalse, ht, hd]; omega
  refine ⟨by simp [initial,hlen], ?_, ?_⟩
  · intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    have hi' := List.mem_range.mp hi
    change (finput x.length pin i).bounded x.length
    unfold finput
    split
    · trivial
    · split
      · simp only [Ref.bounded]; omega
      · simp only [Ref.bounded]; omega
  · intro i
    change (getRef (initial x.length pin).refs i).eval (lut x) = lut (pinFalse x pin) i
    by_cases hi : i < x.length + 1
    · have href : getRef (initial x.length pin).refs i = finput x.length pin i := by
        simp [getRef,List.getD_eq_getElem?_getD,List.getElem?_range hi,initial]
      rw [href]
      rcases Nat.lt_trichotomy i pin with hlt|rfl|hlt
      · have htake : i < (x.take pin).length := by simpa only [ht] using hlt
        rw [show lut (pinFalse x pin) i = lut (x.take pin) i from lut_append_left htake]
        simp [finput, hlt, Nat.ne_of_lt hlt, Ref.eval, lut, List.getD_eq_getElem?_getD, List.getElem?_take]
      · simp [finput, Ref.eval, lut, pinFalse, List.getD_eq_getElem?_getD, ht,
          List.getElem?_append_right]
      · have hne : i ≠ pin := by omega
        have hge : (x.take pin).length ≤ i := by omega
        have hsub : i - pin ≠ 0 := by omega
        have ht0 : i - pin - 1 + pin = i-1 := by omega
        simp [finput, hne, Nat.not_lt_of_ge (Nat.le_of_lt hlt), Ref.eval, lut, pinFalse,
          List.getD_eq_getElem?_getD, List.getElem?_append_right hge, ht,
          List.getElem?_cons, hsub, List.getElem?_drop, ht0, Nat.add_comm pin]
    · have hf : (initial x.length pin).refs.length ≤ i := by
        simp only [initial,List.length_map,List.length_range]; omega
      have hw : (pinFalse x pin).length ≤ i := by omega
      simp only [getRef,lut,List.getD_eq_getElem?_getD,List.getElem?_eq_none_iff.mpr hf,
        List.getElem?_eq_none_iff.mpr hw,Option.getD_none,Ref.eval]

theorem pin4_sim_all (gs : List Gate) (x : List Bool) (hx : x.length = 8)
    (hg : ∀ g ∈ gs, g.2.length ≤ 2) :
    Sim (gs.foldl (State.compile 8) (initial 8 4)) x
      (gs.foldl Gate.step (pinFalse x 4)) := by
  have h := sim_all (gs := gs) (initial_sim x 4 (by omega)) hg
  simpa [hx] using h

theorem compile_refs (s : State) (n : Nat) (g : Gate) :
    (s.compile n g).refs = s.refs ++ [((s.simplified g).emit (n+s.gates.length)).2] := rfl

theorem getRef_append_left {rs zs : List Ref} {i : Nat} (hi : i < rs.length) :
    getRef (rs ++ zs) i = getRef rs i := by
  simp only [getRef,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem getRef_append_here (rs : List Ref) (r : Ref) :
    getRef (rs ++ [r]) rs.length = r := by
  simp [getRef,List.getD_eq_getElem?_getD]

theorem compile_ref_length (s : State) (n : Nat) (gs : List Gate) :
    ((gs.foldl (State.compile n) s).refs).length = s.refs.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih,compile_refs,List.length_append,List.length_cons]
    simp; omega

theorem compile_ref_keep (s : State) (n : Nat) (gs : List Gate) (i : Nat)
    (hi : i < s.refs.length) : getRef (gs.foldl (State.compile n) s).refs i = getRef s.refs i := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (s.compile n g) (by simp [compile_refs]; omega),compile_refs,getRef_append_left hi]

theorem pin4_is_false (gs : List Gate) :
    getRef (gs.foldl (State.compile 8) (initial 8 4)).refs 4 = .literal false := by
  rw [compile_ref_keep _ _ _ _ (by decide)]
  rfl

theorem ctrl_fold_false (s : State) (g : Gate) (a : Nat)
    (hp : getRef s.refs 4 = .literal false) (hOp : g.1 = .conj)
    (hIn : g.2 = [4,a] ∨ g.2 = [a,4]) :
    s.simplified g = .reuse (.literal false) := by
  rcases hIn with h|h <;>
    simp only [State.simplified,hOp,h,List.map_cons,List.map_nil,hp,foldGate] <;>
    cases hx : getRef s.refs a with
    | wire i => rfl
    | literal b => cases b <;> rfl

def Uses (g : Gate) (i : Nat) : Prop :=
  if g.1 = .neg then g.2.head? = some i else i ∈ g.2

theorem consumes_false (s : State) (g : Gate) (i : Nat) (hAr : g.2.length ≤ 2)
    (hUse : Uses g i) (hf : getRef s.refs i = .literal false) :
    (s.simplified g).cost = 0 := by
  rcases g with ⟨o,l⟩
  rcases l with _|⟨a,l⟩
  · cases o <;> simp [Uses] at hUse
  rcases l with _|⟨b,l⟩
  · have ha : a = i := by cases o <;> simpa [Uses,eq_comm] using hUse
    subst a
    cases o <;> simp [State.simplified,hf,foldGate,Code.cost,invert]
  have hn : l = [] :=
    List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hAr; omega)
  subst l
  cases o with
  | neg =>
    have ha : a = i := by simpa [Uses] using hUse
    subst a
    simp [State.simplified,hf,foldGate,pair,invert,Code.cost]
  | conj =>
    have h : a = i ∨ b = i := by simpa [Uses,eq_comm] using hUse
    rcases h with rfl | rfl
    · simpa only [State.simplified,List.map_cons,List.map_nil,hf] using
        (consumer_cost .conj (getRef s.refs b)).1
    · simpa only [State.simplified,List.map_cons,List.map_nil,hf] using
        (consumer_cost .conj (getRef s.refs a)).2 (by decide)
  | disj =>
    have h : a = i ∨ b = i := by simpa [Uses,eq_comm] using hUse
    rcases h with rfl | rfl
    · simpa only [State.simplified,List.map_cons,List.map_nil,hf] using
        (consumer_cost .disj (getRef s.refs b)).1
    · simpa only [State.simplified,List.map_cons,List.map_nil,hf] using
        (consumer_cost .disj (getRef s.refs a)).2 (by decide)

theorem false_at_after_ctrl (gs : List Gate) (i : Nat) (hi : i < gs.length) (a : Nat)
    (hOp : gs[i].1 = .conj) (hIn : gs[i].2 = [4,a] ∨ gs[i].2 = [a,4]) :
    getRef ((gs.take (i+1)).foldl (State.compile 8) (initial 8 4)).refs (9+i) =
      .literal false := by
  let s := (gs.take i).foldl (State.compile 8) (initial 8 4)
  have htake : gs.take (i+1) = gs.take i ++ [gs[i]] := List.take_succ_eq_append_getElem hi
  rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil,compile_refs]
  change getRef (s.refs ++ [((s.simplified gs[i]).emit (8+s.gates.length)).2]) (9+i) = _
  have hn : s.refs.length = 9+i := by
    simp [s,compile_ref_length,initial,Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [← hn,getRef_append_here,ctrl_fold_false s gs[i] a (pin4_is_false _) hOp hIn]
  rfl

theorem pin4_budget_13 (gs : List Gate) (i j a : Nat) (hi : i < gs.length)
    (hj : j < gs.length) (hij : i < j) (h15 : gs.length ≤ 15)
    (hOp : gs[i].1 = .conj) (hIn : gs[i].2 = [4,a] ∨ gs[i].2 = [a,4])
    (hUse : Uses gs[j] (9+i)) (hAr : gs[j].2.length ≤ 2) :
    (gs.foldl (State.compile 8) (initial 8 4)).gates.length ≤ 13 := by
  have h0 := ctrl_fold_false ((gs.take i).foldl (State.compile 8) (initial 8 4))
    gs[i] a (pin4_is_false _) hOp hIn
  have h1 := false_at_after_ctrl gs i hi a hOp hIn
  have htake : (gs.take j).take (i+1) = gs.take (i+1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hsplit :
      gs.take j = gs.take (i+1) ++ (gs.take j).drop (i+1) := by
    have h := (List.take_append_drop (i+1) (gs.take j)).symm
    simpa only [htake] using h
  let st := (gs.take (i+1)).foldl (State.compile 8) (initial 8 4)
  have hn : 9+i < st.refs.length := by
    simp [st,compile_ref_length,initial,Nat.min_eq_left (Nat.succ_le_of_lt hi)]
  have hf : getRef ((gs.take j).foldl (State.compile 8) (initial 8 4)).refs (9+i) =
    .literal false := by
    rw [hsplit,List.foldl_append]
    exact (compile_ref_keep st 8 _ (9+i) hn).trans h1
  exact compile_budget_13 8 i j (initial 8 4) gs rfl h15 hi hj hij
    (by rw [h0]; rfl) (consumes_false _ _ _ hAr hUse hf)

def SameExcept (w v : List Bool) (p q : Nat) : Prop :=
  w.length = v.length ∧ ∀ i, i ≠ p → i ≠ q → lut w i = lut v i

theorem lut_oob {w : List Bool} {i : Nat} (hi : w.length ≤ i) : lut w i = false := by
  simp [lut,List.getD_eq_getElem?_getD,List.getElem?_eq_none_iff.mpr hi]

theorem append_agreement {w v : List Bool} {p q : Nat} {a b : Bool}
    (h : SameExcept w v p q) (hnew : w.length = p ∨ w.length = q ∨ a = b) :
    SameExcept (w ++ [a]) (v ++ [b]) p q := by
  refine ⟨by simp [h.1],?_⟩
  intro i hp hq
  rcases Nat.lt_trichotomy i w.length with hi|hi|hi
  · have hiv : i < v.length := by simpa only [← h.1]
    rw [lut_append_left hi,lut_append_left hiv]
    exact h.2 i hp hq
  · subst i
    have he : a = b := (hnew.resolve_left hp).resolve_left hq
    have hv : lut (v ++ [b]) w.length = b := by rw [h.1, lut_append_here]
    rw [lut_append_here,hv,he]
  · have hiv : v.length < i := by simpa only [← h.1]
    rw [lut_append_past hi,lut_append_past hiv]

theorem sees_only (g : Gate) (w v : List Bool)
    (h : ∀ i, Uses g i → lut w i = lut v i) : g.value w = g.value v := by
  rcases g with ⟨o,ins⟩
  cases o with
  | conj =>
    unfold Gate.value
    congr 1
    apply List.map_congr_left
    intro b hb
    exact h b (by simpa [Uses] using hb)
  | disj =>
    unfold Gate.value
    congr 1
    apply List.map_congr_left
    intro b hb
    exact h b (by simpa [Uses] using hb)
  | neg =>
    cases ins with
    | nil => rfl
    | cons i is =>
      have hh := h i (by simp [Uses])
      simpa [Gate.value,Op.eval,hh]

theorem fold_unaware {p q : Nat} (gs : List Gate) (w v : List Bool)
    (h : SameExcept w v p q)
    (hp : ∀ g ∈ gs, ¬Uses g p)
    (hq : ∀ g ∈ gs, ¬Uses g q) :
    SameExcept (gs.foldl Gate.step w) (gs.foldl Gate.step v) p q := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    have he := sees_only g w v (fun r hr =>
      h.2 r (fun r_eq => hp g (by simp) (r_eq ▸ hr))
        (fun r_eq => hq g (by simp) (r_eq ▸ hr)))
    exact ih _ _ (append_agreement h (Or.inr (Or.inr he))) (by
      intro g hg
      exact hp g (by simp [hg])) (by
      intro g hg
      exact hq g (by simp [hg]))

theorem fold_future {p q : Nat} (gs : List Gate) (w v : List Bool)
    (h : SameExcept w v p q)
    (hp : ∀ g ∈ gs, ¬Uses g p)
    (hq : w.length + gs.length ≤ q) :
    SameExcept (gs.foldl Gate.step w) (gs.foldl Gate.step v) p q := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    have he := sees_only g w v fun r hr => by
      by_cases hh : r = q
      · subst r
        have ha : w.length ≤ q := by omega
        rw [lut_oob ha, lut_oob (by simpa only [← h.1])]
      · exact h.2 r (fun r_eq => hp g (by simp) (r_eq ▸ hr)) hh
    apply ih _ _ (append_agreement h (Or.inr (Or.inr he)))
    · intro g hg
      exact hp g (by simp [hg])
    · simp [Gate.step] at *
      omega

theorem use_mem_input (g : Gate) (r : Nat) (h : Uses g r) : r ∈ g.2 := by
  rcases g with ⟨o,xs⟩
  cases o <;> simp [Uses] at h
  · exact h
  · exact h
  · cases xs with
    | nil => simp at h
    | cons x xs =>
      simp only [List.head?_cons,Option.some.injEq] at h
      subst x
      exact List.mem_cons_self

theorem lut_fold_keep (gs : List Gate) (w : List Bool) (o : Nat) (ho : o < w.length) :
    lut (gs.foldl Gate.step w) o = lut w o := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (Gate.step w g) (by simp [Gate.step]; omega)]
    exact lut_append_left ho

theorem sensitive_needs_later_reader
    (gs : List Gate) (i out : Nat) (hi : i < gs.length)
    (only : ∀ j (hj : j < gs.length), 4 ∈ gs[j].2 → j = i)
    (a b : List Bool) (ha : a.length = 9) (hb : b.length = 9)
    (same : SameExcept a b 4 (9+i))
    (hout4 : out ≠ 4) (houtCtl : out ≠ 9+i)
    (vary : lut (gs.foldl Gate.step a) out ≠ lut (gs.foldl Gate.step b) out) :
    ∃ j, ∃ hj : j < gs.length, i < j ∧ Uses gs[j] (9+i) := by
  by_cases hr : ∃ j, ∃ hj : j < gs.length, i < j ∧ Uses gs[j] (9+i)
  · exact hr
  exfalso
  let pre := gs.take i
  let post := gs.drop (i+1)
  have hn : pre.length = i := by simp [pre,Nat.min_eq_left (Nat.le_of_lt hi)]
  have pre_no : ∀ g ∈ pre, ¬Uses g 4 := by
    intro g hg hu
    obtain ⟨j,hj,rr⟩ := List.mem_iff_getElem.mp hg
    have hj' : j < gs.length := by omega
    have he : pre[j] = gs[j] := List.getElem_take
    have hoff := only j hj' (he ▸ (rr ▸ use_mem_input g 4 hu))
    omega
  have hx := fold_future pre a b same pre_no (by omega)
  have hlen : (pre.foldl Gate.step a).length = 9+i := by rw [fold_length,ha,hn]
  have hy : SameExcept (Gate.step (pre.foldl Gate.step a) gs[i])
      (Gate.step (pre.foldl Gate.step b) gs[i]) 4 (9+i) :=
    append_agreement hx (Or.inr (Or.inl hlen))
  have post_no (r : Nat) (hCond : ∀ j (hj : j < gs.length), i < j → ¬Uses gs[j] r) :
      ∀ g ∈ post, ¬Uses g r := by
    intro g hg hu
    obtain ⟨j,hj,rr⟩ := List.mem_iff_getElem.mp hg
    have hn : post.length = gs.length - (i+1) := by simp [post]
    have had : i+1+j < gs.length := by omega
    have he : post[j] = gs[i+1+j] := List.getElem_drop
    exact hCond (i+1+j) had (by omega) (he ▸ (rr ▸ hu))
  have h4 : ∀ g ∈ post, ¬Uses g 4 := post_no 4 (fun j hj hgt hh => by
    have hn := only j hj (use_mem_input gs[j] 4 hh)
    omega)
  have h9 : ∀ g ∈ post, ¬Uses g (9+i) :=
    post_no (9+i) (fun j hj hgt hh => hr ⟨j,hj,hgt,hh⟩)
  have hh := (fold_unaware post _ _ hy h4 h9).2 out hout4 houtCtl
  apply vary
  have hsplit : gs = pre ++ [gs[i]] ++ post := by
    have h := (List.take_append_drop (i+1) gs).symm
    simpa only [List.take_succ_eq_append_getElem hi,pre,post] using h
  have ea := congrArg (fun l : List Gate => lut (l.foldl Gate.step a) out) hsplit
  have eb := congrArg (fun l : List Gate => lut (l.foldl Gate.step b) out) hsplit
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil] at ea eb
  exact ea.trans (hh.trans eb.symm)

theorem split_at_gate (gs : List Gate) (i : Nat) (hi : i < gs.length) :
    gs = gs.take i ++ [gs[i]] ++ gs.drop (i+1) := by
  have h := (List.take_append_drop (i+1) gs).symm
  simpa only [List.take_succ_eq_append_getElem hi] using h

theorem prefix_avoids_raw (gs : List Gate) (i : Nat) (hi : i < gs.length)
    (only : ∀ j (hj : j < gs.length), 4 ∈ gs[j].2 → j = i) :
    ∀ g ∈ gs.take i, ¬ Uses g 4 := by
  intro g hg h
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hg
  have ht : (gs.take i).length = i := by simp [Nat.min_eq_left (Nat.le_of_lt hi)]
  have hj' : j < gs.length := by omega
  have he' : (gs.take i)[j] = gs[j] := List.getElem_take
  have hh := only j hj' (he' ▸ (he ▸ use_mem_input g 4 h))
  omega

theorem suffix_avoids_raw (gs : List Gate) (i : Nat)
    (only : ∀ j (hj : j < gs.length), 4 ∈ gs[j].2 → j = i) :
    ∀ g ∈ gs.drop (i+1), ¬ Uses g 4 := by
  intro g hg h
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hg
  have ht : (gs.drop (i+1)).length = gs.length - (i+1) := by simp
  have hj' : i+1+j < gs.length := by omega
  have he' : (gs.drop (i+1))[j] = gs[i+1+j] := List.getElem_drop
  have hh := only (i+1+j) hj' (he' ▸ (he ▸ use_mem_input g 4 h))
  omega

theorem fold_split_at (gs : List Gate) (i : Nat) (hi : i < gs.length) (w : List Bool) :
    gs.foldl Gate.step w =
      (gs.drop (i+1)).foldl Gate.step (Gate.step ((gs.take i).foldl Gate.step w) gs[i]) := by
  have h := congrArg (fun l : List Gate => l.foldl Gate.step w) (split_at_gate gs i hi)
  simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using h

theorem ctrl_false_value (g : Gate) (w : List Bool) (a : Nat) (hOp : g.1 = .conj)
    (hIn : g.2 = [4,a] ∨ g.2 = [a,4]) (h : lut w 4 = false ∨ lut w a = false) :
    g.value w = false := by
  rcases hIn with hIn|hIn <;> rcases h with h|h <;> simp [Gate.value,hOp,hIn,Op.eval,h]

theorem vary_requires_control_true
    (gs : List Gate) (i out ctrl : Nat) (hi : i < gs.length)
    (only : ∀ j (hj : j < gs.length), 4 ∈ gs[j].2 → j = i)
    (hOp : gs[i].1 = .conj) (hIn : gs[i].2 = [4,ctrl] ∨ gs[i].2 = [ctrl,4])
    (hn : ctrl ≠ 4)
    (a b : List Bool) (same : SameExcept a b 4 4) (hout4 : out ≠ 4)
    (vary : lut (gs.foldl Gate.step a) out ≠ lut (gs.foldl Gate.step b) out) :
    lut ((gs.take i).foldl Gate.step a) ctrl = true := by
  by_cases ht : lut ((gs.take i).foldl Gate.step a) ctrl = true
  · exact ht
  have hx := fold_unaware (gs.take i) a b same
    (prefix_avoids_raw gs i hi only) (prefix_avoids_raw gs i hi only)
  have ha : lut ((gs.take i).foldl Gate.step a) ctrl = false :=
    Bool.eq_false_iff.mpr ht
  have hb : lut ((gs.take i).foldl Gate.step b) ctrl = false :=
    (hx.2 ctrl hn hn).symm.trans ha
  have hval : gs[i].value ((gs.take i).foldl Gate.step a) =
      gs[i].value ((gs.take i).foldl Gate.step b) :=
    (ctrl_false_value _ _ ctrl hOp hIn (Or.inr ha)).trans
      (ctrl_false_value _ _ ctrl hOp hIn (Or.inr hb)).symm
  have hmid : SameExcept (Gate.step ((gs.take i).foldl Gate.step a) gs[i])
      (Gate.step ((gs.take i).foldl Gate.step b) gs[i]) 4 4 :=
    append_agreement hx (Or.inr (Or.inr hval))
  have he := (fold_unaware (gs.drop (i+1)) _ _ hmid
    (suffix_avoids_raw gs i only) (suffix_avoids_raw gs i only)).2 out hout4 hout4
  exact False.elim (vary ((congrArg (fun l => lut l out) (fold_split_at gs i hi a)).trans
    (he.trans (congrArg (fun l => lut l out) (fold_split_at gs i hi b)).symm)))

theorem ctrl_is_prior (gs : List Gate) (i ctrl : Nat) (hi : i < gs.length) (a : List Bool)
    (ha : a.length = 9) (ht : lut ((gs.take i).foldl Gate.step a) ctrl = true) :
    ctrl < 9+i := by
  by_cases h : ctrl < 9+i
  · exact h
  have hn : ((gs.take i).foldl Gate.step a).length ≤ ctrl := by
    rw [fold_length,ha,List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  rw [lut_oob hn] at ht
  cases ht

def pete9 (w : List Bool) : Bool :=
  let x := lut w
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def pin4Only : List Bool := [false,false,false,false,true,false,false,false,false]
def edge1and2 : List Bool := [false,true,true,false,false,false,false,false,false]
def pin4SensitiveLo : List Bool := [true,false,false,false,false,false,false,false,false]
def pin4SensitiveHi : List Bool := [true,false,false,false,true,false,false,false,false]

theorem pin4_sensitive : pete9 pin4SensitiveLo ≠ pete9 pin4SensitiveHi := by decide
theorem pin4_agreement (q : Nat) : SameExcept pin4SensitiveLo pin4SensitiveHi 4 q := by
  refine ⟨rfl,?_⟩
  intro i h _
  have hr := Nat.lt_or_ge i 9
  rcases hr with hr|hr
  · have cs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases cs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · rw [lut_oob (show pin4SensitiveLo.length ≤ i from hr),
        lut_oob (show pin4SensitiveHi.length ≤ i from hr)]

theorem pete_not_pin4 (gs : List Gate) (out : Nat)
    (hEval : ∀ x : List Bool, x.length = 9 → lut (gs.foldl Gate.step x) out = pete9 x) :
    out ≠ 4 := by
  intro h; subst out
  have hc := hEval pin4Only rfl
  rw [lut_fold_keep gs pin4Only 4 (by decide)] at hc
  exact Bool.noConfusion hc

theorem pete_not_and_wire (gs : List Gate) (i out ctrl : Nat) (hi : i < gs.length)
    (hOp : gs[i].1 = .conj) (hIn : gs[i].2 = [4,ctrl] ∨ gs[i].2 = [ctrl,4])
    (hEval : ∀ x : List Bool, x.length = 9 → lut (gs.foldl Gate.step x) out = pete9 x) :
    out ≠ 9+i := by
  intro he; subst out
  let w := (gs.take i).foldl Gate.step edge1and2
  have hw : w.length = 9+i := by
    simp [w,fold_length,Nat.min_eq_left (Nat.le_of_lt hi),edge1and2]
  have hv : lut w 4 = false := by
    rw [lut_fold_keep _ edge1and2 _ (by decide)]
    rfl
  have hm : 9+i < (Gate.step w gs[i]).length := by simp [Gate.step,hw]
  have hh := hEval edge1and2 rfl
  rw [fold_split_at gs i hi edge1and2] at hh
  change lut ((gs.drop (i+1)).foldl Gate.step (Gate.step w gs[i])) (9+i) = pete9 edge1and2 at hh
  rw [lut_fold_keep _ _ _ hm,← hw] at hh
  change lut (w ++ [gs[i].value w]) w.length = pete9 edge1and2 at hh
  rw [lut_append_here,ctrl_false_value _ _ ctrl hOp hIn (Or.inl hv)] at hh
  exact Bool.noConfusion hh

theorem pete_compiles_to_13 (gs : List Gate) (i out ctrl : Nat) (hi : i < gs.length)
    (only : ∀ j (hj : j < gs.length), 4 ∈ gs[j].2 → j = i)
    (hOp : gs[i].1 = .conj) (hIn : gs[i].2 = [4,ctrl] ∨ gs[i].2 = [ctrl,4])
    (h15 : gs.length ≤ 15) (ha : ∀ g ∈ gs, g.2.length ≤ 2)
    (hEval : ∀ x : List Bool, x.length = 9 → lut (gs.foldl Gate.step x) out = pete9 x) :
    (gs.foldl (State.compile 8) (initial 8 4)).gates.length ≤ 13 := by
  have out4 := pete_not_pin4 gs out hEval
  have outI := pete_not_and_wire gs i out ctrl hi hOp hIn hEval
  have vary : lut (gs.foldl Gate.step pin4SensitiveLo) out ≠
      lut (gs.foldl Gate.step pin4SensitiveHi) out := by
    rw [hEval _ rfl,hEval _ rfl]; exact pin4_sensitive
  obtain ⟨j,hj,hij,heff⟩ := sensitive_needs_later_reader gs i out hi only
    pin4SensitiveLo pin4SensitiveHi rfl rfl (pin4_agreement _) out4 outI vary
  exact pin4_budget_13 gs i j ctrl hi hj hij h15 hOp hIn heff
    (ha gs[j] (List.getElem_mem hj))

theorem ref_from_gate (gs : List Gate) (n idx : Nat) (s : State) (hi : idx < gs.length) :
    getRef (gs.foldl (State.compile n) s).refs (s.refs.length+idx) =
      let st := (gs.take idx).foldl (State.compile n) s
      ((st.simplified gs[idx]).emit (n+st.gates.length)).2 := by
  let st := (gs.take idx).foldl (State.compile n) s
  have ht : st.refs.length = s.refs.length+idx := by
    simp [st,compile_ref_length,Nat.min_eq_left (Nat.le_of_lt hi)]
  have hn : s.refs.length+idx < (st.compile n gs[idx]).refs.length := by
    rw [compile_refs,List.length_append,ht]; simp
  have h : gs.foldl (State.compile n) s =
      (gs.drop (idx+1)).foldl (State.compile n) (st.compile n gs[idx]) := by
    have ee := congrArg (fun a : List Gate => a.foldl (State.compile n) s) (split_at_gate gs idx hi)
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,st] using ee
  rw [h,compile_ref_keep _ _ _ _ hn,compile_refs,←ht,getRef_append_here]

theorem emit_literal_cost_zero (n : Nat) (c : Code) (b : Bool) (h : (c.emit n).2 = .literal b) :
    c.cost = 0 := by
  cases c with
  | reuse _ => rfl
  | mono _ _ => cases h
  | bin _ _ _ => cases h

theorem compile_drops_three (n k i j : Nat) (s : State) (gs : List Gate)
    (hk : k < gs.length) (hi : i < gs.length) (hj : j < gs.length) (hki : k < i) (hij : i < j)
    (hFoldK : (((gs.take k).foldl (State.compile n) s).simplified gs[k]).cost = 0)
    (hFoldI : (((gs.take i).foldl (State.compile n) s).simplified gs[i]).cost = 0)
    (hFoldJ : (((gs.take j).foldl (State.compile n) s).simplified gs[j]).cost = 0) :
    3 ≤ dropCount n s gs := by
  induction gs generalizing s k i j with
  | nil => simp at hk
  | cons g gs ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero => omega
      | succ i =>
        have hi' : i < gs.length := by simpa using hi
        have hj' : j < gs.length := by simpa using hj
        have hI : (((gs.take i).foldl (State.compile n) (s.compile n g)).simplified gs[i]).cost = 0 := by
          simpa [List.take_succ_cons,List.foldl_cons] using hFoldI
        have hJ : (((gs.take j).foldl (State.compile n) (s.compile n g)).simplified gs[j]).cost = 0 := by
          simpa [List.take_succ_cons,List.foldl_cons] using hFoldJ
        cases k with
        | zero =>
          have hK : (s.simplified g).cost = 0 := by simpa using hFoldK
          have h3 := compile_drops_two n i j (s.compile n g) gs hi' hj' (by omega) hI hJ
          simp only [dropCount,hK,Nat.sub_zero]
          omega
        | succ k =>
          have hk' : k < gs.length := by simpa using hk
          have hK : (((gs.take k).foldl (State.compile n) (s.compile n g)).simplified gs[k]).cost = 0 := by
            simpa [List.take_succ_cons,List.foldl_cons] using hFoldK
          have h3 := ih k i j (s.compile n g) hk' hi' hj' (by omega) (by omega) hK hI hJ
          simp only [dropCount]
          omega

theorem ctrl_false_persist (gs : List Gate) (i j a : Nat) (hi : i < gs.length) (hij : i < j)
    (hop : gs[i].1 = .conj) (hIn : gs[i].2 = [4,a] ∨ gs[i].2 = [a,4]) :
    getRef ((gs.take j).foldl (State.compile 8) (initial 8 4)).refs (9+i) = .literal false := by
  have h1 := false_at_after_ctrl gs i hi a hop hIn
  have ht : (gs.take j).take (i+1) = gs.take (i+1) := by
    rw [List.take_take,Nat.min_eq_left (by omega)]
  have hsplit : gs.take j = gs.take (i+1) ++ (gs.take j).drop (i+1) := by
    simpa only [ht] using (List.take_append_drop (i+1) (gs.take j)).symm
  let st := (gs.take (i+1)).foldl (State.compile 8) (initial 8 4)
  have hn : 9+i < st.refs.length := by
    simp [st,compile_ref_length,initial,Nat.min_eq_left (Nat.succ_le_of_lt hi)]
  rw [hsplit,List.foldl_append]
  exact (compile_ref_keep st 8 _ (9+i) hn).trans h1

theorem literal_ctrl_saves_spare (gs : List Gate) (k i j : Nat)
    (hk : k < gs.length) (hi : i < gs.length) (hj : j < gs.length) (hki : k < i) (hij : i < j)
    (h15 : gs.length ≤ 15) (hop : gs[i].1 = .conj)
    (hIn : gs[i].2 = [4,9+k] ∨ gs[i].2 = [9+k,4])
    (hUse : Uses gs[j] (9+i)) (hAr : gs[j].2.length ≤ 2)
    (hlit : getRef (gs.foldl (State.compile 8) (initial 8 4)).refs (9+k) = .literal true) :
    (gs.foldl (State.compile 8) (initial 8 4)).gates.length ≤ 12 := by
  have hFoldI := ctrl_fold_false ((gs.take i).foldl (State.compile 8) (initial 8 4))
    gs[i] (9+k) (pin4_is_false _) hop hIn
  have hFoldJ := consumes_false _ gs[j] (9+i) hAr hUse (ctrl_false_persist gs i j (9+k) hi hij hop hIn)
  have hr := ref_from_gate gs 8 k (initial 8 4) hk
  have hconst : getRef (gs.foldl (State.compile 8) (initial 8 4)).refs (9+k) =
      let st := (gs.take k).foldl (State.compile 8) (initial 8 4)
      ((st.simplified gs[k]).emit (8+st.gates.length)).2 := hr
  rw [hlit] at hconst
  have hFoldK := emit_literal_cost_zero _ _ _ hconst.symm
  have hb := compile_drops_three 8 k i j (initial 8 4) gs hk hi hj hki hij hFoldK
    (by rw [hFoldI];rfl) hFoldJ
  have hq := count_conservation 8 (initial 8 4) gs
  have hnil : (initial 8 4).gates.length = 0 := rfl
  rw [hnil,Nat.zero_add] at hq
  omega

def pinTrue (x : List Bool) (pin : Nat) : List Bool :=
  x.take pin ++ true :: x.drop pin

theorem pin_pair (x : List Bool) (p : Nat) (hp : p ≤ x.length) :
    (pinFalse x p).length = x.length+1 ∧ (pinTrue x p).length = x.length+1 ∧
      SameExcept (pinFalse x p) (pinTrue x p) p p := by
  have htake : (x.take p).length = p := by simp [Nat.min_eq_left hp]
  have hlen : ∀ v : Bool, (x.take p ++ v :: x.drop p).length = x.length+1 := by
    intro v
    simp [htake]; omega
  refine ⟨hlen false,hlen true,(hlen false).trans (hlen true).symm,?_⟩
  intro j hj _
  rcases Nat.lt_or_ge j p with hp'|hp'
  · have hj' : j < (x.take p).length := by omega
    unfold pinFalse pinTrue
    rw [lut_append_left hj',lut_append_left hj']
  · have hge : (x.take p).length ≤ j := by omega
    have hne : j-p ≠ 0 := by omega
    simp [pinTrue,pinFalse,lut,List.getD_eq_getElem?_getD,List.getElem?_append_right hge,
      List.getElem?_cons,htake,hne]

theorem control_full_from_prefix (gs : List Gate) (i r : Nat) (hi : i < gs.length)
    (w : List Bool) (h : r < ((gs.take i).foldl Gate.step w).length) :
    lut (gs.foldl Gate.step w) r = lut ((gs.take i).foldl Gate.step w) r := by
  rw [fold_split_at gs i hi]
  have hs : r < (Gate.step ((gs.take i).foldl Gate.step w) gs[i]).length := by
    simp [Gate.step]; omega
  rw [lut_fold_keep _ _ _ hs]
  exact lut_append_left h

theorem emit_arity (n : Nat) (c : Code) : ∀ g ∈ (c.emit n).1, g.2.length ≤ 2 := by
  cases c <;> simp [Code.emit]
  all_goals (intro g hg; subst g; decide)

theorem compiled_arity (s : State) (n : Nat) (gs : List Gate)
    (h : ∀ g ∈ s.gates, g.2.length ≤ 2) :
    ∀ g ∈ (gs.foldl (State.compile n) s).gates, g.2.length ≤ 2 := by
  induction gs generalizing s with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro g' hg
    change g' ∈ s.gates ++ ((s.simplified g).emit (n+s.gates.length)).1 at hg
    rcases List.mem_append.mp hg with hOld|hNew
    · exact h g' hOld
    · exact emit_arity _ _ g' hNew

theorem local_child9163 (gs : List Gate) (i out ctrl : Nat) (hi : i < gs.length)
    (only : ∀ j (hj : j < gs.length), 4 ∈ gs[j].2 → j = i)
    (hOp : gs[i].1 = .conj) (hIn : gs[i].2 = [4,ctrl] ∨ gs[i].2 = [ctrl,4])
    (hctrl : 9 ≤ ctrl) (h15 : gs.length ≤ 15) (ha : ∀ g ∈ gs, g.2.length ≤ 2)
    (hEval : ∀ x : List Bool, x.length = 9 → lut (gs.foldl Gate.step x) out = pete9 x) :
    ∃ ds : List Gate, ∃ out' ctrl' : Nat,
      (∀ g ∈ ds, g.2.length ≤ 2) ∧ ds.length ≤ 13 ∧
      (∀ x : List Bool, x.length = 8 → lut (ds.foldl Gate.step x) out' = pete9 (pinFalse x 4)) ∧
      ∀ x : List Bool, x.length = 8 → pete9 (pinFalse x 4) = false →
        pete9 (pinTrue x 4) = true → lut (ds.foldl Gate.step x) ctrl' = true := by
  let st := gs.foldl (State.compile 8) (initial 8 4)
  have har : ∀ g ∈ st.gates, g.2.length ≤ 2 :=
    compiled_arity (initial 8 4) 8 gs (by simp [initial])
  have hb : st.gates.length ≤ 13 := pete_compiles_to_13 gs i out ctrl hi only hOp hIn h15 ha hEval
  have hout4 := pete_not_pin4 gs out hEval
  have houtI := pete_not_and_wire gs i out ctrl hi hOp hIn hEval
  have vary : lut (gs.foldl Gate.step pin4SensitiveLo) out ≠
      lut (gs.foldl Gate.step pin4SensitiveHi) out := by
    rw [hEval _ rfl,hEval _ rfl]; exact pin4_sensitive
  obtain ⟨j,hj,hij,heff⟩ := sensitive_needs_later_reader gs i out hi only
    pin4SensitiveLo pin4SensitiveHi rfl rfl (pin4_agreement _) hout4 houtI vary
  have hne : ctrl ≠ 4 := by omega
  have hprior := ctrl_is_prior gs i ctrl hi pin4SensitiveLo rfl
    (vary_requires_control_true gs i out ctrl hi only hOp hIn hne
      pin4SensitiveLo pin4SensitiveHi (pin4_agreement _) hout4 vary)
  have outSem (x : List Bool) (hx : x.length = 8) :
      (getRef st.refs out).eval (lut (st.gates.foldl Gate.step x)) =
        pete9 (pinFalse x 4) := by
    exact ((pin4_sim_all gs x hx ha).2.2 out).trans (hEval _ (by
      have h := (pin_pair x 4 (by omega)).1
      omega))
  have ctrlSem (x : List Bool) (hx : x.length = 8) (hl : pete9 (pinFalse x 4) = false)
      (hh : pete9 (pinTrue x 4) = true) :
      (getRef st.refs ctrl).eval (lut (st.gates.foldl Gate.step x)) = true := by
    obtain ⟨hl9,hh9,hsame⟩ := pin_pair x 4 (by omega)
    have h1 : (pinFalse x 4).length = 9 := by omega
    have h2 : (pinTrue x 4).length = 9 := by omega
    have hd : lut (gs.foldl Gate.step (pinFalse x 4)) out ≠
        lut (gs.foldl Gate.step (pinTrue x 4)) out := by
      rw [hEval _ h1,hEval _ h2,hl,hh]; decide
    have h3 : ctrl < ((gs.take i).foldl Gate.step (pinFalse x 4)).length := by
      rw [fold_length,h1,List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
      exact hprior
    exact ((pin4_sim_all gs x hx ha).2.2 ctrl).trans
      ((control_full_from_prefix gs i ctrl hi _ h3).trans
      (vary_requires_control_true gs i out ctrl hi only hOp hIn hne _ _ hsame hout4 hd))
  cases ho : getRef st.refs out with
  | literal b =>
    have low := outSem (List.replicate 8 false) rfl
    have high := outSem [false,true,true,false,false,false,false,false] rfl
    rw [ho] at low high
    change b = false at low
    change b = true at high
    simp_all
  | wire o =>
    have outGood : ∀ x : List Bool, x.length = 8 → lut (st.gates.foldl Gate.step x) o =
        pete9 (pinFalse x 4) := by
      intro x hx
      have h := outSem x hx
      rwa [ho] at h
    have hob : (Ref.wire o).bounded ((st.gates.foldl Gate.step (List.replicate 8 false)).length) := by
      have h := getRef_bounded st.refs (pin4_sim_all gs (List.replicate 8 false) rfl ha).2.1 out
      rwa [ho] at h
    have hood : o < 8+st.gates.length := by simpa [Ref.bounded,fold_length] using hob
    cases hc : getRef st.refs ctrl with
    | wire r =>
      refine ⟨st.gates,o,r,har,hb,outGood,?_⟩
      intro x hx hl hh
      have h := ctrlSem x hx hl hh
      rwa [hc] at h
    | literal b =>
      have h := ctrlSem [true,false,false,false,false,false,false,false] rfl (by decide) (by decide)
      rw [hc] at h
      change b = true at h
      subst b
      let k := ctrl - 9
      have hk : k < gs.length := by omega
      have hki : k < i := by omega
      have hce : 9+k = ctrl := by omega
      have hs : st.gates.length ≤ 12 := literal_ctrl_saves_spare gs k i j hk hi hj hki hij
        h15 hOp (by rwa [hce]) heff (ha gs[j] (List.getElem_mem hj)) (by rwa [hce])
      refine ⟨st.gates ++ [(.conj,[])],o,8+st.gates.length,?_,by simp; omega,?_,?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hh|hh
        · exact har g hh
        · simp at hh
          subst g; decide
      · intro x hx
        rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
        have hlen : (st.gates.foldl Gate.step x).length = 8+st.gates.length := by rw [fold_length,hx]
        change lut ((st.gates.foldl Gate.step x) ++ [_]) o = pete9 (pinFalse x 4)
        rw [lut_append_left (by rw [hlen]; exact hood)]
        exact outGood x hx
      · intro x hx _ _
        rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
        have hlen : (st.gates.foldl Gate.step x).length = 8+st.gates.length := by rw [fold_length,hx]
        rw [← hlen]
        exact lut_append_here _ true

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def fromGate (g : PEqualNP.CircuitLowerBounds.Gate) : Gate :=
  (match g.op with
    | .and => .conj
    | .or => .disj
    | .not => .neg
    | _ => .disj, g.inputs)

def toGate (g : Gate) : PEqualNP.CircuitLowerBounds.Gate :=
  ⟨match g.1 with | .conj => .and | .disj => .or | .neg => .not, g.2⟩

theorem from_op_ok (g : PEqualNP.CircuitLowerBounds.Gate)
    (h : g.op ∈ [GateOp.and,GateOp.or,GateOp.not]) (w : List Bool) :
    Gate.step w (fromGate g) =
      w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))] := by
  cases g with | mk op inputs =>
  cases op <;> try { simp at h }
  all_goals try rfl
  case not =>
    cases inputs <;> rfl

theorem from_wires (C : Circuit) (hC : FanInTwo C) (w : List Bool) :
    (C.gates.map fromGate).foldl Gate.step w = C.wires w := by
  unfold Circuit.wires
  have h : ∀ g ∈ C.gates, g.op ∈ [GateOp.and,GateOp.or,GateOp.not] :=
    fun g hg => by simpa using (hC _ hg).1
  generalize C.gates = gs at h ⊢
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [from_op_ok g (h g (by simp))]
    exact ih _ (fun g hg => h g (by simp [hg]))

theorem to_wires (gs : List Gate) (o : Nat) (w : List Bool) :
    (Circuit.mk (gs.map toGate) o).wires w = gs.foldl Gate.step w := by
  unfold Circuit.wires
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [ih]
    congr 1
    rcases g with ⟨o,is⟩
    cases o <;> try rfl
    case neg => cases is <;> rfl

theorem to_fanIn (gs : List Gate) (o : Nat) (h : ∀ g ∈ gs, g.2.length ≤ 2) :
    FanInTwo (Circuit.mk (gs.map toGate) o) := by
  intro g hg
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
  rcases p with ⟨op,is⟩
  refine ⟨?_,h _ hp⟩
  cases op <;> simp [toGate]

def peteFin (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

theorem FinRead9 (f : Fin 9 → Bool) (i : Nat) (hi : i < 9) :
    lut (List.ofFn f) i = f ⟨i,hi⟩ := by
  simp only [lut, List.getD_eq_getElem?_getD, List.getElem?_ofFn,dite_eq_left hi,Option.getD_some]

theorem peteFin_eq (f : Fin 9 → Bool) : pete9 (List.ofFn f) = peteFin f := by
  unfold pete9 peteFin
  repeat rw [FinRead9 _ _ (by decide)]
  rfl

def ofList9 (w : List Bool) (hw : w.length = 9) (i : Fin 9) : Bool :=
  w[i.val]'(hw.symm ▸ i.isLt)

theorem ofList9_eq (w : List Bool) (hw : w.length = 9) :
    List.ofFn (ofList9 w hw) = w := by
  apply List.ext_getElem (List.length_ofFn.trans hw.symm)
  intro i hi hi'
  rw [List.getElem_ofFn]
  rfl

theorem list_insert4 (f : Fin 8 → Bool) (b : Bool) :
    List.ofFn (Fin.insertNth (4 : Fin 9) b f) =
      (List.ofFn f).take 4 ++ b :: (List.ofFn f).drop 4 := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hi' : i < 9 := by simpa using hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem exactProof : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x2.size), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (15 : ℕ) → (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x7 : Fin x2.size), (4 : ℕ) ∈ (x2.gates.get x7).inputs ↔ x7 = x3) → ∀ (x8 : ℕ), (9 : ℕ) ≤ x8 → (x2.gates.get x3).inputs = [(4 : ℕ), x8] ∨ (x2.gates.get x3).inputs = [x8, (4 : ℕ)] → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size ≤ (13 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x12 = fun (x14 : Fin (8 : ℕ) → Bool) => x1 (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x14)) ∧ ∀ (x14 : Fin (8 : ℕ) → Bool), x1 (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x14) = Bool.false → x1 (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.true x14) = Bool.true → (x12.wires (List.ofFn x14)).getD x13 Bool.false = Bool.true := by
  dsimp only
  intro C i hFan hsize hop hun ctrl hctrl hArgs hFn
  let gs := C.gates.map fromGate
  have hlen : gs.length = C.size := by simp [gs,Circuit.size]
  have hi : i.val < gs.length := by rw [hlen]; exact i.isLt
  have h4 : ∀ j (hj : j < gs.length), 4 ∈ gs[j].2 → j = i.val := by
    intro j hj hh
    let j' : Fin C.size := ⟨j, by simpa [hlen] using hj⟩
    have hy : 4 ∈ (C.gates.get j').inputs := by
      change 4 ∈ C.gates[j].inputs
      simpa [gs,fromGate] using hh
    exact congrArg Fin.val ((hun j').mp hy)
  have ho : gs[i.val].1 = .conj := by
    simp [gs,fromGate,show C.gates[i.val] = C.gates.get i from rfl,hop]
  have ha : gs[i.val].2 = [4,ctrl] ∨ gs[i.val].2 = [ctrl,4] := by
    simpa [gs,fromGate,show C.gates.get i = C.gates[i.val] from rfl] using hArgs
  have hAr : ∀ g ∈ gs, g.2.length ≤ 2 := by
    intro g hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    exact (hFan g' hg').2
  have hEval (xs : List Bool) (hx : xs.length = 9) :
      lut (gs.foldl Gate.step xs) C.output = pete9 xs := by
    have h := congrFun hFn (ofList9 xs hx)
    change C.eval (List.ofFn (ofList9 xs hx)) = peteFin (ofList9 xs hx) at h
    rw [← peteFin_eq,ofList9_eq] at h
    rw [from_wires C hFan]
    exact h
  obtain ⟨ds,o,z,hD,hlD,hd,hz⟩ :=
    local_child9163 gs i.val C.output ctrl hi h4 ho ha hctrl (by simpa [hlen]) hAr hEval
  refine ⟨Circuit.mk (ds.map toGate) o,z,to_fanIn ds o hD,by simpa [Circuit.size],?_,?_⟩
  · funext y
    change lut ((Circuit.mk (ds.map toGate) o).wires (List.ofFn y)) o =
      peteFin (Fin.insertNth (4 : Fin 9) false y)
    rw [to_wires,← peteFin_eq,list_insert4]
    exact hd _ List.length_ofFn
  · intro y hlo hhi
    change peteFin (Fin.insertNth (4 : Fin 9) false y) = false at hlo
    change peteFin (Fin.insertNth (4 : Fin 9) true y) = true at hhi
    change lut ((Circuit.mk (ds.map toGate) o).wires (List.ofFn y)) z = true
    rw [to_wires]
    rw [← peteFin_eq,list_insert4] at hlo hhi
    exact hz _ List.length_ofFn hlo hhi

end PEqualNP.Outside.L_meta_9163

theorem PEqualNP.Outside.L_meta_9163 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x2.size), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (15 : ℕ) → (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x7 : Fin x2.size), (4 : ℕ) ∈ (x2.gates.get x7).inputs ↔ x7 = x3) → ∀ (x8 : ℕ), (9 : ℕ) ≤ x8 → (x2.gates.get x3).inputs = [(4 : ℕ), x8] ∨ (x2.gates.get x3).inputs = [x8, (4 : ℕ)] → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size ≤ (13 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x12 = fun (x14 : Fin (8 : ℕ) → Bool) => x1 (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x14)) ∧ ∀ (x14 : Fin (8 : ℕ) → Bool), x1 (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x14) = Bool.false → x1 (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.true x14) = Bool.true → (x12.wires (List.ofFn x14)).getD x13 Bool.false = Bool.true :=
  PEqualNP.Outside.L_meta_9163.exactProof
