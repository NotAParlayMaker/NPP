import Mathlib
import PEqualNP.Defs

/-!
# Gap L-meta-174: the last input costs at most one gate

For `f` on `n` inputs let `F` be the function on `n + 1` inputs that applies `f` to the
first `n` bits and ANDs the result with the last bit. Fixing the last input to `true`
gives `f` back, so a circuit for `f` lifts to one for `F` by adding a single AND gate.
Conversely, gate elimination on the last input removes one gate. Together: `F` has a
circuit of size `s + 1` exactly when `f` has one of size `s`.
-/

namespace PEqualNP.Outside.L_meta_174_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Run gates on a wire list (the fold inside `Circuit.wires`). -/
def wiresF (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresF C.gates x := rfl

theorem wiresF_append (gs gs' : List Gate) (w : List Bool) :
    wiresF (gs ++ gs') w = wiresF gs' (wiresF gs w) := by
  simp [wiresF, List.foldl_append]

theorem wiresF_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresF gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresF], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresF (g :: gs) w
        = wiresF gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresF (gs : List Gate) (w : List Bool) :
    (wiresF gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresF_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresF (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresF gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresF_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

/-- The allowed gates: AND, OR, NOT with at most two reads. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hl : j < L.length
  · rw [List.getD_append _ _ _ _ hl]
  · have h4 : (L ++ [S]).length ≤ j := by simp; omega
    rw [List.getD_eq_default _ _ h4, List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  cases L <;> simp

/-- If no gate reads wire `n`, the computed wires stay equal wherever the inputs are equal
away from wire `n`, so the output value never sees the wire `n` bit. -/
theorem noRead_agree (n : ℕ) : ∀ (gs : List Gate) (L1 L2 : List Bool),
    L1.length = L2.length →
    (∀ i : ℕ, i ≠ n → L1.getD i false = L2.getD i false) →
    (∀ g ∈ gs, n ∉ g.inputs) →
    ∀ i : ℕ, i ≠ n → (wiresF gs L1).getD i false = (wiresF gs L2).getD i false := by
  intro gs
  induction gs with
  | nil => intro L1 L2 _ hag _ i hi; exact hag i hi
  | cons g gs ih =>
    intro L1 L2 hlen hagree hno i hi
    have hgno : n ∉ g.inputs := hno g List.mem_cons_self
    have hgsno : ∀ g ∈ gs, n ∉ g.inputs :=
      fun g hg => hno g (List.mem_cons_of_mem _ hg)
    -- the two gate values coincide, because every read index differs from `n`
    have hval : g.op.eval (g.inputs.map fun q => L1.getD q false)
        = g.op.eval (g.inputs.map fun q => L2.getD q false) := by
      congr 1
      apply List.map_congr_left
      intro q hq
      exact hagree q (fun hne => hgno (hne ▸ hq))
    have hstep : (L1 ++ [g.op.eval (g.inputs.map fun q => L1.getD q false)]).length
        = (L2 ++ [g.op.eval (g.inputs.map fun q => L2.getD q false)]).length := by
      simp only [List.length_append, hlen]
      simp
    have hstepagree : ∀ j : ℕ, j ≠ n →
        (L1 ++ [g.op.eval (g.inputs.map fun q => L1.getD q false)]).getD j false
          = (L2 ++ [g.op.eval (g.inputs.map fun q => L2.getD q false)]).getD j false := by
      intro j hj
      by_cases hjl : j < L1.length
      · rw [List.getD_append _ _ _ _ hjl, List.getD_append _ _ _ _ (by omega), hagree j hj]
      · by_cases hjk : j = L1.length
        · subst hjk
          rw [getD_snoc_eq, hlen, getD_snoc_eq]
          exact hval
        · have f1 : (L1 ++ [g.op.eval (g.inputs.map fun q => L1.getD q false)]).length
              = L1.length + 1 := by simp
          have f2 : (L2 ++ [g.op.eval (g.inputs.map fun q => L2.getD q false)]).length
              = L2.length + 1 := by simp
          rw [List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by omega)]
    rw [wiresF, wiresF, List.foldl_cons, List.foldl_cons]
    exact ih _ _ hstep hstepagree hgsno i hi

/-! ## small helpers -/

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  have hf : (fun k : Fin n => (List.ofFn x).getD (k : ℕ) false) = x := by simp
  exact congrFun hf ⟨i, hi⟩

theorem wiresF_single (g : Gate) (w : List Bool) :
    wiresF [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem wiresF_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresF (g :: gs) w = wiresF gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

/-- The value of a freshly computed wire is visible through any further computation. -/
theorem getD_next {α : Type} (L : List α) (S : α) (t : List α) (d : α) :
    ((L ++ [S]) ++ t).getD L.length d = S := by
  rw [List.getD_append _ _ _ _ (by simp), getD_snoc_eq]

/-! ## Direction: lifting a circuit for `f` to one for the lifted function -/

/-- Wire indices below `n` keep their number; the computed wires shift by one. -/
def shiftIdx (n : ℕ) (i : ℕ) : ℕ := if i < n then i else i + 1

/-- Shift all reads of a gate by one, leaving the operation. -/
def mapGate (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftIdx n)⟩

theorem mapGate_ok (n : ℕ) (γ : List Gate) (hok : ∀ g ∈ γ, Ok g) (g : Gate)
    (hg : g ∈ γ.map (mapGate n)) : Ok g := by
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  obtain ⟨h1, h2⟩ := hok g0 hg0
  simp only [Ok, mapGate]
  exact ⟨h1, by simp only [List.length_map]; exact h2⟩

/-- The wires of a shifted circuit at the shifted slot of every new wire equal the wires of
the original circuit. -/
theorem shiftWires (n : ℕ) : ∀ γ : List Gate, ∀ bx bw : List Bool,
    bw.length ≥ n → bw.length + 1 = bx.length →
    (∀ a : ℕ, bx.getD (shiftIdx n a) false = bw.getD a false) →
    ∀ j : ℕ, j < γ.length →
      (wiresF (γ.map (mapGate n)) bx).getD (bx.length + j) false
        = (wiresF γ bw).getD (bw.length + j) false := by
  intro γ
  induction γ with
  | nil =>
    intro bx bw _ _ _ j hj
    exact absurd hj (Nat.not_lt_zero j)
  | cons g gs ih =>
    intro bx bw h1 h2 hR j hj
    set sv1 : Bool := ((mapGate n g).op).eval ((mapGate n g).inputs.map fun i => bx.getD i false)
      with hv1
    set sv2 : Bool := g.op.eval (g.inputs.map fun a => bw.getD a false) with hv2
    -- the gate value on the two sides
    have hge : ((mapGate n g).inputs.map (fun i => bx.getD i false))
        = g.inputs.map (fun a => bw.getD a false) := by
      show ((g.inputs.map (shiftIdx n)).map (fun i => bx.getD i false)) = _
      simp only [List.map_map, Function.comp_def, hR]
    have hval : sv1 = sv2 := by
      rw [hv1, hge]
      show g.op.eval (g.inputs.map fun a => bw.getD a false) = sv2
      rw [← hv2]
    -- lengths of the extended lists
    have hf2 : ((bx ++ [sv1]) : List Bool).length = bx.length + 1 := by simp
    have hf1 : ((bw ++ [sv2]) : List Bool).length = bw.length + 1 := by simp
    -- the read agreement for the lists after the new wire is appended on each side
    have hR' : ∀ a : ℕ, (bx ++ [sv1]).getD (shiftIdx n a) false
        = (bw ++ [sv2]).getD a false := by
      intro a
      rcases Nat.lt_or_ge a n with han | han
      · have ke : shiftIdx n a = a := by simp [shiftIdx, han]
        have hb1 : shiftIdx n a < bx.length := by rw [ke]; omega
        have hb2 : a < bw.length := by omega
        rw [List.getD_append bx [sv1] false (shiftIdx n a) hb1,
          List.getD_append bw [sv2] false a hb2, hR a]
      · have ke : shiftIdx n a = a + 1 := by simp [shiftIdx, han]
        have hRa : bx.getD (a + 1) false = bw.getD a false := by
          have hv := hR a
          rw [ke] at hv
          exact hv
        rw [ke]
        by_cases hx1 : a + 1 < bx.length
        · rw [List.getD_append bx [sv1] false (a + 1) hx1,
            List.getD_append bw [sv2] false a (by omega : a < bw.length), hRa]
        · by_cases haeq : a + 1 = bx.length
          · have hae : a = bw.length := by omega
            rw [haeq, getD_snoc_eq bx sv1 false, hae, getD_snoc_eq bw sv2 false]
            exact hval
          · have hwo1 : ((bx ++ [sv1]) : List Bool).length ≤ a + 1 := by omega
            have hwo2 : ((bw ++ [sv2]) : List Bool).length ≤ a := by omega
            rw [List.getD_eq_default _ _ hwo1, List.getD_eq_default _ _ hwo2]
    have h1' : ((bw ++ [sv2]) : List Bool).length ≥ n := by rw [hf1]; omega
    have h2' : ((bw ++ [sv2]) : List Bool).length + 1 = ((bx ++ [sv1]) : List Bool).length := by
      rw [hf1, hf2]; omega
    -- unfold the fold one step on both sides
    rw [List.map_cons, wiresF_cons, wiresF_cons, ← hv1, ← hv2]
    rcases j with _ | k
    · -- the newly created wire on each side
      simp only [Nat.add_zero]
      obtain ⟨t1, ht1, _⟩ := wiresF_prefix (gs.map (mapGate n)) (bx ++ [sv1])
      obtain ⟨t2, ht2, _⟩ := wiresF_prefix gs (bw ++ [sv2])
      rw [ht1, ht2, getD_next _ _ _ _, getD_next _ _ _ _]
      exact hval
    · -- recurse on the remaining gates, with the indices re-anchored
      have hix1 : bx.length + (k + 1) = ((bx ++ [sv1]) : List Bool).length + k := by
        rw [hf2]; omega
      have hix2 : bw.length + (k + 1) = ((bw ++ [sv2]) : List Bool).length + k := by
        rw [hf1]; omega
      rw [hix1, hix2]
      exact ih _ _ h1' h2' hR' k (by simp only [List.length_cons] at hj; omega)

theorem lift_circuit (n s : ℕ) (f : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n f s) :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
      (s + 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := h
  set gs' := C.gates.map (mapGate n) with hgs'
  set top : Gate := ⟨GateOp.and, [n, shiftIdx n C.output]⟩ with htop
  refine ⟨⟨gs' ++ [top], n + 1 + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg1 | hg2
    · exact mapGate_ok n C.gates hok g hg1
    · rw [List.mem_singleton] at hg2
      subst hg2
      simp only [Ok, htop]
      simp
  · show ((gs' ++ [top] : List Gate)).length ≤ s + 1
    have hgl : gs'.length = C.gates.length := by rw [hgs']; simp
    rw [List.length_append, hgl]
    simp only [htop, List.length_cons, List.length_nil]
    have hsz2 : C.size = C.gates.length := rfl
    omega
  · intro x
    have hlyy : ∀ y : Fin n → Bool, C.eval (List.ofFn y) = f y := hev
    have hfnl : (List.ofFn x).length = n + 1 := by simp
    set yy := fun i : Fin n => x i.castSucc with hyy
    set byy := List.ofFn yy with hbyy
    have hbyl : byy.length = n := by rw [hbyy]; simp
    have hols : ((List.ofFn yy) : List Bool).length = n := by simp
    have hRR : ∀ a : ℕ, (List.ofFn x).getD (shiftIdx n a) false = byy.getD a false := by
      intro a
      rcases Nat.lt_or_ge a n with han | han
      · have ke : shiftIdx n a = a := by simp [shiftIdx, han]
        rw [ke, getD_ofFn x a (by omega), getD_ofFn yy a han]
        rfl
      · have ke : shiftIdx n a = a + 1 := by simp [shiftIdx, han]
        rw [ke, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    -- value on the old side
    have hfolder : (wiresF C.gates (List.ofFn yy)).getD C.output false = f yy := by
      have hv := hlyy yy
      simp only [Circuit.eval, wires_eq] at hv
      exact hv
    -- one step of the new fold, and the two reads of its top gate
    simp only [Circuit.eval, wires_eq]
    rw [wiresF_append, wiresF_single]
    set w' := wiresF gs' (List.ofFn x) with hw'
    have hw'l : w'.length = n + 1 + C.gates.length := by
      rw [hw', length_wiresF, hgs']; simp
    obtain ⟨t, ht, _⟩ := wiresF_prefix gs' (List.ofFn x)
    have hLx : ((wiresF (C.gates.map (mapGate n)) (List.ofFn x)) : List Bool).length
        = n + 1 + C.gates.length := by rw [length_wiresF]; simp
    have hLo : ((wiresF C.gates (List.ofFn yy)) : List Bool).length
        = n + C.gates.length := by rw [length_wiresF, hols]
    have hwa : w'.getD n false = x (Fin.last n) := by
      rw [hw', ht, List.getD_append (List.ofFn x) t false n (by omega),
        getD_ofFn x n (by omega)]
      rfl
    have hval : ((⟨GateOp.and, [n, shiftIdx n C.output]⟩ : Gate).op).eval
        ((⟨GateOp.and, [n, shiftIdx n C.output]⟩ : Gate).inputs.map fun i => w'.getD i false)
        = (w'.getD n false && w'.getD (shiftIdx n C.output) false) := by
      simp [GateOp.eval]
    have hws : w'.getD (shiftIdx n C.output) false = f yy := by
      rcases Nat.lt_or_ge C.output n with hlt | hge
      · have ke : shiftIdx n C.output = C.output := by simp [shiftIdx, hlt]
        rw [ke, hw', ht, List.getD_append (List.ofFn x) t false C.output (by omega),
          getD_ofFn x C.output (by omega)]
        obtain ⟨t2, ht2, _⟩ := wiresF_prefix C.gates (List.ofFn yy)
        rw [← hfolder, ht2,
          List.getD_append (List.ofFn yy) t2 false C.output (by omega),
          getD_ofFn yy C.output hlt, hyy]
        rfl
      · have ke : shiftIdx n C.output = C.output + 1 := by simp [shiftIdx, hge]
        rcases Nat.lt_or_ge C.output (n + C.gates.length) with hlo | hhi
        · have hj : C.output - n < C.gates.length := by omega
          have hsw := shiftWires n C.gates (List.ofFn x) byy (by rw [hbyl]) (by omega) hRR
            (C.output - n) hj
          have hi1 : (List.ofFn x).length + (C.output - n) = C.output + 1 := by omega
          have hi2 : byy.length + (C.output - n) = C.output := by rw [hbyl]; omega
          rw [hi1, hi2] at hsw
          rw [ke, hw', hgs']
          exact hsw.trans hfolder
        · have hb_mo : ((wiresF (C.gates.map (mapGate n)) (List.ofFn x)) : List Bool).length
              ≤ C.output + 1 := by rw [hLx]; omega
          have hb_old : ((wiresF C.gates (List.ofFn yy)) : List Bool).length ≤ C.output := by
            rw [hLo]; omega
          rw [ke, hw', hgs', List.getD_eq_default _ _ hb_mo, ← hfolder,
            List.getD_eq_default _ _ hb_old]
    -- assemble
    have hidx : n + 1 + C.gates.length = w'.length := hw'l.symm
    rw [hidx, getD_snoc_eq, htop, hval, hwa, hws]
/-! ## Gate elimination on the last wire -/

/-- A NOT gate reads only its first wire: drop the others. -/
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (Fv : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map Fv) = g.op.eval (g.inputs.map Fv) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresF_norm (gs : List Gate) : ∀ w : List Bool,
    wiresF (gs.map normGate) w = wiresF gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresF ((g :: gs).map normGate) w = wiresF (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresF (g :: gs) w
        = wiresF gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresF (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresF]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresF]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresF]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresF]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresF]
/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
saved. -/
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
and every old wire has a valid status whose value on the new wires is the old value. -/
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresF acc.2 y) = w.getD i false

theorem invElim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresF gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresF acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresF, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresF (acc.2 ++ r.1.toList) y = wiresF r.1.toList w' := by
      rw [wiresF_append]
    obtain ⟨t, ht, htl⟩ := wiresF_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresF (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

/-- The statuses at the start: the first `n` old wires are the new input wires, and the last
input is the constant `b`. -/
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : ((List.ofFn y : List Bool)).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresF]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp
/-- Gate elimination: fix the last input of `ff` to `b`. If `ff` depends on that input and the
restriction is not constant, a circuit of size `s + 1` for `ff` gives one of size `s` for the
restriction. -/
theorem gateElim (n : ℕ) (ff : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, ff (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ ff x)
    (hnc : ∃ y y' : Fin n → Bool, ff (Fin.snoc y b) ≠ ff (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) ff (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => ff (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresF gs (List.ofFn x)).getD C.output false = ff x := by
    intro x
    rw [hgs, wiresF_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresF gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact invElim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresF acc.2 (List.ofFn y))
        = ff (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push_neg at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        -- the two wire lists agree away from the wire `n`
        have hofD : ((List.ofFn (Function.update x (Fin.last n) (!x (Fin.last n)))) : List Bool).length
            = n + 1 := by simp
        have hofx : ((List.ofFn x) : List Bool).length = n + 1 := by simp
        have hlen : (List.ofFn (Function.update x (Fin.last n) (!x (Fin.last n)))).length
            = (List.ofFn x).length := by simp
        have hagr : ∀ i : ℕ, i ≠ n →
            (List.ofFn (Function.update x (Fin.last n) (!x (Fin.last n)))).getD i false
              = (List.ofFn x).getD i false := by
          intro i hi
          rcases Nat.lt_or_ge i (n + 1) with hlt | hge
          · have hnne : (⟨i, hlt⟩ : Fin (n + 1)) ≠ Fin.last n := by
              intro e
              have hv := congrArg Fin.val e
              simp at hv
              exact hi hv
            rw [getD_ofFn _ _ hlt, getD_ofFn _ _ hlt, Function.update_of_ne hnne]
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        have hns := noRead_agree n gs
          (List.ofFn (Function.update x (Fin.last n) (!x (Fin.last n)))) (List.ofFn x)
          hlen hagr hread C.output hout
        rw [← hevg (Function.update x (Fin.last n) (!x (Fin.last n))), ← hevg x]
        exact hns
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_174_aux

open PEqualNP.Outside.L_meta_174_aux in
/-- Left: the lifted function inherits the circuit plus one AND gate. Right: gate
elimination removes a gate, because the last input is read and the restriction `f` is not
constant. -/
theorem PEqualNP.Outside.L_meta_174 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool),
    (∃ y y' : Fin n → Bool, f y ≠ f y') →
    (PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => x (Fin.last n) && f (fun i : Fin n => x i.castSucc)) (s + 1) ↔
     PEqualNP.MetaComplexity.HasCircuitSize n f s) := by
  intro n s f hne
  refine ⟨fun hca => ?_, lift_circuit n s f⟩
  obtain ⟨y, y', hyne⟩ := hne
  have hy0 : ∃ y0 : Fin n → Bool, f y0 = true := by
    by_cases hb : f y = true
    · exact ⟨y, hb⟩
    · by_cases hb' : f y' = true
      · exact ⟨y', hb'⟩
      · refine absurd (show f y = f y' from ?_) hyne
        simp only [hb, hb']
  have hFsnoc : ∀ y : Fin n → Bool,
      ((fun x : Fin (n + 1) → Bool => x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
        (Fin.snoc y true)) = f y := by
    intro y
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
    rfl
  have hdep : ∃ x : Fin (n + 1) → Bool,
      ((fun x : Fin (n + 1) → Bool => x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
        (Function.update x (Fin.last n) (!(x (Fin.last n))))) ≠
      ((fun x : Fin (n + 1) → Bool => x (Fin.last n) && f (fun i : Fin n => x i.castSucc)) x) := by
    obtain ⟨y0, hy0⟩ := hy0
    refine ⟨Fin.snoc y0 true, ?_⟩
    have e1 : ((Fin.snoc y0 true : Fin (n + 1) → Bool) (Fin.last n)) = true :=
      Fin.snoc_last (α := fun _ => Bool) true y0
    have e3 : ((Function.update (Fin.snoc y0 true : Fin (n + 1) → Bool) (Fin.last n)
        (!((Fin.snoc y0 true : Fin (n + 1) → Bool) (Fin.last n)))) (Fin.last n)) = false := by
      rw [Function.update_self, e1]
      simp
    simp [e3]
    exact hy0
  have hnc : ∃ y1 y2 : Fin n → Bool,
      ((fun x : Fin (n + 1) → Bool => x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
        (Fin.snoc y1 true)) ≠
      ((fun x : Fin (n + 1) → Bool => x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
        (Fin.snoc y2 true)) :=
    ⟨y, y', by rw [hFsnoc y, hFsnoc y']; exact hyne⟩
  obtain ⟨C', ok', hsz', hev'⟩ :=
    gateElim n (fun x : Fin (n + 1) → Bool => x (Fin.last n) && f (fun i : Fin n => x i.castSucc))
      true s hdep hnc hca
  refine ⟨C', ok', hsz', fun x => ?_⟩
  exact (hev' x).trans (hFsnoc x)
