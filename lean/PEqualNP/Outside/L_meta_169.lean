import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_169_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- A NOT gate reads only its first wire: drop the others. -/
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
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

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
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
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

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
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
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
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
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
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp


theorem elim_len1 (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih]; simp [elimStep]; omega

theorem elim_split (n : ℕ) (A B : List Gate) (g : Gate) (acc : List Stat × List Gate) :
    elim n (A ++ g :: B) acc = elim n B (elimStep n (elim n A acc) g) := by
  simp [elim, List.foldl_append]

theorem bad_const (n jv : ℕ) (g0 : Gate) (hok : Ok g0) (S : List Stat)
    (hSl : S.length = n + 1 + jv) (hSn : S.getD n (Stat.const false) = Stat.const false) (m : ℕ)
    (hread : (g0.op = GateOp.not ∧ g0.inputs.head? = some n) ∨
      (g0.op ≠ GateOp.not ∧ n ∈ g0.inputs))
    (hbad : ¬ (g0.op = GateOp.or ∧ g0.inputs.length = 2 ∧ n ∈ g0.inputs ∧
      ∃ w ∈ g0.inputs, w ≠ n ∧ w < n + 1 + jv)) :
    ∃ c, (simplify (normGate g0).op m
      ((normGate g0).inputs.map fun i => S.getD i (Stat.const false))).2 = Stat.const c := by
  obtain ⟨op, ins⟩ := g0
  obtain ⟨hop, hlen⟩ := hok
  have hdef : ∀ b, n + 1 + jv ≤ b → S.getD b (Stat.const false) = Stat.const false :=
    fun b hb => List.getD_eq_default _ _ (by omega)
  simp only at hop hlen hread hbad
  rcases hop with h | h | h <;> (have e : op = _ := h; subst e)
  · -- AND
    have hn : n ∈ ins := by
      rcases hread with ⟨h1, _⟩ | ⟨_, h2⟩
      · cases h1
      · exact h2
    show ∃ c, (simplify GateOp.and m (ins.map fun i => S.getD i (Stat.const false))).2 = _
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at hn
    · simp at hn; subst hn
      simp only [List.map_cons, List.map_nil, hSn]
      exact ⟨_, rfl⟩
    · simp at hn
      rcases hn with rfl | rfl
      · simp only [List.map_cons, List.map_nil, hSn]
        cases S.getD b (Stat.const false) <;> exact ⟨_, rfl⟩
      · simp only [List.map_cons, List.map_nil, hSn]
        cases S.getD a (Stat.const false) <;> exact ⟨_, rfl⟩
    · simp at hlen
  · -- OR
    have hn : n ∈ ins := by
      rcases hread with ⟨h1, _⟩ | ⟨_, h2⟩
      · cases h1
      · exact h2
    show ∃ c, (simplify GateOp.or m (ins.map fun i => S.getD i (Stat.const false))).2 = _
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at hn
    · simp at hn; subst hn
      simp only [List.map_cons, List.map_nil, hSn]
      exact ⟨_, rfl⟩
    · have hw : ∀ w ∈ [a, b], w ≠ n → n + 1 + jv ≤ w := by
        intro w hw hwn
        by_contra hlt
        exact hbad ⟨rfl, rfl, hn, w, hw, hwn, by omega⟩
      have hst : ∀ w ∈ [a, b], S.getD w (Stat.const false) = Stat.const false := by
        intro w hw'
        by_cases hwn : w = n
        · subst hwn; exact hSn
        · exact hdef w (hw w hw' hwn)
      simp only [List.map_cons, List.map_nil, hst a (by simp), hst b (by simp)]
      exact ⟨_, rfl⟩
    · simp at hlen
  · -- NOT
    rcases hread with ⟨_, h2⟩ | ⟨h1, _⟩
    · rcases ins with _ | ⟨a, l⟩
      · simp at h2
      · simp at h2; subst h2
        show ∃ c, (simplify GateOp.not m ([a].map fun i => S.getD i (Stat.const false))).2 = _
        simp only [List.map_cons, List.map_nil, hSn]
        exact ⟨_, rfl⟩
    · exact absurd rfl h1

/-- Wire `p` dropped: later indices move down by one. -/
def sh (p i : ℕ) : ℕ := if i < p then i else i - 1

def shG (p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh p)⟩

theorem rel_step (p : ℕ) (B : List Gate) (hB : ∀ h ∈ B, p ∉ h.inputs) :
    ∀ U U' : List Bool, U.length = U'.length + 1 → p < U.length →
      (∀ i, i ≠ p → U.getD i false = U'.getD (sh p i) false) →
      (wiresFrom B U).length = (wiresFrom (B.map (shG p)) U').length + 1 ∧
      ∀ i, i ≠ p → (wiresFrom B U).getD i false = (wiresFrom (B.map (shG p)) U').getD (sh p i) false := by
  induction B with
  | nil => intro U U' hl hp hr; exact ⟨hl, hr⟩
  | cons h B ih =>
    intro U U' hl hp hr
    have hpi : p ∉ h.inputs := hB h List.mem_cons_self
    have heq : h.op.eval (h.inputs.map fun i => U.getD i false) =
        (shG p h).op.eval ((shG p h).inputs.map fun i => U'.getD i false) := by
      simp only [shG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hr i (fun e => hpi (e ▸ hi))
    have s1 : wiresFrom (h :: B) U = wiresFrom B (U ++ [h.op.eval (h.inputs.map fun i => U.getD i false)]) := rfl
    have s2 : wiresFrom ((h :: B).map (shG p)) U' = wiresFrom (B.map (shG p))
        (U' ++ [(shG p h).op.eval ((shG p h).inputs.map fun i => U'.getD i false)]) := rfl
    rw [s1, s2, heq]
    apply ih (fun h' hh' => hB h' (List.mem_cons_of_mem _ hh'))
    · simp [hl]
    · simp; omega
    · intro i hip
      set a := (shG p h).op.eval ((shG p h).inputs.map fun i => U'.getD i false)
      by_cases hiU : i < U.length
      · rw [List.getD_append _ _ _ _ hiU, hr i hip]
        have : sh p i < U'.length := by unfold sh; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ this]
      · by_cases hiE : i = U.length
        · subst hiE
          rw [getD_snoc_eq]
          have : sh p U.length = U'.length := by unfold sh; split_ifs <;> omega
          rw [this, getD_snoc_eq]
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; unfold sh; split_ifs <;> omega)]

theorem reads_norm (g0 : Gate) (n : ℕ)
    (h : (g0.op = GateOp.not ∧ g0.inputs.head? = some n) ∨ (g0.op ≠ GateOp.not ∧ n ∈ g0.inputs)) :
    n ∈ (normGate g0).inputs := by
  obtain ⟨op, ins⟩ := g0
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    subst h1
    cases ins with
    | nil => simp at h2
    | cons a l => simp at h2; subst h2; simp [normGate]
  · simp only at h1 h2
    cases op <;> simp_all [normGate]

theorem rel_init (W : List Bool) (v : Bool) :
    ∀ i, i ≠ W.length → (W ++ [v]).getD i false = W.getD (sh W.length i) false := by
  intro i hi
  by_cases hlt : i < W.length
  · rw [List.getD_append _ _ _ _ hlt]; simp [sh, hlt]
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp [sh, hlt]; omega)]


end PEqualNP.Outside.L_meta_169_aux

open PEqualNP.Outside.L_meta_169_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_169 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' false)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false)) s → C.size ≤ s + 1) → ∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧ n ∈ (C.gates.get j).inputs ∧ ∃ w ∈ (C.gates.get j).inputs, w ≠ n ∧ w < n + 1 + j.val := by
  intro n C hmin _hdep hnc hsave j hread
  by_contra hbad
  have hok : ∀ g ∈ C.gates, Ok g := fun g hg => hmin.1 g hg
  set gs := C.gates.map normGate with hgs
  have hglen : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hj : j.val < gs.length := by rw [hglen]; exact j.2
  set A := gs.take j.val with hA
  set B := gs.drop (j.val + 1) with hB
  set g := gs[j.val] with hgdef
  have hsplit : gs = A ++ g :: B := by
    rw [hA, hB, hgdef, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hg : g = normGate (C.gates.get j) := by simp [hgdef, hgs]
  have hAlen : A.length = j.val := by simp [hA]; omega
  have hlenS : gs.length = A.length + 1 + B.length := by
    have := congrArg List.length hsplit; simp at this; omega
  have hgmem : g ∈ gs := by rw [hsplit]; simp
  have hAsub : ∀ h ∈ A, h ∈ gs := fun h hh => by rw [hsplit]; simp [hh]
  have hBsub : ∀ h ∈ B, h ∈ gs := fun h hh => by rw [hsplit]; simp [hh]
  have hevg : ∀ x : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn x)).getD C.output false = circuitFun (n + 1) C x := by
    intro x; rw [hgs, wiresFrom_norm]; rfl
  -- the elimination pass, split at gate `j`
  have hl1 : (elim n A (initStats n false, [])).1.length = n + 1 + j.val := by
    rw [elim_len1]; simp [initStats, hAlen]
  have hn1 : (elim n A (initStats n false, [])).1.getD n (Stat.const false) = Stat.const false := by
    rw [elim_getD n n _ A _ (by simp [initStats])]
    exact getD_snoc_len _ _ _ _ (by simp)
  set acc1 := elim n A (initStats n false, []) with hacc1
  set r := simplify g.op (n + acc1.2.length)
    (g.inputs.map fun i => acc1.1.getD i (Stat.const false)) with hr
  have hconst : ∃ c, r.2 = Stat.const c := by
    rw [hr, hg]
    exact bad_const n j.val (C.gates.get j) (hok _ (List.get_mem _ _)) acc1.1 hl1 hn1 _ hread hbad
  have hgn : n ∈ g.inputs := by rw [hg]; exact reads_norm _ n hread
  have hnone : r.1 = none := by
    have hgo := hnok g hgmem
    apply simplify_count
    · exact hgo.1.1
    · simpa using hgo.1.2
    · intro h; simpa using hgo.2 h
    · exact ⟨false, List.mem_map.2 ⟨n, hgn, hn1⟩⟩
  set acc2 := elimStep n acc1 g with hacc2
  have h2g : acc2.2 = acc1.2 := by
    show acc1.2 ++ r.1.toList = acc1.2
    rw [hnone]; simp
  have h2l : acc2.1.length = n + 1 + j.val + 1 := by
    show (acc1.1 ++ [r.2]).length = _
    simp [hl1]
  have h2p : acc2.1.getD (n + 1 + j.val) (Stat.const false) = r.2 :=
    getD_snoc_len _ _ _ _ hl1
  have h2n : acc2.1.getD n (Stat.const false) = Stat.const false := by
    show (acc1.1 ++ [r.2]).getD n (Stat.const false) = _
    rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hn1
  have hF : elim n gs (initStats n false, []) = elim n B acc2 := by
    rw [hsplit, elim_split]
  have h1len : acc1.2.length ≤ A.length := by
    have := elim_len n A (initStats n false, []); simpa using this
  have hFlen : (elim n B acc2).2.length ≤ acc2.2.length + B.length := elim_len n B acc2
  -- the restricted circuit
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y)
      (wiresFrom gs (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool)))
      (elim n gs (initStats n false, [])) := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n false y)
  have hval : ∀ y : Fin n → Bool,
      ((elim n gs (initStats n false, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n false, [])).2 (List.ofFn y))
        = circuitFun (n + 1) C (Fin.snoc y false) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : (elim n gs (initStats n false, [])).1.getD C.output (Stat.const false) with
  | const c =>
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire jj =>
    have hD : HasCircuitSize n (fun y : Fin n → Bool => circuitFun (n + 1) C (Fin.snoc y false))
        (elim n gs (initStats n false, [])).2.length := by
      refine ⟨⟨(elim n gs (initStats n false, [])).2, jj⟩,
        fun g hg => elim_ok n gs _ (by simp) g hg, le_refl _, ?_⟩
      intro y
      have := hval y
      rw [hst] at this
      exact this
    have hbig := hsave _ hD
    have hCs : C.size = gs.length := by rw [hglen]; rfl
    rw [hF] at hbig
    by_cases hBr : ∃ h ∈ B, n ∈ h.inputs ∨ (n + 1 + j.val) ∈ h.inputs
    · obtain ⟨h, hh, hk⟩ := hBr
      have hsave2 : (elim n B acc2).2.length + 1 ≤ acc2.2.length + B.length := by
        rcases hk with hk | hk
        · exact elim_len_lt n n B acc2 (fun g hg => hnok g (hBsub g hg)) (by omega)
            ⟨false, h2n⟩ ⟨h, hh, hk⟩
        · obtain ⟨c, hc⟩ := hconst
          exact elim_len_lt n (n + 1 + j.val) B acc2 (fun g hg => hnok g (hBsub g hg))
            (by omega) ⟨c, by rw [h2p, hc]⟩ ⟨h, hh, hk⟩
      rw [h2g] at hsave2
      omega
    · push Not at hBr
      by_cases hAr : ∃ h ∈ A, n ∈ h.inputs
      · have := elim_len_lt n n A (initStats n false, []) (fun g hg => hnok g (hAsub g hg))
          (by simp [initStats]) ⟨false, getD_snoc_len _ _ _ _ (by simp)⟩ hAr
        simp at this
        rw [h2g] at hFlen
        rw [← hacc1] at this
        omega
      · by_cases ho : C.output = n + 1 + j.val
        · obtain ⟨c, hc⟩ := hconst
          rw [hF, ho, elim_getD n _ _ B acc2 (by omega), h2p, hc] at hst
          cases hst
        · -- gate `j` is read by no later gate and is not the output: drop it
          set p := n + 1 + j.val with hp
          let C' : Circuit := ⟨A ++ B.map (shG p), sh p C.output⟩
          have hfun : circuitFun (n + 1) C' = circuitFun (n + 1) C := by
            funext x
            rw [← hevg x]
            show (wiresFrom (A ++ B.map (shG p)) (List.ofFn x)).getD (sh p C.output) false = _
            rw [hsplit, wiresFrom_append, wiresFrom_append]
            set W := wiresFrom A (List.ofFn x) with hW
            have hWl : W.length = p := by rw [hW, length_wiresFrom]; simp [hAlen, hp]
            have s1 : wiresFrom (g :: B) W =
                wiresFrom B (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
            rw [s1]
            have hrel := rel_step p B (fun h hh => (hBr h hh).2)
              (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) W (by simp)
              (by simp; omega) (by rw [← hWl]; exact rel_init W _)
            exact (hrel.2 C.output ho).symm
          have hfan : FanInTwo C' := by
            intro h hh
            rcases List.mem_append.1 hh with h1 | h1
            · exact (hnok h (hAsub h h1)).1
            · obtain ⟨h0, hh0, rfl⟩ := List.mem_map.1 h1
              have := (hnok h0 (hBsub h0 hh0)).1
              exact ⟨this.1, by simpa [shG] using this.2⟩
          have := hmin.2 C' hfan hfun
          have hC' : C'.size = A.length + B.length := by
            show (A ++ B.map (shG p)).length = _
            simp
          omega
