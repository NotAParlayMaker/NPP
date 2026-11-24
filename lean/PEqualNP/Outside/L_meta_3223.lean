import Mathlib
import PEqualNP.Defs

-- Constant propagation (wiresFrom .. force_or) copied from L_meta_2305, itself adapted from stierms, L-meta-517 (PR 553).
namespace PEqualNP.Outside.L_meta_3223_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

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

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

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
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
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

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def ConstAt (a : List Stat × List Gate) (k : ℕ) (c : Bool) : Prop :=
  k < a.1.length ∧ a.1.getD k (Sum.inl false) = Sum.inl c


theorem const_step (n : ℕ) (a : List Stat × List Gate) (g : Gate) (k : ℕ) (c : Bool)
    (h : ConstAt a k c) : ConstAt (elimStep n a g) k c := by
  have hk := h.1
  refine ⟨by simp [elimStep]; omega, ?_⟩
  change (a.1 ++ [_]).getD k (Sum.inl false) = _
  rw [getD_snoc_ne _ _ _ _ (by omega)]
  exact h.2

theorem elim_const (n : ℕ) (gs : List Gate) (k : ℕ) (c : Bool) :
    ∀ a, ConstAt a k c → ConstAt (elim n gs a) k c := by
  induction gs with
  | nil => intro a h; exact h
  | cons g gs ih => intro a h; exact ih _ (const_step n a g k c h)

theorem elim_status_length (n : ℕ) (gs : List Gate) : ∀ a,
    (elim n gs a).1.length = a.1.length + gs.length := by
  induction gs with
  | nil => intro a; simp [elim]
  | cons g gs ih => intro a; change (elim n gs (elimStep n a g)).1.length = _; rw [ih]; simp [elimStep]; omega

theorem none_of_const (n : ℕ) (a : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (k : ℕ) (c : Bool) (hc : ConstAt a k c) (hk : k ∈ g.inputs) :
    (simplify g.op (n + a.2.length) (g.inputs.map fun i => a.1.getD i (Sum.inl false))).1 = none := by
  apply simplify_count _ _ _ hg.1.1
  · simpa using hg.1.2
  · intro h; simpa using hg.2 h
  · exact ⟨c, List.mem_map.mpr ⟨k, hk, hc.2⟩⟩

theorem step_len_le (n : ℕ) (a : List Stat × List Gate) (g : Gate) :
    (elimStep n a g).2.length ≤ a.2.length + 1 := by
  simp only [elimStep, List.length_append]
  exact Nat.add_le_add_left (toList_length_le _) _

theorem step_len_const (n : ℕ) (a : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (k : ℕ) (c : Bool) (hc : ConstAt a k c) (hk : k ∈ g.inputs) :
    (elimStep n a g).2.length = a.2.length := by
  simp only [elimStep, none_of_const n a g hg k c hc hk]
  simp

theorem force_and (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2) (hc : Sum.inl false ∈ ins) :
    (simplify GateOp.and m ins).2 = Sum.inl false := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simplify, simpAnd] <;> aesop

theorem force_or (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2) (hc : Sum.inl true ∈ ins) :
    (simplify GateOp.or m ins).2 = Sum.inl true := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
    simp_all [simplify, simpOr]


theorem step_len_cs (n : ℕ) (a : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (k : ℕ) (c : Bool) (hc : a.1.getD k (Sum.inl false) = Sum.inl c) (hk : k ∈ g.inputs) :
    (elimStep n a g).2.length = a.2.length := by
  have h : (simplify g.op (n + a.2.length)
      (g.inputs.map fun i => a.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count _ _ _ hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.mpr ⟨k, hk, hc⟩⟩
  simp only [elimStep, h]
  simp

theorem elim_split (n : ℕ) (p t : List Gate) (g : Gate) (a : List Stat × List Gate) :
    elim n (p ++ g :: t) a = elim n t (elimStep n (elim n p a) g) := by
  simp [elim, List.foldl_append]

theorem skip (n : ℕ) (p t : List Gate) (g : Gate) (a : List Stat × List Gate)
    (hs : (elimStep n (elim n p a) g).2.length = (elim n p a).2.length) :
    (elim n (p ++ g :: t) a).2.length ≤ a.2.length + p.length + t.length := by
  rw [elim_split]
  have h1 := elim_len n t (elimStep n (elim n p a) g)
  have h2 := elim_len n p a
  omega

theorem agree (Z : ℕ → Prop) (gs : List Gate) : ∀ (u v : List Bool), u.length = v.length →
    (∀ i, ¬ Z i → u.getD i false = v.getD i false) → (∀ g ∈ gs, ∀ k ∈ g.inputs, ¬ Z k) →
    (wiresFrom gs u).length = (wiresFrom gs v).length ∧
      ∀ i, ¬ Z i → (wiresFrom gs u).getD i false = (wiresFrom gs v).getD i false := by
  induction gs with
  | nil => intro u v hl h _; exact ⟨hl, h⟩
  | cons g gs ih =>
    intro u v hl h hg
    have e : (g.inputs.map fun i => u.getD i false) = (g.inputs.map fun i => v.getD i false) := by
      apply List.map_congr_left
      intro k hk
      exact h k (hg g List.mem_cons_self k hk)
    change (wiresFrom gs (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])).length
        = (wiresFrom gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])).length ∧
      ∀ i, ¬ Z i → (wiresFrom gs (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])).getD i false
        = (wiresFrom gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])).getD i false
    rw [e]
    refine ih _ _ (by simp [hl]) ?_ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro i hi
    by_cases hil : i = u.length
    · subst hil; rw [getD_snoc_eq, hl, getD_snoc_eq]
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]; exact h i hi

theorem agree_split (Z : ℕ → Prop) (p t : List Gate) (g1 : Gate) (u v : List Bool)
    (hl : u.length = v.length)
    (h : ∀ i, ¬ Z i → u.getD i false = v.getD i false) (hz : Z (u.length + p.length))
    (hp : ∀ g ∈ p, ∀ k ∈ g.inputs, ¬ Z k) (ht : ∀ g ∈ t, ∀ k ∈ g.inputs, ¬ Z k) :
    ∀ i, ¬ Z i → (wiresFrom (p ++ g1 :: t) u).getD i false
      = (wiresFrom (p ++ g1 :: t) v).getD i false := by
  rw [wiresFrom_append, wiresFrom_append]
  obtain ⟨h1, h2⟩ := agree Z p u v hl h hp
  have l1 := length_wiresFrom p u
  change ∀ i, ¬ Z i → (wiresFrom t (wiresFrom p u ++
      [g1.op.eval (g1.inputs.map fun i => (wiresFrom p u).getD i false)])).getD i false
    = (wiresFrom t (wiresFrom p v ++
      [g1.op.eval (g1.inputs.map fun i => (wiresFrom p v).getD i false)])).getD i false
  refine (agree Z t _ _ (by simp [h1]) ?_ ht).2
  intro i hi
  have hne : i ≠ (wiresFrom p u).length := by
    rintro rfl; exact hi (l1 ▸ hz)
  rw [getD_snoc_ne _ _ _ _ hne, getD_snoc_ne _ _ _ _ (by omega)]
  exact h2 i hi

def init (n : ℕ) (tpl : List (Option (Fin n))) : List Stat × List Gate :=
  (tpl.map (fun o => o.elim (Sum.inl false) (fun v => Sum.inr v.val)), [])

theorem init_inv (n : ℕ) (tpl : List (Option (Fin n))) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (tpl.map (fun o => o.elim false x)) (init n tpl) := by
  refine ⟨by simp [init], ?_⟩
  intro i
  by_cases h : i < tpl.length
  · have e1 : (init n tpl).1.getD i (Sum.inl false)
        = (tpl[i]).elim (Sum.inl false) (fun v => Sum.inr v.val) := by
      simp [init, List.getD_eq_getElem?_getD, h]
    have e2 : (tpl.map (fun o => o.elim false x)).getD i false = (tpl[i]).elim false x := by
      simp [List.getD_eq_getElem?_getD, h]
    rw [e1, e2]
    cases tpl[i] with
    | none => exact ⟨trivial, rfl⟩
    | some v =>
      refine ⟨?_, ?_⟩
      · simp [Stat.Valid, init]
      · simp [Stat.val, wiresFrom, init, List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp [init]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem count_bound (n : ℕ) (tpl : List (Option (Fin n))) (w0 e : ℕ) (gs : List Gate) (o : ℕ)
    (hnok : ∀ g ∈ gs, NOk g) (hw : tpl[w0]? = some none) (he : e ≤ 1)
    (hor : e = 1 → ∀ g ∈ gs, g.op = GateOp.or → w0 ∉ g.inputs)
    (hA : ∃ y1 y2 : List Bool, y1.length = tpl.length ∧ y2.length = tpl.length ∧
      (∀ i, i ≠ w0 → y1.getD i false = y2.getD i false) ∧
      (wiresFrom gs y1).getD o false ≠ (wiresFrom gs y2).getD o false)
    (hnc : ∀ c, (elim n gs (init n tpl)).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    (elim n gs (init n tpl)).2.length + (e + 1) ≤ gs.length := by
  obtain ⟨y1, y2, l1, l2, hag, hne⟩ := hA
  have hw0 : w0 < tpl.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hw
    cases hw
  have hc0 : ConstAt (init n tpl) w0 false :=
    ⟨by simpa [init] using hw0, by simp [init, List.getD_eq_getElem?_getD, hw]⟩
  have hg1 : ∃ g1 ∈ gs, w0 ∈ g1.inputs := by
    by_contra hno
    push_neg at hno
    have h := (agree (fun i => i = w0) gs y1 y2 (by omega) hag
      (fun g hg k hk hkz => hno g hg (hkz ▸ hk))).2
    by_cases ho : o = w0
    · exact hnc false (ho ▸ (elim_const n gs w0 false _ hc0).2)
    · exact hne (h o ho)
  obtain ⟨g1, hg1, hin1⟩ := hg1
  obtain ⟨p, t, rfl⟩ := List.append_of_mem hg1
  have c1 := elim_const n p w0 false _ hc0
  have hn1 := hnok g1 (by simp)
  have s1 := step_len_const n _ g1 hn1 w0 false c1 hin1
  have lp := elim_len n p (init n tpl)
  have i0 : (init n tpl).2.length = 0 := rfl
  have lt := elim_len n t (elimStep n (elim n p (init n tpl)) g1)
  have len1 : (elim n p (init n tpl)).1.length = tpl.length + p.length := by
    rw [elim_status_length]; simp [init]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with rfl | rfl
  · rw [elim_split]; simp only [List.length_append, List.length_cons]; omega
  · have hconst1 : ∃ c, ConstAt (elimStep n (elim n p (init n tpl)) g1) (tpl.length + p.length) c := by
      have hlen : tpl.length + p.length < (elimStep n (elim n p (init n tpl)) g1).1.length := by
        simp [elimStep, len1]
      rcases hn1.1.1 with hop | hop | hop
      · have hop : g1.op = GateOp.and := hop
        refine ⟨false, hlen, ?_⟩
        change ((elim n p (init n tpl)).1 ++ [_]).getD _ (Sum.inl false) = _
        rw [getD_snoc_len _ _ _ _ len1, hop]
        exact force_and _ _ (by simpa using hn1.1.2) (List.mem_map.mpr ⟨w0, hin1, c1.2⟩)
      · have hop : g1.op = GateOp.or := hop
        exact absurd hin1 (hor rfl g1 (by simp) hop)
      · have hop : g1.op = GateOp.not := hop
        have hl := hn1.2 hop
        have hinp : g1.inputs = [w0] := by
          rcases hi : g1.inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
          · rw [hi] at hin1; simp at hin1
          · rw [hi] at hin1; simp at hin1; rw [hin1]
          · rw [hi] at hl; simp at hl
        refine ⟨true, hlen, ?_⟩
        change ((elim n p (init n tpl)).1 ++ [_]).getD _ (Sum.inl false) = _
        rw [getD_snoc_len _ _ _ _ len1, hop, hinp]
        simp only [List.map_cons, List.map_nil, c1.2]
        rfl
    obtain ⟨c, hcc⟩ := hconst1
    by_cases hexp : ∃ h ∈ p, w0 ∈ h.inputs ∨ tpl.length + p.length ∈ h.inputs
    · obtain ⟨h, hh, hr⟩ := hexp
      obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hh
      have lenp : (elim n p1 (init n tpl)).1.length = tpl.length + p1.length := by
        rw [elim_status_length]; simp [init]
      have sh : (elimStep n (elim n p1 (init n tpl)) h).2.length
          = (elim n p1 (init n tpl)).2.length := by
        rcases hr with hr | hr
        · exact step_len_cs n _ h (hnok h (by simp)) w0 false (elim_const n p1 w0 false _ hc0).2 hr
        · refine step_len_cs n _ h (hnok h (by simp)) _ false ?_ hr
          exact List.getD_eq_default _ _ (by simp [lenp])
      have hsk := skip n p1 p2 h (init n tpl) sh
      rw [elim_split]
      simp only [List.length_append, List.length_cons] at *
      omega
    · by_cases hext : ∃ h ∈ t, w0 ∈ h.inputs ∨ tpl.length + p.length ∈ h.inputs
      · obtain ⟨h, hh, hr⟩ := hext
        obtain ⟨t1, t2, rfl⟩ := List.append_of_mem hh
        have c0' := const_step n _ g1 w0 false c1
        have sh : (elimStep n (elim n t1 (elimStep n (elim n p (init n tpl)) g1)) h).2.length
            = (elim n t1 (elimStep n (elim n p (init n tpl)) g1)).2.length := by
          rcases hr with hr | hr
          · exact step_len_cs n _ h (hnok h (by simp)) w0 false (elim_const n t1 w0 false _ c0').2 hr
          · exact step_len_cs n _ h (hnok h (by simp)) _ c (elim_const n t1 _ c _ hcc).2 hr
        have hsk := skip n t1 t2 h _ sh
        rw [elim_split]
        simp only [List.length_append, List.length_cons] at *
        omega
      · exfalso
        push_neg at hexp hext
        have h := agree_split (fun i => i = w0 ∨ i = tpl.length + p.length) p t g1 y1 y2
          (by omega) (fun i hi => hag i (fun hh => hi (Or.inl hh))) (Or.inr (by rw [l1]))
          (fun g hg k hk hkz => by
            rcases hkz with rfl | rfl
            · exact (hexp g hg).1 hk
            · exact (hexp g hg).2 hk)
          (fun g hg k hk hkz => by
            rcases hkz with rfl | rfl
            · exact (hext g hg).1 hk
            · exact (hext g hg).2 hk)
        by_cases ho : o = w0 ∨ o = tpl.length + p.length
        · rcases ho with ho | ho
          · exact hnc false (ho ▸ (elim_const n _ w0 false _ hc0).2)
          · rw [elim_split] at hnc
            exact hnc c (ho ▸ (elim_const n t _ c _ hcc).2)
        · exact hne (h o ho)

theorem normGate_or (g : Gate) (h : (normGate g).op = GateOp.or) : normGate g = g := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [normGate] at h ⊢

theorem main (n : ℕ) (C : Circuit) (tpl : List (Option (Fin n))) (w0 e : ℕ)
    (hF : FanInTwo C) (hw : tpl[w0]? = some none) (he : e ≤ 1)
    (hor : e = 1 → ∀ g ∈ C.gates, g.op = GateOp.or → w0 ∉ g.inputs)
    (hA : ∃ (y1 : List Bool) (y2 : List Bool), y1.length = tpl.length ∧ y2.length = tpl.length ∧
      (∀ i : ℕ, i ≠ w0 → y1.getD i false = y2.getD i false) ∧ C.eval y1 ≠ C.eval y2)
    (hB : ∃ (a : Fin n → Bool) (b : Fin n → Bool),
      C.eval (tpl.map (fun o => o.elim false a)) ≠ C.eval (tpl.map (fun o => o.elim false b))) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + (e + 1) ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (tpl.map (fun o => o.elim false x)) := by
  have heval : ∀ y, C.eval y = (wiresFrom (C.gates.map normGate) y).getD C.output false := by
    intro y; rw [wiresFrom_norm]; rfl
  have hok : ∀ g ∈ C.gates.map normGate, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hF g0 hg0)
  have hval : ∀ x : Fin n → Bool,
      ((elim n (C.gates.map normGate) (init n tpl)).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim n (C.gates.map normGate) (init n tpl)).2 (List.ofFn x))
      = C.eval (tpl.map (fun o => o.elim false x)) := by
    intro x
    rw [heval]
    exact ((inv_elim n (List.ofFn x) (by simp) (C.gates.map normGate) _ _
      (fun g hg => (hok g hg).1) (init_inv n tpl x)).2 C.output).2
  have hnc : ∀ c, (elim n (C.gates.map normGate) (init n tpl)).1.getD C.output (Sum.inl false)
      ≠ Sum.inl c := by
    intro c hc
    obtain ⟨a, b, hab⟩ := hB
    apply hab
    rw [← hval a, ← hval b, hc]
    rfl
  have hcount := count_bound n tpl w0 e (C.gates.map normGate) C.output hok hw he
    (by
      intro he1 g hg hop
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      have e := normGate_or g0 hop
      rw [e] at hop ⊢
      exact hor he1 g0 hg0 hop)
    (by
      obtain ⟨y1, y2, l1, l2, hag, hne⟩ := hA
      rw [heval, heval] at hne
      exact ⟨y1, y2, l1, l2, hag, hne⟩)
    hnc
  rcases hs : (elim n (C.gates.map normGate) (init n tpl)).1.getD C.output (Sum.inl false)
    with c | k
  · exact absurd hs (hnc c)
  · refine ⟨⟨(elim n (C.gates.map normGate) (init n tpl)).2, k⟩, ?_, ?_, ?_⟩
    · exact elim_ok n _ (init n tpl) (by simp [init])
    · have : C.size = (C.gates.map normGate).length := by simp [Circuit.size]
      rw [this]
      exact hcount
    · intro x
      have h := hval x
      rw [hs] at h
      exact h

end PEqualNP.Outside.L_meta_3223_aux

theorem PEqualNP.Outside.L_meta_3223 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Option (Fin x1))) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x3[x4]? = Option.some Option.none → x5 ≤ (1 : ℕ) → (x5 = (1 : ℕ) → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ∉ x10.inputs) → (∃ (x10 : List Bool) (x11 : List Bool), x10.length = x3.length ∧ x11.length = x3.length ∧ (∀ (x12 : ℕ), x12 ≠ x4 → x10.getD x12 Bool.false = x11.getD x12 Bool.false) ∧ x2.eval x10 ≠ x2.eval x11) → (∃ (x11 : Fin x1 → Bool) (x12 : Fin x1 → Bool), x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x11) x3) ≠ x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x12) x3)) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size + (x5 + (1 : ℕ)) ≤ x2.size ∧ ∀ (x13 : Fin x1 → Bool), x12.eval (List.ofFn x13) = x2.eval (List.map (fun (x14 : Option (Fin x1)) => x14.elim Bool.false x13) x3) := by
  intro x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6
  exact PEqualNP.Outside.L_meta_3223_aux.main x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6
