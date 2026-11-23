import Mathlib
import PEqualNP.Defs

-- Gate simplification helpers adapted from the project (Apache-2.0).
namespace PEqualNP.Outside.Absorb193

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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

abbrev Stat : Type := Sum Bool ℕ

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
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
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

theorem elim_len_count (n h : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → h < acc.1.length →
    acc.1.getD h (Sum.inl false) = Sum.inl false →
    (elim n gs acc).2.length + gs.countP (fun g => g.inputs.contains h) ≤
      acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hh hc
    have hstep : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have ih' := ih (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        change (acc.1 ++ [_]).getD h (Sum.inl false) = _
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hc)
    rw [hstep, List.countP_cons, List.length_cons]
    by_cases hmem : h ∈ g.inputs
    · have hg := hok g List.mem_cons_self
      have hn : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hg.1.1
        · simpa using hg.1.2
        · intro e; simpa using hg.2 e
        · exact ⟨false, List.mem_map.mpr ⟨h, hmem, hc⟩⟩
      have hl : (elimStep n acc g).2.length = acc.2.length := by
        change (acc.2 ++ _).length = _
        rw [hn]
        simp
      rw [if_pos (List.contains_iff_mem.mpr hmem)]
      omega
    · have hl : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        simp only [elimStep, List.length_append]
        omega
      rw [if_neg (by simpa using hmem)]
      omega

theorem elim_extends (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ tail : List Gate, (elim n gs acc).2 = acc.2 ++ tail := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨tail, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ++ tail, ?_⟩
    change (elim n gs (elimStep n acc g)).2 = _
    rw [ht]
    simp [elimStep, List.append_assoc]

def overrideStats (m h : ℕ) : List Stat :=
  List.ofFn (fun i : Fin m => if (i : ℕ) = h then Sum.inl false else Sum.inr i)

theorem override_at (m h : ℕ) (hh : h < m) :
    (overrideStats m h).getD h (Sum.inl false) = Sum.inl false := by
  simp [overrideStats, hh]

theorem override_inv (n h : ℕ) (ps : List Gate) (y : List Bool) (hy : y.length = n)
    (hh : (wiresFrom ps y).getD h false = false) :
    Inv n y (wiresFrom ps y) (overrideStats (n + ps.length) h, ps) := by
  refine ⟨by simp [overrideStats, length_wiresFrom, hy], ?_⟩
  intro i
  have hw : (wiresFrom ps y).length = n + ps.length := by simp [length_wiresFrom, hy]
  by_cases hi : i < n + ps.length
  · by_cases he : i = h
    · subst i
      simp [overrideStats, hi, Stat.Valid, Stat.val]
      exact hh
    · simp [overrideStats, hi, he, Stat.Valid, Stat.val]
  · rw [List.getD_eq_default _ _ (by simp [overrideStats]; omega),
      List.getD_eq_default _ _ (by omega)]
    exact ⟨trivial, rfl⟩

def readers (n h : ℕ) (gs : List Gate) : ℕ :=
  (gs.zipIdx n).countP (fun p => decide (h < p.2) && p.1.inputs.contains h)

theorem readers_append (n h : ℕ) (ps qs : List Gate) :
    readers n h (ps ++ qs) = readers n h ps + readers (n + ps.length) h qs := by
  simp [readers, List.zipIdx_append]

theorem readers_before (n h : ℕ) (ps : List Gate) (hp : n + ps.length ≤ h + 1) :
    readers n h ps = 0 := by
  apply List.countP_eq_zero.mpr
  intro p hp'
  have hb := (List.mem_zipIdx hp').2.1
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem readers_after (n h : ℕ) (qs : List Gate) (hh : h < n) :
    readers n h qs = qs.countP (fun g => g.inputs.contains h) := by
  unfold readers
  calc
    _ = (qs.zipIdx n).countP (fun p => p.1.inputs.contains h) := by
      apply List.countP_congr
      intro p hp
      have hb := (List.mem_zipIdx hp).1
      simp [show h < p.2 by omega]
    _ = _ := by
      simpa only [List.countP_map, Function.comp_def] using
        congrArg (List.countP (fun g : Gate => g.inputs.contains h)) (List.zipIdx_map_fst n qs)

theorem absorb_split (n h : ℕ) (ps qs : List Gate) (o : ℕ)
    (hp : h < n + ps.length)
    (hokp : ∀ g ∈ ps, Ok g) (hokq : ∀ g ∈ qs, NOk g)
    (hf : ∀ x : Fin n → Bool,
      (wiresFrom (ps ++ qs) (List.ofFn x)).getD h false = true →
      (wiresFrom (ps ++ qs) (List.ofFn x)).getD o false = true) :
    ∃ D : Circuit, FanInTwo D ∧
      (∀ x : Fin n → Bool,
        D.eval (List.ofFn x) = (wiresFrom (ps ++ qs) (List.ofFn x)).getD o false) ∧
      D.size + qs.countP (fun g => g.inputs.contains h) ≤ ps.length + qs.length + 1 := by
  let acc := elim n qs (overrideStats (n + ps.length) h, ps)
  have hcount := elim_len_count n h qs (overrideStats (n + ps.length) h, ps) hokq
    (by simpa [overrideStats] using hp) (override_at _ _ hp)
  change acc.2.length + qs.countP (fun g => g.inputs.contains h) ≤ ps.length + qs.length at hcount
  have hok : ∀ g ∈ acc.2, Ok g := elim_ok n qs _ hokp
  obtain ⟨tail, hext⟩ := elim_extends n qs (overrideStats (n + ps.length) h, ps)
  change acc.2 = ps ++ tail at hext
  have hwire : ∀ x : Fin n → Bool,
      (wiresFrom acc.2 (List.ofFn x)).getD h false =
        (wiresFrom (ps ++ qs) (List.ofFn x)).getD h false := by
    intro x
    have hh : h < (wiresFrom ps (List.ofFn x)).length := by simpa [length_wiresFrom] using hp
    rw [hext, wiresFrom_append, wiresFrom_append,
      getD_wiresFrom tail _ h hh, getD_wiresFrom qs _ h hh]
  have hval : ∀ x : Fin n → Bool,
      (wiresFrom (ps ++ qs) (List.ofFn x)).getD h false = false →
      (acc.1.getD o (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        (wiresFrom (ps ++ qs) (List.ofFn x)).getD o false := by
    intro x hx
    have hprefix : (wiresFrom ps (List.ofFn x)).getD h false = false := by
      rw [wiresFrom_append, getD_wiresFrom _ _ _ (by simpa [length_wiresFrom] using hp)] at hx
      exact hx
    have hinv := inv_elim n (List.ofFn x) (by simp) qs
      (wiresFrom ps (List.ofFn x)) (overrideStats (n + ps.length) h, ps)
      (fun g hg => (hokq g hg).1) (override_inv n h ps _ (by simp) hprefix)
    simpa only [wiresFrom_append] using (hinv.2 o).2
  cases hs : acc.1.getD o (Sum.inl false) with
  | inl c =>
    cases c with
    | false =>
      refine ⟨⟨acc.2, h⟩, hok, ?_, ?_⟩
      · intro x
        change (wiresFrom acc.2 (List.ofFn x)).getD h false = _
        rw [hwire]
        cases hv : (wiresFrom (ps ++ qs) (List.ofFn x)).getD h false with
        | false =>
          have e := hval x hv
          rw [hs] at e
          exact e
        | true => exact (hf x hv).symm
      · change acc.2.length + _ ≤ _
        omega
    | true =>
      refine ⟨⟨[⟨GateOp.and, []⟩], n⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst g
        simp
      · intro x
        change (wiresFrom [⟨GateOp.and, []⟩] (List.ofFn x)).getD n false = _
        have ht : (wiresFrom [⟨GateOp.and, []⟩] (List.ofFn x)).getD n false = true := by
          simp [wiresFrom, GateOp.eval]
        rw [ht]
        cases hv : (wiresFrom (ps ++ qs) (List.ofFn x)).getD h false with
        | false =>
          have e := hval x hv
          rw [hs] at e
          exact e
        | true => exact (hf x hv).symm
      · change 1 + _ ≤ _
        omega
  | inr j =>
    refine ⟨⟨acc.2 ++ [⟨GateOp.or, [h, j]⟩], n + acc.2.length⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hok g hg
      · simp only [List.mem_singleton] at hg
        subst g
        simp
    · intro x
      change (wiresFrom (acc.2 ++ [⟨GateOp.or, [h, j]⟩]) (List.ofFn x)).getD
        (n + acc.2.length) false = _
      rw [wiresFrom_append]
      have hl : n + acc.2.length = (wiresFrom acc.2 (List.ofFn x)).length := by
        simp [length_wiresFrom]
      rw [hl]
      have he : ∀ w : List Bool,
          (wiresFrom [⟨GateOp.or, [h, j]⟩] w).getD w.length false =
            (w.getD h false || w.getD j false) := by
        intro w
        simp [wiresFrom, GateOp.eval]
      rw [he, hwire]
      cases hv : (wiresFrom (ps ++ qs) (List.ofFn x)).getD h false with
      | false =>
        have e := hval x hv
        rw [hs] at e
        exact e
      | true => simpa using (hf x hv).symm
    · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
      omega

theorem readers_norm (n h : ℕ) (gs : List Gate) :
    readers n h (gs.map normGate) = gs.zipIdx.countP (fun p =>
      decide (h < n + p.2) &&
        (GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs
          (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains h) := by
  unfold readers
  rw [List.zipIdx_map, List.zipIdx_eq_map_add]
  simp only [List.countP_map]
  apply List.countP_congr
  rintro ⟨⟨op, ins⟩, j⟩ _
  cases op <;> rfl

end PEqualNP.Outside.Absorb193

open PEqualNP.Outside.Absorb193 in
theorem PEqualNP.Outside.L_meta_193 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (h : ℕ), PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains h) ≤ C.size + 1 := by
  intro n C h hok hf
  let gs := C.gates.map normGate
  have hlen : gs.length = C.gates.length := by simp [gs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g' (hok g' hg')
  have hsame : ∀ x : Fin n → Bool,
      wiresFrom gs (List.ofFn x) = C.wires (List.ofFn x) := by
    intro x
    exact wiresFrom_norm C.gates (List.ofFn x)
  have hcount := readers_norm n h C.gates
  change readers n h gs = _ at hcount
  by_cases hh : h < n + gs.length
  · let k := h + 1 - n
    let ps := gs.take k
    let qs := gs.drop k
    have hk : k ≤ gs.length := by dsimp [k]; omega
    have hpLen : ps.length = k := by simp [ps, hk]
    have hp : h < n + ps.length := by rw [hpLen]; dsimp [k]; omega
    have hsplit : ps ++ qs = gs := List.take_append_drop k gs
    have hbefore : readers n h ps = 0 := by
      by_cases hn : h < n
      · have hk0 : k = 0 := by dsimp [k]; omega
        simp [ps, hk0, readers]
      · apply readers_before
        rw [hpLen]
        dsimp [k]
        omega
    have hr : readers n h gs = qs.countP (fun g => g.inputs.contains h) := by
      rw [← hsplit, readers_append, hbefore, zero_add, readers_after _ _ _ hp]
    have hokps : ∀ g ∈ ps, Ok g := by
      intro g hg
      exact (hnok g (List.mem_of_mem_take hg)).1
    have hokqs : ∀ g ∈ qs, NOk g := by
      intro g hg
      exact hnok g (List.mem_of_mem_drop hg)
    have hf' : ∀ x : Fin n → Bool,
        (wiresFrom (ps ++ qs) (List.ofFn x)).getD h false = true →
        (wiresFrom (ps ++ qs) (List.ofFn x)).getD C.output false = true := by
      intro x hx
      rw [hsplit, hsame] at hx ⊢
      exact hf x hx
    obtain ⟨D, hd, he, hs⟩ := absorb_split n h ps qs C.output hp hokps hokqs hf'
    refine ⟨D, hd, ?_, ?_⟩
    · funext x
      change D.eval (List.ofFn x) = C.eval (List.ofFn x)
      rw [he x, hsplit, hsame]
      rfl
    · rw [← hcount, hr]
      have hl : ps.length + qs.length = C.size := by
        rw [← List.length_append, hsplit, hlen]
        rfl
      simpa only [hl] using hs
  · have hr : readers n h gs = 0 := readers_before n h gs (by omega)
    refine ⟨C, hok, rfl, ?_⟩
    rw [← hcount, hr]
    omega
