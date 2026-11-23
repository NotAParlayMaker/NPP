import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.OrChain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire evaluator and gate simplification pass adapt the project helpers for fixed inputs.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
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

abbrev Stat := Bool ⊕ ℕ

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
  | [Sum.inr j, Sum.inr k] => if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (try split at hg) <;> simp at hg <;> subst g <;> simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (try split at hg) <;> simp at hg <;> subst g <;> simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        | inr k => cases c <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      | inr j =>
        cases b with
        | inl d => cases d <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        | inr k =>
          by_cases hjk : j = k
          · subst k
            simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
          · simp_all [simplify, simpAnd, hjk, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        | inr k => cases c <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      | inr j =>
        cases b with
        | inl d => cases d <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        | inr k =>
          by_cases hjk : j = k
          · subst k
            simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
          · simp_all [simplify, simpOr, hjk, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
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

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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

lemma elim_append (m : ℕ) (pre post : List Gate) (a : List Stat × List Gate) :
    elim m (pre ++ post) a = elim m post (elim m pre a) := by
  simp [elim, List.foldl_append]

lemma elim_fst_length (m : ℕ) (gs : List Gate) (a : List Stat × List Gate) :
    (elim m gs a).1.length = a.1.length + gs.length := by
  induction gs generalizing a with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim m gs (elimStep m a g)).1.length = _
    rw [ih]
    simp [elimStep]
    omega

def reader (g : Gate) (w : ℕ) : Prop := w ∈ (normGate g).inputs

lemma reader_iff (g : Gate) (w : ℕ) :
    reader g w ↔ (g.op = GateOp.not ∧ g.inputs.head? = some w) ∨
      (g.op ≠ GateOp.not ∧ w ∈ g.inputs) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [reader, normGate, eq_comm]

def initial (k : ℕ) (forced : Option ℕ) : List Stat :=
  List.ofFn fun i : Fin k => if forced = some i.val then Sum.inl false else Sum.inr i.val

lemma initial_length (k : ℕ) (forced : Option ℕ) : (initial k forced).length = k := by
  simp [initial]

lemma initial_const (k v : ℕ) (hv : v < k) :
    (initial k (some v)).getD v (Sum.inl false) = Sum.inl false := by
  simp [initial, hv]

def masked (forced : Option ℕ) (w : List Bool) : List Bool :=
  match forced with
  | none => w
  | some v => w.set v false

lemma getD_masked (w : List Bool) (forced : Option ℕ) (j : ℕ) :
    (masked forced w).getD j false = if forced = some j then false else w.getD j false := by
  cases forced with
  | none => simp [masked]
  | some v =>
    by_cases hv : v = j
    · subst v
      by_cases hj : j < w.length
      · simp [masked, hj]
      · rw [List.getD_eq_default _ _ (by simpa [masked] using Nat.le_of_not_gt hj)]
        simp
    · simp [masked, hv, Ne.symm hv, List.getElem?_set_ne]

lemma inv_prefix (m : ℕ) (y : List Bool) (hy : y.length = m) (pre : List Gate)
    (forced : Option ℕ) :
    Inv m y (masked forced (wiresFrom pre y)) (initial (m + pre.length) forced, pre) := by
  let w := wiresFrom pre y
  have hw : w.length = m + pre.length := by simp [w, length_wiresFrom, hy]
  constructor
  · cases forced <;> simp [initial, masked, length_wiresFrom, hy]
  intro j
  change _ ∧ _ = (masked forced w).getD j false
  rw [getD_masked]
  by_cases hj : j < m + pre.length
  · by_cases hf : forced = some j <;> simp [initial, hj, hf, Stat.Valid, Stat.val, w]
  · have h := Nat.le_of_not_gt hj
    rw [List.getD_eq_default _ _ (by simpa [initial] using h)]
    have hwj : w.getD j false = false := List.getD_eq_default _ _ (by omega)
    rw [hwj]
    simp [Stat.Valid, Stat.val]

lemma masked_eq_self {w : List Bool} {v : ℕ} (h : w.getD v false = false) :
    masked (some v) w = w := by
  apply List.ext_getElem
  · simp [masked]
  · intro i h₁ h₂
    by_cases hi : v = i
    · subst v
      simpa [masked, h₂] using h.symm
    · simp [masked, hi, Ne.symm hi, List.getElem_set_ne]

lemma skip_reader {m v : ℕ} {a : List Stat × List Gate} {g : Gate}
    (hg : NOk g) (hr : v ∈ g.inputs) (hc : ∃ b, a.1.getD v (Sum.inl false) = Sum.inl b) :
    (elimStep m a g).2.length = a.2.length := by
  obtain ⟨b, hb⟩ := hc
  have hn := simplify_count g.op (m + a.2.length)
    (g.inputs.map fun i => a.1.getD i (Sum.inl false)) hg.1.1
    (by simpa using hg.1.2) (by intro h; simpa using hg.2 h)
    ⟨b, List.mem_map.mpr ⟨v, hr, hb⟩⟩
  change (a.2 ++ (simplify g.op (m + a.2.length) _).1.toList).length = _
  rw [hn]
  simp

lemma skip_one (m : ℕ) (gs : List Gate) (a : List Stat × List Gate) (j : Fin gs.length)
    (hs : (elimStep m (elim m (gs.take j) a) (gs.get j)).2.length =
      (elim m (gs.take j) a).2.length) :
    (elim m gs a).2.length + 1 ≤ a.2.length + gs.length := by
  have hsplit : gs.take j ++ gs.get j :: gs.drop (j.val + 1) = gs := by
    rw [List.get_eq_getElem, List.getElem_cons_drop, List.take_append_drop]
  have h := elim_len m (gs.take j) a
  have h' := elim_len m (gs.drop (j.val + 1)) (elimStep m (elim m (gs.take j) a) (gs.get j))
  conv_lhs => rw [← hsplit, elim_append]
  change (elim m (gs.drop (j.val + 1)) (elimStep m (elim m (gs.take j) a) (gs.get j))).2.length + 1 ≤ _
  simp only [List.length_take, List.length_drop] at h h'
  rw [hs] at h'
  omega

lemma elim_cons (m : ℕ) (g : Gate) (gs : List Gate) (a : List Stat × List Gate) :
    elim m (g :: gs) a = elim m gs (elimStep m a g) := rfl

lemma elim_take_succ (m : ℕ) (gs : List Gate) (a : List Stat × List Gate) (j : Fin gs.length) :
    elim m (gs.take (j.val + 1)) a = elimStep m (elim m (gs.take j) a) (gs.get j) := by
  rw [List.take_succ_eq_append_getElem j.isLt, elim_append]
  rfl

lemma elim_mid (m : ℕ) (gs : List Gate) (a : List Stat × List Gate)
    (i j : ℕ) (hij : i ≤ j) :
    elim m (gs.take j) a =
      elim m ((gs.take j).drop i) (elim m (gs.take i) a) := by
  conv_lhs => rw [← List.take_append_drop i (gs.take j), elim_append, List.take_take, Nat.min_eq_left hij]

lemma skip_two (m : ℕ) (gs : List Gate) (a : List Stat × List Gate) (j k : Fin gs.length)
    (hjk : j.val < k.val)
    (hsj : (elimStep m (elim m (gs.take j) a) (gs.get j)).2.length =
      (elim m (gs.take j) a).2.length)
    (hsk : (elimStep m (elim m (gs.take k) a) (gs.get k)).2.length =
      (elim m (gs.take k) a).2.length) :
    (elim m gs a).2.length + 2 ≤ a.2.length + gs.length := by
  have h := skip_one m gs a k hsk
  have hsplit : gs.take k ++ gs.get k :: gs.drop (k.val + 1) = gs := by
    rw [List.get_eq_getElem, List.getElem_cons_drop, List.take_append_drop]
  have hpre := elim_len m (gs.take j) a
  have hmid := elim_len m ((gs.take k).drop (j.val + 1)) (elim m (gs.take (j.val + 1)) a)
  have hpost := elim_len m (gs.drop (k.val + 1)) (elimStep m (elim m (gs.take k) a) (gs.get k))
  rw [← elim_mid m gs a (j.val + 1) k (by omega)] at hmid
  have hj : (elim m (gs.take (j.val + 1)) a).2.length = (elim m (gs.take j) a).2.length := by
    rw [elim_take_succ, hsj]
  rw [hj] at hmid
  rw [hsk] at hpost
  conv_lhs => rw [← hsplit, elim_append, elim_cons]
  simp only [List.length_take, List.length_drop] at hpre hmid hpost
  omega

lemma skip_when_const (m : ℕ) (gs : List Gate) (a : List Stat × List Gate)
    (i j : ℕ) (hij : i ≤ j) (v : ℕ) (hv : v < (elim m (gs.take i) a).1.length) :
    (elim m (gs.take j) a).1.getD v (Sum.inl false) =
      (elim m (gs.take i) a).1.getD v (Sum.inl false) := by
  rw [elim_mid m gs a i j hij, elim_getD _ _ _ _ _ hv]

lemma simplify_emits_binary (op : GateOp) (m : ℕ) (ins : List Stat)
    (hb : op = GateOp.and ∨ op = GateOp.or)
    (h : (simplify op m ins).1 ≠ none) :
    ∃ a b : ℕ, a ≠ b ∧ ins = [Sum.inr a, Sum.inr b] := by
  rcases hb with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp [simplify, simpAnd] at h
    · cases a <;> simp [simplify, simpAnd] at h
    · cases a <;> cases b <;> simp_all [simplify, simpAnd] <;> split at h <;> simp_all
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp [simplify, simpOr] at h
    · cases a <;> simp [simplify, simpOr] at h
    · cases a <;> cases b <;> simp_all [simplify, simpOr] <;> split at h <;> simp_all

lemma elim_gates_prefix (m : ℕ) (gs : List Gate) (a : List Stat × List Gate) :
    ∃ more, (elim m gs a).2 = a.2 ++ more := by
  induction gs generalizing a with
  | nil => exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    obtain ⟨more, hm⟩ := ih (elimStep m a g)
    rw [elim_cons, hm]
    exact ⟨_, List.append_assoc _ _ _⟩

def value {m : ℕ} (C : Circuit) (x : Fin m → Bool) (v : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD v false

lemma circuitFun_eq_value (m : ℕ) (C : Circuit) (x : Fin m → Bool) :
    circuitFun m C x = value C x C.output := rfl

lemma inv_simulation (m : ℕ) (C : Circuit) (pre tail : List Gate)
    (hs : C.gates = pre ++ tail) (hf : FanInTwo C) (forced : Option ℕ) (x : Fin m → Bool) :
    Inv m (List.ofFn x) (wiresFrom tail (masked forced (wiresFrom pre (List.ofFn x))))
      (elim m (tail.map normGate) (initial (m + pre.length) forced, pre)) := by
  rw [← wiresFrom_norm tail]
  apply inv_elim m _ (by simp)
  · intro g hg
    obtain ⟨g₀, hm, rfl⟩ := List.mem_map.mp hg
    exact (normGate_nok g₀ (hf g₀ (by rw [hs]; exact List.mem_append_right _ hm))).1
  · exact inv_prefix m _ (by simp) pre forced

-- Simplification without a fixed wire cannot delete a gate of a minimal circuit.
lemma no_saved_gate (m : ℕ) (C : Circuit) (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output) :
    C.gates.length ≤ (elim m (C.gates.map normGate) (initial m none, [])).2.length := by
  let a := elim m (C.gates.map normGate) (initial m none, [])
  have hh (x : Fin m → Bool) :
      (a.1.getD C.output (Sum.inl false)).val (wiresFrom a.2 (List.ofFn x)) =
        value C x C.output := by
    simpa [a, masked, wiresFrom, value] using
      ((inv_simulation m C [] C.gates (by simp) hmin.1 none x).2 C.output).2
  cases hs : a.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, y, hn⟩ := hnc
    have hx := hh x
    have hy := hh y
    rw [hs] at hx hy
    exact False.elim (hn (hx.symm.trans hy))
  | inr o =>
    apply hmin.2 ⟨a.2, o⟩ (elim_ok m _ _ (by simp))
    funext x
    have hx := hh x
    rw [hs] at hx
    exact hx

def restore (m v o : ℕ) (a : List Stat × List Gate) : Circuit :=
  match a.1.getD o (Sum.inl false) with
  | Sum.inl false => ⟨a.2, v⟩
  | Sum.inl true => ⟨a.2 ++ [⟨GateOp.and, []⟩], m + a.2.length⟩
  | Sum.inr j => ⟨a.2 ++ [⟨GateOp.or, [v, j]⟩], m + a.2.length⟩

lemma restore_bound (m v o : ℕ) (a : List Stat × List Gate) :
    (restore m v o a).size ≤ a.2.length + 1 := by
  unfold restore
  split
  all_goals simp [Circuit.size]

lemma restore_ok (m v o : ℕ) (a : List Stat × List Gate)
    (ha : ∀ g ∈ a.2, Ok g) : FanInTwo (restore m v o a) := by
  unfold restore
  split
  · exact ha
  all_goals
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact ha _ h
    · simp

lemma restore_value (m v o : ℕ) (a : List Stat × List Gate) (x : Fin m → Bool) :
    let w := wiresFrom a.2 (List.ofFn x)
    circuitFun m (restore m v o a) x =
      (w.getD v false || (a.1.getD o (Sum.inl false)).val w) := by
  let w := wiresFrom a.2 (List.ofFn x)
  have hw : w.length = m + a.2.length := by simp [w, length_wiresFrom]
  rw [circuitFun_eq_value]
  unfold restore
  split
  · rename_i h
    rw [h]
    simp [value, Stat.val]
  · change (wiresFrom (a.2 ++ [_]) (List.ofFn x)).getD (m + a.2.length) false = _
    rw [wiresFrom_append, ← hw]
    rename_i h
    rw [h]
    change (w ++ [true]).getD w.length false = _
    simp [Stat.val]
  · rename_i j hj
    change (wiresFrom (a.2 ++ [_]) (List.ofFn x)).getD (m + a.2.length) false = _
    rw [wiresFrom_append, ← hw]
    rw [hj]
    change (w ++ [w.getD v false || (w.getD j false || false)]).getD w.length false = _
    simp only [Bool.or_false, getD_snoc_eq, Stat.val]
    rfl

-- Reattach a fixed wire at the output. If it is true, the original output is already true.
lemma cut_saves_at_most_one (m : ℕ) (C : Circuit) (hmin : IsMinimalCircuit m C)
    (pre tail : List Gate) (hs : C.gates = pre ++ tail) (v : ℕ) (hv : v < m + pre.length)
    (hd : ∀ x : Fin m → Bool, value C x v = true → value C x C.output = true) :
    C.gates.length ≤ (elim m (tail.map normGate) (initial (m + pre.length) (some v), pre)).2.length + 1 := by
  let a := elim m (tail.map normGate) (initial (m + pre.length) (some v), pre)
  obtain ⟨more, hmore⟩ := elim_gates_prefix m (tail.map normGate) (initial (m + pre.length) (some v), pre)
  change a.2 = pre ++ more at hmore
  refine (hmin.2 (restore m v C.output a) (restore_ok m v C.output a (elim_ok m _ _ ?_)) ?_).trans
    (restore_bound m v C.output a)
  · intro g hg
    exact hmin.1 g (by rw [hs]; exact List.mem_append_left _ hg)
  · funext x
    have hlen : v < (wiresFrom pre (List.ofFn x)).length := by simpa [length_wiresFrom] using hv
    have hval : (wiresFrom a.2 (List.ofFn x)).getD v false = value C x v := by
      rw [hmore, value, hs, wiresFrom_append, wiresFrom_append,
        getD_wiresFrom _ _ _ hlen, getD_wiresFrom _ _ _ hlen]
    rw [restore_value, hval, circuitFun_eq_value]
    cases hb : value C x v
    · have hp : (wiresFrom pre (List.ofFn x)).getD v false = false := by
        rw [value, hs, wiresFrom_append, getD_wiresFrom _ _ _ hlen] at hb
        exact hb
      have hi := ((inv_simulation m C pre tail hs hmin.1 (some v) x).2 C.output).2
      rw [masked_eq_self hp, ← wiresFrom_append, ← hs] at hi
      simpa [value, a] using hi
    · simp [hd x hb]

lemma op_norm (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

lemma norm_not_mem {g : Gate} (h : g.op ≠ GateOp.not) : normGate g = g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [normGate]

def regular (w : ℕ) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b, a < w ∧ b < w ∧ a ≠ b ∧ (normGate g).inputs = [a, b]) ∨
  (g.op = GateOp.not ∧ ∃ a, a < w ∧ (normGate g).inputs = [a])

lemma regular_of_emits (m : ℕ) (a : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (h : (elimStep m a g).2.length ≠ a.2.length) :
    (∃ u v, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      u < a.1.length ∧ v < a.1.length ∧ u ≠ v ∧ g.inputs = [u, v]) ∨
    (∃ u, g.op = GateOp.not ∧ u < a.1.length ∧ g.inputs = [u]) := by
  let f := fun i => a.1.getD i (Sum.inl false)
  have hf {i j : ℕ} (hi : f i = Sum.inr j) : i < a.1.length := by
    by_contra! hh
    have hd : f i = Sum.inl false := List.getD_eq_default _ _ hh
    rw [hd] at hi
    cases hi
  have he : (simplify g.op (m + a.2.length) (g.inputs.map f)).1 ≠ none := by
    intro hh
    apply h
    change (a.2 ++ (simplify g.op (m + a.2.length) (g.inputs.map f)).1.toList).length = _
    rw [hh]
    simp
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1.1
  by_cases hn : g.op = GateOp.not
  · have hlen := hg.2 hn
    rcases e : g.inputs with _ | ⟨u, _ | ⟨v, more⟩⟩
    · exact False.elim (he (by simp [hn, e, simplify, simpNot]))
    · cases hu : f u with
      | inl c =>
        exact False.elim (he (by simp [hn, e, simplify, simpNot, hu]))
      | inr j => exact Or.inr ⟨u, hn, hf hu, rfl⟩
    · simp [e] at hlen
  · have hb : g.op = GateOp.and ∨ g.op = GateOp.or := by tauto
    obtain ⟨i, j, hij, hins⟩ := simplify_emits_binary _ _ _ hb he
    rcases e : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, more⟩⟩⟩ <;> simp [e] at hins
    refine Or.inl ⟨u, v, hb, hf hins.1, hf hins.2, ?_, rfl⟩
    intro hv
    subst v
    exact hij (Sum.inr.inj (hins.1.symm.trans hins.2))

lemma gate_regular (m : ℕ) (C : Circuit) (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output)
    (j : Fin C.gates.length) : regular (m + j.val) (C.gates.get j) := by
  let gs := C.gates.map normGate
  let a : List Stat × List Gate := (initial m none, [])
  let j' : Fin gs.length := ⟨j.val, by simpa [gs] using j.isLt⟩
  let a' := elim m (gs.take j') a
  have he : (elimStep m a' (gs.get j')).2.length ≠ a'.2.length := by
    intro hh
    have h := skip_one m gs a j' hh
    have h' := no_saved_gate m C hmin hnc
    change C.gates.length ≤ (elim m gs a).2.length at h'
    have h'': (elim m gs a).2.length + 1 ≤ C.gates.length := by
      simpa only [a, List.length_nil, zero_add, gs, List.length_map] using h
    omega
  have hl : a'.1.length = m + j.val := by
    simp [a', elim_fst_length, a, initial, j', gs, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  have hg : gs.get j' = normGate (C.gates.get j) := by simp [gs, j', List.get_eq_getElem]
  have hk : Ok (C.gates.get j) := hmin.1 _ (List.get_mem _ _)
  rw [hg] at he
  have h := regular_of_emits _ _ _ (normGate_nok _ hk) he
  rcases h with ⟨u, v, hop, hu, hv, hne, hins⟩ | ⟨u, hop, hu, hins⟩
  · exact Or.inl ⟨by simpa only [op_norm] using hop, u, v, hl ▸ hu, hl ▸ hv, hne, hins⟩
  · exact Or.inr ⟨by simpa only [op_norm] using hop, u, hl ▸ hu, hins⟩

lemma regular_reader_lt {w v : ℕ} {g : Gate} (hg : regular w g) (hr : reader g v) : v < w := by
  rcases hg with ⟨_, a, b, ha, hb, _, e⟩ | ⟨_, a, ha, e⟩
  · have h : v = a ∨ v = b := by simpa [reader, e] using hr
    rcases h with rfl | rfl
    · exact ha
    · exact hb
  · have h : v = a := by simpa [reader, e] using hr
    exact h ▸ ha

lemma value_gate (m : ℕ) (C : Circuit) (j : Fin C.gates.length) (x : Fin m → Bool) :
    let g := normGate (C.gates.get j)
    value C x (m + j.val) = g.op.eval (g.inputs.map fun i =>
      (wiresFrom (C.gates.take j) (List.ofFn x)).getD i false) := by
  have hsplit : C.gates.take j ++ C.gates.get j :: C.gates.drop (j.val + 1) = C.gates := by
    rw [List.get_eq_getElem, List.getElem_cons_drop, List.take_append_drop]
  let w := wiresFrom (C.gates.take j) (List.ofFn x)
  have hw : w.length = m + j.val := by
    simp [w, length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  dsimp only
  unfold value
  have he := congrArg (fun (l : List Gate) => (wiresFrom l (List.ofFn x)).getD (m + j.val) false) hsplit
  rw [← he, wiresFrom_append]
  change (wiresFrom (C.gates.drop (j.val + 1)) (w ++ [_])).getD (m + j.val) false = _
  rw [getD_wiresFrom _ _ _ (by simp [hw]), ← hw, getD_snoc_eq, normGate_eval]

lemma value_gate_regular (m : ℕ) (C : Circuit) (j : Fin C.gates.length) (x : Fin m → Bool)
    (hr : regular (m + j.val) (C.gates.get j)) :
    let g := normGate (C.gates.get j)
    value C x (m + j.val) = g.op.eval (g.inputs.map fun i => value C x i) := by
  rw [value_gate]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h : i < m + j.val := regular_reader_lt hr hi
  have hd : i < (wiresFrom (C.gates.take j) (List.ofFn x)).length := by
    simpa [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt j.isLt)] using h
  conv_rhs => rw [value, ← List.take_append_drop (j : ℕ) C.gates, wiresFrom_append]
  exact (getD_wiresFrom _ _ _ hd).symm

def leads {m : ℕ} (C : Circuit) (v : ℕ) : Prop :=
  ∀ x : Fin m → Bool, value C x v = true → value C x C.output = true

lemma const_after_non_or (m : ℕ) (a : List Stat × List Gate) (g : Gate) (v : ℕ)
    (hr : reader g v) (hw : regular a.1.length g) (ho : g.op ≠ GateOp.or)
    (hv : a.1.getD v (Sum.inl false) = Sum.inl false) :
    ∃ b, (elimStep m a (normGate g)).1.getD a.1.length (Sum.inl false) = Sum.inl b := by
  simp only [elimStep]
  rw [getD_snoc_eq, op_norm]
  rcases hw with ⟨hop, i, j, _, _, _, hi⟩ | ⟨hop, i, _, hi⟩
  · have ha : g.op = GateOp.and := hop.resolve_right ho
    have h : v = i ∨ v = j := by simpa [reader, hi] using hr
    refine ⟨false, ?_⟩
    rw [ha, hi]
    simp only [List.map_cons, List.map_nil]
    rcases h with rfl | rfl
    · rw [hv]
      cases a.1.getD j (Sum.inl false) <;> simp [simplify, simpAnd]
    · rw [hv]
      cases a.1.getD i (Sum.inl false) <;> simp [simplify, simpAnd]
  · have h : v = i := by simpa [reader, hi] using hr
    subst i
    exact ⟨true, by simp only [hop, hi, List.map_cons, List.map_nil, hv, simplify, simpNot, Bool.not_false]⟩

-- Two gates that disappear after fixing a wire would give a strictly smaller circuit.
lemma cut_two_forbidden {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output)
    (v : ℕ) (hv : leads (m := m) C v)
    (j k : Fin C.gates.length) (hjk : j < k)
    (hj : reader (C.gates.get j) v)
    (hk : reader (C.gates.get k) v ∨
      ((C.gates.get j).op ≠ GateOp.or ∧ reader (C.gates.get k) (m + j.val))) : False := by
  let pre := C.gates.take j
  let tail := C.gates.drop j
  let gs := tail.map normGate
  let a : List Stat × List Gate := (initial (m + pre.length) (some v), pre)
  have hp : pre.length = j.val := List.length_take_of_le j.isLt.le
  have htail : tail.length = C.gates.length - j.val := List.length_drop
  have hgs : gs.length = C.gates.length - j.val := by simp only [gs, List.length_map, htail]
  have hjk' : j.val < k.val := hjk
  let i₁ : Fin gs.length := ⟨0, by rw [hgs]; omega⟩
  let i₂ : Fin gs.length := ⟨k.val - j.val, by rw [hgs]; omega⟩
  have ib : i₁.val < i₂.val := by change 0 < k.val - j.val; omega
  have eq₁ : gs.get i₁ = normGate (C.gates.get j) := by
    simp [gs, tail, i₁, List.get_eq_getElem, List.getElem_drop]
  have eq₂ : gs.get i₂ = normGate (C.gates.get k) := by
    have eq : j.val + (k.val - j.val) = k.val := by omega
    simp only [gs, tail, i₂, List.get_eq_getElem, List.getElem_map, List.getElem_drop, eq]
  have ok₁ : NOk (gs.get i₁) := by rw [eq₁]; exact normGate_nok _ (hmin.1 _ (List.get_mem _ _))
  have ok₂ : NOk (gs.get i₂) := by rw [eq₂]; exact normGate_nok _ (hmin.1 _ (List.get_mem _ _))
  have reg := gate_regular m C hmin hnc j
  have hvpre : v < m + pre.length := hp ▸ regular_reader_lt reg hj
  have ha : a.1.length = m + pre.length := initial_length _ _
  have hc₀ : a.1.getD v (Sum.inl false) = Sum.inl false := initial_const _ _ hvpre
  have hpre₀ : elim m (gs.take i₁) a = a := rfl
  have hskip₁ : (elimStep m (elim m (gs.take i₁) a) (gs.get i₁)).2.length =
      (elim m (gs.take i₁) a).2.length := by
    rw [hpre₀]
    exact skip_reader ok₁ (eq₁ ▸ hj) ⟨false, hc₀⟩
  have hskip₂ : (elimStep m (elim m (gs.take i₂) a) (gs.get i₂)).2.length =
      (elim m (gs.take i₂) a).2.length := by
    rcases hk with hk | ⟨ho, hk⟩
    · have hread : v ∈ (gs.get i₂).inputs := by rw [eq₂]; exact hk
      apply skip_reader ok₂ hread
      refine ⟨false, ?_⟩
      rw [skip_when_const m gs a 0 i₂ (Nat.zero_le _) v (by simpa [elim, ha] using hvpre)]
      exact hc₀
    · have hw : regular a.1.length (C.gates.get j) := by simpa [ha, hp] using reg
      obtain ⟨b, hb⟩ := const_after_non_or m a _ v hj hw ho hc₀
      have hstep : elim m (gs.take 1) a = elimStep m a (normGate (C.gates.get j)) := by
        change elim m (gs.take (i₁.val + 1)) a = _
        rw [elim_take_succ, hpre₀, eq₁]
      have hlen : m + j.val < (elim m (gs.take 1) a).1.length := by
        simp [elim_fst_length, ha, hp, Nat.min_eq_left (show 1 ≤ gs.length by omega)]
      have hread : m + j.val ∈ (gs.get i₂).inputs := by rw [eq₂]; exact hk
      apply skip_reader ok₂ hread
      refine ⟨b, ?_⟩
      rw [skip_when_const m gs a 1 i₂ (by exact ib) (m + j.val) hlen, hstep, ← hp, ← ha]
      exact hb
  have h := skip_two m gs a i₁ i₂ ib hskip₁ hskip₂
  have h' := cut_saves_at_most_one m C hmin pre tail (List.take_append_drop _ _).symm v hvpre hv
  have hl : a.2.length + gs.length = C.gates.length := by
    change pre.length + gs.length = _
    rw [hp, hgs]
    omega
  rw [hl] at h
  change C.gates.length ≤ (elim m gs a).2.length + 1 at h'
  omega

lemma unique_reader {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output)
    {v : ℕ} (hv : leads (m := m) C v) (j k : Fin C.gates.length)
    (hj : reader (C.gates.get j) v) (hk : reader (C.gates.get k) v) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact False.elim (cut_two_forbidden hmin hnc v hv j k h hj (Or.inl hk))
  · exact h
  · exact False.elim (cut_two_forbidden hmin hnc v hv k j h hk (Or.inl hj))

lemma value_kept_by_take (m : ℕ) (C : Circuit) (j w : ℕ) (hj : j ≤ C.gates.length)
    (hw : w < m + j) (x : Fin m → Bool) :
    value ⟨C.gates.take j, C.output⟩ x w = value C x w := by
  conv_rhs => rw [value, ← List.take_append_drop j C.gates, wiresFrom_append]
  have h : w < (wiresFrom (C.gates.take j) (List.ofFn x)).length := by
    simpa [length_wiresFrom, List.length_take_of_le hj] using hw
  exact (getD_wiresFrom _ _ _ h).symm

lemma final_reader_or {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output)
    {v : ℕ} (hv : leads (m := m) C v) (htrue : ∃ x : Fin m → Bool, value C x v = true)
    (j : Fin C.gates.length) (hj : reader (C.gates.get j) v)
    (hout : m + j.val = C.output) : (C.gates.get j).op = GateOp.or := by
  have hg := gate_regular m C hmin hnc j
  have hvlt := regular_reader_lt hg hj
  by_contra ho
  have hfun (x : Fin m → Bool) : value C x C.output = value C x v := by
    rcases hb : value C x v
    · rw [← hout, value_gate_regular m C j x hg]
      rcases hg with ⟨hop, a, b, _, _, _, hin⟩ | ⟨hop, a, _, hin⟩
      · have ha : (C.gates.get j).op = GateOp.and := hop.resolve_right ho
        have hmem : v ∈ (normGate (C.gates.get j)).inputs := hj
        rw [hin] at hmem
        have he : v = a ∨ v = b := by simpa using hmem
        rw [op_norm, ha, hin]
        rcases he with rfl | rfl <;> simp [GateOp.eval, hb]
      · exfalso
        obtain ⟨y, hy⟩ := htrue
        have hmem : v ∈ (normGate (C.gates.get j)).inputs := hj
        rw [hin] at hmem
        have h : v = a := by simpa using hmem
        have hh := hv y hy
        rw [← hout, value_gate_regular m C j y (Or.inr ⟨hop, a, ‹a < m + j.val›, hin⟩)] at hh
        rw [op_norm, hop, hin, ← h] at hh
        simpa [GateOp.eval, hy] using hh
    · exact hv x hb
  let D : Circuit := ⟨C.gates.take j, v⟩
  have hok : FanInTwo D := fun g hg => hmin.1 g (List.mem_of_mem_take hg)
  have hsize := hmin.2 D hok (by
    funext x
    rw [circuitFun_eq_value, circuitFun_eq_value, hfun]
    exact value_kept_by_take m C j v j.isLt.le hvlt x)
  have hlen : D.size = j.val := List.length_take_of_le j.isLt.le
  change C.gates.length ≤ D.size at hsize
  omega

def edge (m : ℕ) (C : Circuit) (v w : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, w = m + j.val ∧ reader (C.gates.get j) v

lemma edge_eq (m : ℕ) (C : Circuit) :
    edge m C = fun a b => ∃ j : Fin C.gates.length, b = m + j.val ∧
      ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨
        (C.gates.get j).op ≠ GateOp.not ∧ a ∈ (C.gates.get j).inputs) := by
  funext a b
  apply propext
  unfold edge
  simp only [reader_iff]

lemma edge_lt {m : ℕ} {C : Circuit} (hreg : ∀ j : Fin C.gates.length, regular (m + j.val) (C.gates.get j))
    {v w : ℕ} (h : edge m C v w) : v < w := by
  obtain ⟨j, rfl, hj⟩ := h
  exact regular_reader_lt (hreg j) hj

lemma path_lt {m : ℕ} {C : Circuit} (hreg : ∀ j : Fin C.gates.length, regular (m + j.val) (C.gates.get j))
    {v w : ℕ} (h : Relation.TransGen (edge m C) v w) : v < w := by
  induction h with
  | single h => exact edge_lt hreg h
  | tail _ h ih => exact ih.trans (edge_lt hreg h)

lemma value_input (m : ℕ) (C : Circuit) (x : Fin m → Bool) (j : Fin m) :
    value C x j.val = x j := by
  unfold value
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp [j.isLt]

lemma equal_off_path {m : ℕ} {C : Circuit} (hreg : ∀ j : Fin C.gates.length, regular (m + j.val) (C.gates.get j))
    (u : Fin m) (x y : Fin m → Bool) (heq : ∀ i : Fin m, i ≠ u → x i = y i)
    (w : ℕ) (hwu : w ≠ u.val) (hnp : ¬ Relation.TransGen (edge m C) u.val w) :
    value C x w = value C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < m
    · rw [value_input m C x ⟨w, hw⟩, value_input m C y ⟨w, hw⟩]
      exact heq ⟨w, hw⟩ (fun e => hwu (congrArg Fin.val e))
    by_cases hw' : w < m + C.gates.length
    · let j : Fin C.gates.length := ⟨w - m, by omega⟩
      have h : w = m + j.val := by simp [j]; omega
      rw [h, value_gate_regular m C j x (hreg j), value_gate_regular m C j y (hreg j)]
      congr 1
      apply List.map_congr_left
      intro v hv
      have hed : edge m C v w := ⟨j, h, hv⟩
      apply ih v (edge_lt hreg hed)
      · intro e
        rw [e] at hed
        exact hnp (Relation.TransGen.single hed)
      · intro hprev
        exact hnp (hprev.tail hed)
    · have hx : value C x w = false := List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)
      have hy : value C y w = false := List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)
      rw [hx, hy]

lemma last_gate {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (j : Fin C.gates.length) (he : C.output = m + j.val) : j.val + 1 = C.gates.length := by
  let D : Circuit := ⟨C.gates.take (j.val + 1), C.output⟩
  have hs : j.val + 1 ≤ C.gates.length := j.isLt
  have hf : FanInTwo D := fun g hg => hmin.1 g (List.mem_of_mem_take hg)
  have hx := hmin.2 D hf (by
    funext x
    rw [circuitFun_eq_value, circuitFun_eq_value]
    exact value_kept_by_take m C (j.val + 1) C.output hs (by omega) x)
  have hsz : D.size = j.val + 1 := List.length_take_of_le hs
  change C.gates.length ≤ D.size at hx
  omega

lemma edge_or_value {m : ℕ} {C : Circuit} (j : Fin C.gates.length)
    (hreg : regular (m + j.val) (C.gates.get j)) (ho : (C.gates.get j).op = GateOp.or)
    {v : ℕ} (hv : reader (C.gates.get j) v) :
    ∃ w, w ≠ v ∧ w < m + j.val ∧ (C.gates.get j).inputs.length = 2 ∧
      w ∈ (C.gates.get j).inputs ∧ ∀ x : Fin m → Bool,
      value C x (m + j.val) = (value C x v || value C x w) := by
  have hnot : (C.gates.get j).op ≠ GateOp.not := by rw [ho]; intro h; cases h
  rcases hreg with ⟨hor, a, b, ha, hb, hne, hin⟩ | ⟨h, _⟩
  · have hraw : (C.gates.get j).inputs = [a, b] := by rwa [norm_not_mem hnot] at hin
    have he : v = a ∨ v = b := by
      have hmem : v ∈ (normGate (C.gates.get j)).inputs := hv
      rw [hin] at hmem
      simpa using hmem
    have hval (x : Fin m → Bool) : value C x (m + j.val) = (value C x a || value C x b) := by
      rw [value_gate_regular m C j x (Or.inl ⟨hor, a, b, ha, hb, hne, hin⟩)]
      rw [op_norm, ho, hin]
      simp [GateOp.eval]
    rcases he with rfl | rfl
    · exact ⟨b, Ne.symm hne, hb, by rw [hraw]; simp, by rw [hraw]; simp, hval⟩
    · exact ⟨a, hne, ha, by rw [hraw]; simp, by rw [hraw]; simp, fun x => (hval x).trans (Bool.or_comm _ _)⟩
  · exact (hnot h).elim

-- The set contains the chain built so far. Only its last wire can reach a new gate directly.
def frontier (m : ℕ) (C : Circuit) (n v : ℕ) (S : Set ℕ) : Prop :=
  n ∈ S ∧ (∀ a ∈ S, a ≤ v) ∧
    ∀ a b, a ∈ S → a ≠ v → edge m C a b → b ∈ S

lemma agree_beyond_frontier {m : ℕ} {C : Circuit}
    (hreg : ∀ j : Fin C.gates.length, regular (m + j.val) (C.gates.get j))
    (u : Fin m) (v : ℕ) (S : Set ℕ) (hs : frontier m C u.val v S)
    (x y : Fin m → Bool) (heq : ∀ i : Fin m, i ≠ u → x i = y i)
    (hv : value C x v = value C y v) (w : ℕ) (hw : w ∉ S) :
    value C x w = value C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hb : w < m
    · rw [value_input m C x ⟨w, hb⟩, value_input m C y ⟨w, hb⟩]
      apply heq
      intro h
      have e : w = u.val := congrArg Fin.val h
      exact hw (e.symm ▸ hs.1)
    by_cases hg : w < m + C.gates.length
    · let j : Fin C.gates.length := ⟨w - m, by omega⟩
      have h : w = m + j.val := by simp [j]; omega
      rw [h, value_gate_regular m C j x (hreg j), value_gate_regular m C j y (hreg j)]
      congr 1
      apply List.map_congr_left
      intro a ha
      have hed : edge m C a w := ⟨j, h, ha⟩
      by_cases e : a = v
      · simpa [e] using hv
      · apply ih a (edge_lt hreg hed)
        exact fun hmem => hw (hs.2.2 a w hmem e hed)
    · have hx : value C x w = false := List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)
      have hy : value C y w = false := List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)
      rw [hx, hy]

lemma extend_frontier {m : ℕ} {C : Circuit} {n v w : ℕ} {S : Set ℕ}
    (hs : frontier m C n v S) (hvw : v < w)
    (hnext : ∀ t, edge m C v t → t = w) :
    frontier m C n w (insert w S) := by
  refine ⟨Set.mem_insert_of_mem _ hs.1, ?_, ?_⟩
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | h
    · exact le_rfl
    · exact (hs.2.1 a h).trans hvw.le
  · intro a b ha hne hed
    obtain rfl | ha := Set.mem_insert_iff.mp ha
    · exact (hne rfl).elim
    by_cases h : a = v
    · subst a
      exact Set.mem_insert_iff.mpr (Or.inl (hnext _ hed))
    · exact Set.mem_insert_of_mem _ (hs.2.2 _ _ ha h hed)

lemma reached_leads {m : ℕ} {C : Circuit}
    (hreg : ∀ j : Fin C.gates.length, regular (m + j.val) (C.gates.get j))
    (u : Fin m) {v : ℕ} {S : Set ℕ} (hs : frontier m C u.val v S)
    (hv : ∀ x : Fin m → Bool, x u = true → value C x v = true)
    (hf : ∀ x : Fin m → Bool, x u = true → value C x C.output = true)
    (hvo : v < C.output) : leads (m := m) C v := by
  intro x hx
  let y := Function.update x u true
  have hy : y u = true := Function.update_self u true x
  have hxy : ∀ i : Fin m, i ≠ u → x i = y i := by
    intro i hi
    exact (Function.update_of_ne hi true x).symm
  have h := agree_beyond_frontier hreg u v S hs x y hxy (hx.trans (hv y hy).symm)
    C.output (fun hm => (not_le_of_gt hvo) (hs.2.1 _ hm))
  exact h.trans (hf y hy)

lemma path_first {m : ℕ} {C : Circuit} {v w : ℕ}
    (h : Relation.TransGen (edge m C) v w) : ∃ t, edge m C v t := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

def chain {m : ℕ} (C : Circuit) (v : ℕ) (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length) : Prop :=
  StrictMono c ∧
  C.output = m + (c (Fin.last k)).val ∧
  reader (C.gates.get (c 0)) v ∧
  (∀ i : Fin k, reader (C.gates.get (c i.succ)) (m + (c i.castSucc).val)) ∧
  ∀ i : Fin (k + 1), (C.gates.get (c i)).op = GateOp.or ∧ leads (m := m) C (m + (c i).val)

lemma build_chain {m : ℕ} {C : Circuit} (u : Fin m) (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output)
    (hf : ∀ x : Fin m → Bool, x u = true → value C x C.output = true)
    {v : ℕ} (hpath : Relation.TransGen (edge m C) v C.output) :
    ∀ S : Set ℕ, frontier m C u.val v S →
      (∀ x : Fin m → Bool, x u = true → value C x v = true) →
      ∃ k c, chain (m := m) C v k c := by
  have reg := gate_regular m C hmin hnc
  induction hpath using Relation.TransGen.head_induction_on with
  | @single a h =>
    intro S hs hv
    obtain ⟨j, hj, hread⟩ := h
    have hlt : a < C.output := edge_lt reg ⟨j, hj, hread⟩
    have hdom := reached_leads reg u hs hv hf hlt
    have ho := final_reader_or hmin hnc hdom ⟨fun _ => true, hv _ rfl⟩ j hread hj.symm
    refine ⟨0, fun _ => j, ?_, hj, hread, Fin.elim0, fun i => ⟨ho, ?_⟩⟩
    · intro i i' hi
      change i.val < i'.val at hi
      have hi₀ := i.isLt
      have hi₁ := i'.isLt
      exact False.elim (by omega)
    · rw [← hj]
      exact fun _ h => h
  | @head a b hed htail ih =>
    intro S hs hv
    obtain ⟨j, rfl, hread⟩ := hed
    have ha : a < m + j.val := regular_reader_lt (reg j) hread
    have hb : m + j.val < C.output := path_lt reg htail
    have hdom := reached_leads reg u hs hv hf (ha.trans hb)
    have ho : (C.gates.get j).op = GateOp.or := by
      by_contra he
      obtain ⟨_, q, _, hr⟩ := path_first htail
      have hq : j < q := by
        have hl := regular_reader_lt (reg q) hr
        exact Fin.lt_def.mpr (by omega)
      exact cut_two_forbidden hmin hnc a hdom j q hq hread (Or.inr ⟨he, hr⟩)
    have only : ∀ t, edge m C a t → t = m + j.val := by
      rintro t ⟨j', rfl, hj'⟩
      rw [unique_reader hmin hnc hdom j' j hj' hread]
    obtain ⟨other, _, _, _, _, hval⟩ := edge_or_value j (reg j) ho hread
    have hs' := extend_frontier hs ha only
    have htrue (x : Fin m → Bool) (hh : x u = true) : value C x (m + j.val) = true := by
      rw [hval x, hv x hh]
      rfl
    have hdom' := reached_leads reg u hs' htrue hf hb
    obtain ⟨k, c, hc, hend, hhd, hnxt, hgate⟩ := ih _ hs' htrue
    refine ⟨k + 1, Fin.cons j c, ?_, ?_, ?_, ?_, ?_⟩
    · have hh := regular_reader_lt (reg (c 0)) hhd
      have hj₀ : j < c 0 := Fin.lt_def.mpr (by omega)
      exact Fin.strictMono_cons.mpr ⟨fun i => hj₀.trans_le (hc.monotone (Fin.zero_le i)), hc⟩
    · simpa only [← Fin.succ_last, Fin.cons_succ] using hend
    · simpa only [Fin.cons_zero] using hread
    · intro i
      cases i using Fin.cases with
      | zero => simpa only [Fin.castSucc_zero, Fin.cons_succ, Fin.cons_zero] using hhd
      | succ i => simpa only [Fin.castSucc_succ, Fin.cons_succ] using hnxt i
    · intro i
      cases i using Fin.cases with
      | zero => simpa only [Fin.cons_zero] using And.intro ho hdom'
      | succ i => simpa only [Fin.cons_succ] using hgate i

lemma or_reads_iff {g : Gate} (ho : g.op = GateOp.or) (v : ℕ) :
    reader g v ↔ v ∈ g.inputs := by
  rw [reader_iff, ho]
  simp

lemma reader_chain_gate {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output)
    {v k : ℕ} {c : Fin (k + 1) → Fin C.gates.length} (hc : chain (m := m) C v k c)
    (i : Fin (k + 1)) (j : Fin C.gates.length)
    (hj : reader (C.gates.get j) (m + (c i).val)) :
    ∃ q : Fin k, i = q.castSucc ∧ j = c q.succ := by
  obtain ⟨_, hout, _, hstep, hgate⟩ := hc
  refine Fin.lastCases (motive := fun i =>
    reader (C.gates.get j) (m + (c i).val) → ∃ q : Fin k, i = q.castSucc ∧ j = c q.succ) ?_ ?_ i hj
  · intro h
    have hlast := last_gate hmin (c (Fin.last k)) hout
    have hlt := regular_reader_lt (gate_regular m C hmin hnc j) h
    omega
  · intro q h
    exact ⟨q, rfl, unique_reader hmin hnc (hgate q.castSucc).2 j (c q.succ) h (hstep q)⟩

lemma chain_reach {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output)
    {v k : ℕ} {c : Fin (k + 1) → Fin C.gates.length}
    (hdom : leads (m := m) C v) (hc : chain (m := m) C v k c) (w : ℕ) :
    Relation.TransGen (edge m C) v w ↔ ∃ i, w = m + (c i).val := by
  have hhead := hc.2.2.1
  have hstep := hc.2.2.2.1
  constructor
  · intro h
    induction h with
    | single h =>
      obtain ⟨j, rfl, hj⟩ := h
      exact ⟨0, by rw [unique_reader hmin hnc hdom j (c 0) hj hhead]⟩
    | tail _ h ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, rfl, hj⟩ := h
      rw [hi] at hj
      obtain ⟨q, _, rfl⟩ := reader_chain_gate hmin hnc hc i j hj
      exact ⟨q.succ, rfl⟩
  · rintro ⟨i, rfl⟩
    induction i using Fin.induction with
    | zero => exact Relation.TransGen.single ⟨c 0, rfl, hhead⟩
    | succ i ih => exact ih.tail ⟨c i.succ, rfl, hstep i⟩

lemma not_reached_first_side {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output)
    {v k : ℕ} {c : Fin (k + 1) → Fin C.gates.length}
    (hdom : leads (m := m) C v) (hc : chain (m := m) C v k c)
    {w : ℕ} (hw : reader (C.gates.get (c 0)) w) :
    ¬ Relation.TransGen (edge m C) v w := by
  intro hpath
  obtain ⟨i, hi⟩ := (chain_reach hmin hnc hdom hc w).mp hpath
  rw [hi] at hw
  obtain ⟨q, _, heq⟩ := reader_chain_gate hmin hnc hc i (c 0) hw
  have bad := congrArg Fin.val (hc.1.injective heq)
  simp at bad

lemma later_side_safe {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y : Fin m → Bool, value C x C.output ≠ value C y C.output)
    {v k : ℕ} {c : Fin (k + 1) → Fin C.gates.length}
    (hdom : leads (m := m) C v) (hc : chain (m := m) C v k c)
    (i : Fin k) {w : ℕ} (hw : reader (C.gates.get (c i.succ)) w)
    (hne : w ≠ m + (c i.castSucc).val) :
    w ≠ v ∧ ¬ Relation.TransGen (edge m C) v w := by
  constructor
  · rintro rfl
    have heq := unique_reader hmin hnc hdom (c i.succ) (c 0) hw hc.2.2.1
    have bad := congrArg Fin.val (hc.1.injective heq)
    simp at bad
  · intro hpath
    obtain ⟨j, he⟩ := (chain_reach hmin hnc hdom hc w).mp hpath
    rw [he] at hw
    obtain ⟨q, hq, hz⟩ := reader_chain_gate hmin hnc hc j (c i.succ) hw
    have eq : i = q := Fin.succ_injective _ (hc.1.injective hz)
    subst q
    exact hne (he.trans (congrArg (fun j => m + (c j).val) hq))

lemma find_chain (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hmin : IsMinimalCircuit (n + 1) C) (hH : ∃ y y', H y ≠ H y')
    (hf : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i => x i.castSucc))) :
    (∃ x y : Fin (n + 1) → Bool, value C x C.output ≠ value C y C.output) ∧
    leads (m := n + 1) C n ∧ ∃ k c, chain (m := n + 1) C n k c := by
  obtain ⟨y, y', hne⟩ := hH
  have hlo : ∃ z, H z = false := by
    cases e : H y with
    | false => exact ⟨y, e⟩
    | true =>
      refine ⟨y', ?_⟩
      cases e' : H y' <;> simp_all
  have hhi : ∃ z, H z = true := by
    cases e : H y with
    | true => exact ⟨y, e⟩
    | false =>
      refine ⟨y', ?_⟩
      cases e' : H y' <;> simp_all
  obtain ⟨z, hz⟩ := hlo
  obtain ⟨t, ht⟩ := hhi
  have heval (s : Fin n → Bool) (b : Bool) :
      value C (Fin.snoc s b) C.output = (b || H s) := by
    simpa only [circuitFun_eq_value, Fin.snoc_last, Fin.snoc_castSucc] using hf (Fin.snoc s b)
  have hdiff : value C (Fin.snoc z false) C.output ≠ value C (Fin.snoc z true) C.output := by
    rw [heval, heval, hz]
    simp
  have hnc : ∃ x y : Fin (n + 1) → Bool, value C x C.output ≠ value C y C.output := ⟨_, _, hdiff⟩
  have hnot : C.output ≠ n := by
    intro e
    have h := heval t false
    rw [e] at h
    change value C (Fin.snoc t false) (Fin.last n).val = _ at h
    rw [value_input, Fin.snoc_last, ht] at h
    cases h
  have hreg := gate_regular (n + 1) C hmin hnc
  have hpath : Relation.TransGen (edge (n + 1) C) n C.output := by
    by_contra h
    apply hdiff
    apply equal_off_path hreg (Fin.last n)
    · intro i hi
      refine Fin.lastCases (motive := fun j => j ≠ Fin.last n →
        (Fin.snoc z false : Fin (n + 1) → Bool) j = (Fin.snoc z true : Fin (n + 1) → Bool) j) ?_ ?_ i hi
      · exact fun hn => (hn rfl).elim
      · intro i _
        simp
    · exact hnot
    · exact h
  have hd (x : Fin (n + 1) → Bool) (hx : x (Fin.last n) = true) : value C x C.output = true := by
    rw [← circuitFun_eq_value, hf, hx]
    rfl
  have hu (x : Fin (n + 1) → Bool) : value C x n = x (Fin.last n) :=
    value_input (n + 1) C x (Fin.last n)
  have hdom : leads (m := n + 1) C n := fun x hx => hd x ((hu x).symm.trans hx)
  have hfront : frontier (n + 1) C (Fin.last n).val n {n} := by
    simp [frontier]
    intro a b ha hna
    exact (hna ha).elim
  exact ⟨hnc, hdom, build_chain (Fin.last n) hmin hnc hd hpath _ hfront
    (fun x hx => (hu x).trans hx)⟩

end PEqualNP.Outside.OrChain

open PEqualNP.Outside.OrChain in
theorem PEqualNP.Outside.L_meta_568 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n →
    Bool) →
    Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C →
    (∃ y y' : Fin n →
    Bool, H y ≠ H y') →
    (∀ x : Fin (n + 1) →
    Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) →
    ∃ (k : ℕ) (c : Fin (k + 1) →
    Fin C.gates.length), StrictMono c ∧
      (c (Fin.last k)).val + 1 = C.gates.length ∧
      C.output = n + 1 + (c (Fin.last k)).val ∧
      (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (C.gates.get (c i)).inputs.length = 2) ∧
      n ∈ (C.gates.get (c 0)).inputs ∧
      (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧
      (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
      n ∈ (C.gates.get j).inputs) →
    j = c 0) ∧
      (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
      (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) →
    j = c i.succ) ∧
      (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
      a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧
      (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧
      w < n + 1 + (c 0).val ∧
      ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
      a ∈ (C.gates.get j).inputs)) n w) ∧
      (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧
      w ≠ n ∧
      w < n + 1 + (c i.succ).val ∧
      ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
      a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hmin hH hf
  obtain ⟨hnc, hdom, k, c, hc⟩ := find_chain n C H hmin hH hf
  obtain ⟨hmono, hout, hhead, hstep, hgate⟩ := hc
  have hchain : chain (m := n + 1) C n k c := ⟨hmono, hout, hhead, hstep, hgate⟩
  have reg := gate_regular (n + 1) C hmin hnc
  have hfirst := edge_or_value (c 0) (reg (c 0)) (hgate 0).1 hhead
  have hnext (i : Fin k) := edge_or_value (c i.succ) (reg (c i.succ)) (hgate i.succ).1 (hstep i)
  have hor (i : Fin (k + 1)) : (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (C.gates.get (c i)).inputs.length = 2 := by
    refine ⟨(hgate i).1, ?_⟩
    cases i using Fin.cases with
    | zero =>
      obtain ⟨_, _, _, h, _, _⟩ := hfirst
      exact h
    | succ i =>
      obtain ⟨_, _, _, h, _, _⟩ := hnext i
      exact h
  refine ⟨k, c, hmono, last_gate hmin (c (Fin.last k)) hout, hout, hor, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (or_reads_iff (hgate 0).1 _).mp hhead
  · intro i
    exact (or_reads_iff (hgate i.succ).1 _).mp (hstep i)
  · intro j hj
    exact unique_reader hmin hnc hdom j (c 0) ((reader_iff _ _).mpr hj) hhead
  · intro i j hj
    exact unique_reader hmin hnc (hgate i.castSucc).2 j (c i.succ) ((reader_iff _ _).mpr hj) (hstep i)
  · intro j
    have h := chain_reach hmin hnc hdom hchain (n + 1 + j.val)
    rw [show (∃ i, n + 1 + j.val = n + 1 + (c i).val) ↔ ∃ i, c i = j from by
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, Fin.ext (by omega)⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, by rw [hi]⟩] at h
    simpa only [edge_eq] using h
  · obtain ⟨w, hn, hlt, _, hmem, _⟩ := hfirst
    refine ⟨w, hmem, hn, hlt, ?_⟩
    have hr := (or_reads_iff (hgate 0).1 w).mpr hmem
    simpa only [edge_eq] using not_reached_first_side hmin hnc hdom hchain hr
  · intro i
    obtain ⟨w, hn, hlt, _, hmem, _⟩ := hnext i
    have hr := (or_reads_iff (hgate i.succ).1 w).mpr hmem
    obtain ⟨hn', hnr⟩ := later_side_safe hmin hnc hdom hchain i hr hn
    refine ⟨w, hmem, hn, hn', hlt, ?_⟩
    simpa only [edge_eq] using hnr
