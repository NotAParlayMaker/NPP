import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2553

open PEqualNP.CircuitLowerBounds

-- Gate simplification adapted from this project's Shannon, Support, Elim and Parity helpers.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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


def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


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

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
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

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

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


lemma elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

lemma norm_read (g : Gate) (k : ℕ) (h : k ∈ g.inputs ∧
    (g.op = GateOp.not → g.inputs.head? = some k)) : k ∈ (normGate g).inputs := by
  obtain ⟨op, ins⟩ := g
  cases op <;> try exact h.1
  have hh := h.2 rfl
  cases ins <;> simp_all [normGate]

def readers (k : ℕ) (gs : List Gate) : List Gate :=
  gs.filter (fun g => decide (k ∈ g.inputs))

lemma readers_nonempty (k : ℕ) (gs : List Gate) (i : Fin gs.length)
    (h : k ∈ (gs.get i).inputs) : 1 ≤ (readers k gs).length := by
  have hm : gs.get i ∈ readers k gs := by
    exact List.mem_filter.mpr ⟨List.get_mem gs i, by simpa using h⟩
  cases hrs : readers k gs with
  | nil => simp [hrs] at hm
  | cons _ _ => simp

lemma two_readers (k : ℕ) (gs : List Gate) (a b : Fin gs.length) (hab : a ≠ b)
    (ha : k ∈ (gs.get a).inputs) (hb : k ∈ (gs.get b).inputs) :
    2 ≤ (readers k gs).length := by
  induction gs with
  | nil => exact Fin.elim0 a
  | cons g gs ih =>
    cases a using Fin.cases <;> cases b using Fin.cases
    · exact (hab rfl).elim
    · have h := readers_nonempty k gs _ hb
      have hg : k ∈ g.inputs := ha
      simp only [readers, List.filter_cons, hg, decide_true, ite_true, List.length_cons] at *
      omega
    · have h := readers_nonempty k gs _ ha
      have hg : k ∈ g.inputs := hb
      simp only [readers, List.filter_cons, hg, decide_true, ite_true, List.length_cons] at *
      omega
    · have h := ih _ _ (fun e => hab (congrArg Fin.succ e)) ha hb
      by_cases hg : k ∈ g.inputs
      all_goals simp [readers, hg] at h ⊢ <;> omega

lemma elim_reads (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ gs, NOk g) (hk : k < acc.1.length)
    (hc : acc.1.getD k (Sum.inl false) = Sum.inl false) :
    (elim n gs acc).2.length + (readers k gs).length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim, readers]
  | cons g gs ih =>
    have hg := hok g List.mem_cons_self
    have hlt : k < (elimStep n acc g).1.length := by simp [elimStep]; omega
    have hc' : (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl false := by
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega), hc]
    have ht := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hlt hc'
    change (elim n gs (elimStep n acc g)).2.length + (readers k (g :: gs)).length ≤ _
    by_cases hread : k ∈ g.inputs
    · rw [elimStep_none n acc g hg k hread false hc] at ht
      simp [readers, hread] at ht ⊢
      omega
    · have ho := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      have hstep : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        omega
      simp [readers, hread] at ht ⊢
      omega

def initial {n m : ℕ} (p : Fin n) (r : Fin n → Fin m) : List Stat :=
  List.ofFn fun i : Fin n => if i = p then Sum.inl false else Sum.inr (r i).val

lemma initial_inv {n m : ℕ} (p : Fin n) (r : Fin n → Fin m) (x : Fin m → Bool) :
    Inv m (List.ofFn x) (List.ofFn (fun i : Fin n => if i = p then false else x (r i)))
      (initial p r, []) := by
  refine ⟨by simp [initial], ?_⟩
  intro j
  simp only [List.length_nil, Nat.add_zero, show wiresFrom [] (List.ofFn x) = List.ofFn x from rfl]
  by_cases hj : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa [initial] using hj),
      List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [initial, List.getElem_ofFn]
    split
    · exact ⟨trivial, rfl⟩
    · refine ⟨(r ⟨j, hj⟩).isLt, ?_⟩
      simp [Stat.val, (r ⟨j, hj⟩).isLt]
  · rw [List.getD_eq_default _ _ (by simpa [initial] using Nat.le_of_not_gt hj),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)]
    exact ⟨trivial, rfl⟩

lemma restrict_two (n m s : ℕ) (C : Circuit) (p : Fin n) (r : Fin n → Fin m)
    (hok : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ s + 2)
    (hz : C.eval (List.ofFn fun i : Fin n => if i = p then false else (fun _ : Fin m => false) (r i)) = false)
    (hreads : ∃ a b : Fin C.gates.length, a ≠ b ∧
      (p.val ∈ (C.gates.get a).inputs ∧ ((C.gates.get a).op = GateOp.not → (C.gates.get a).inputs.head? = some p.val)) ∧
      (p.val ∈ (C.gates.get b).inputs ∧ ((C.gates.get b).op = GateOp.not → (C.gates.get b).inputs.head? = some p.val))) :
    PEqualNP.MetaComplexity.HasCircuitSize m
      (fun x : Fin m → Bool => C.eval (List.ofFn fun i : Fin n => if i = p then false else x (r i))) s := by
  let gs := C.gates.map normGate
  have hglen : gs.length = C.gates.length := List.length_map normGate
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g' (hok g' hg')
  let start : List Stat × List Gate := (initial p r, [])
  have hp : p.val < start.1.length := by simpa [start, initial] using p.isLt
  have hconst : start.1.getD p.val (Sum.inl false) = Sum.inl false := by
    rw [List.getD_eq_getElem _ _ hp]
    simp [start, initial]
  obtain ⟨a, b, hab, ha, hb⟩ := hreads
  have hn := two_readers p.val gs (Fin.cast hglen.symm a) (Fin.cast hglen.symm b)
    (fun h => hab (Fin.ext (congrArg (fun i : Fin gs.length => i.val) h)))
    (by simpa [gs] using norm_read _ _ ha) (by simpa [gs] using norm_read _ _ hb)
  let acc := elim m gs start
  have hlen : acc.2.length ≤ s := by
    have hr := elim_reads m p.val gs start hnok hp hconst
    have hsz : C.gates.length ≤ s + 2 := hs
    change acc.2.length + (readers p.val gs).length ≤ start.2.length + gs.length at hr
    simp only [start, List.length_nil, zero_add, hglen] at hr
    omega
  have hval (x : Fin m → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        C.eval (List.ofFn fun i : Fin n => if i = p then false else x (r i)) := by
    have h := inv_elim m (List.ofFn x) (by simp) gs _ _ (fun g hg => (hnok g hg).1)
      (initial_inv p r x)
    calc
      _ = (wiresFrom gs (List.ofFn fun i : Fin n => if i = p then false else x (r i))).getD C.output false :=
        (h.2 C.output).2
      _ = _ := by simp only [gs, wiresFrom_norm, Circuit.eval, wires_eq]
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    have hb : b = false := by
      have h := hval (fun _ => false)
      rw [ho] at h
      exact h.trans hz
    subst b
    refine ⟨⟨[], m⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by simp [Circuit.size], ?_⟩
    intro x
    have hx := hval x
    rw [ho] at hx
    exact (by simp [Circuit.eval, Circuit.wires] : (⟨[], m⟩ : Circuit).eval (List.ofFn x) = false).trans hx
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elim_ok m gs start (by simp [start]), hlen, ?_⟩
    intro x
    have hx := hval x
    rw [ho] at hx
    exact hx

end PEqualNP.Outside.L_meta_2553

theorem PEqualNP.Outside.L_meta_2553 :
    ∀ (x1 x2 x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x1) (x6 : Fin x1 → Fin x2),
    have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => x7 ∈ x8.inputs ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.not → x8.inputs.head? = Option.some x7);
    have x8 : (Fin x2 → Bool) → Bool := fun (x8 : Fin x2 → Bool) => x4.eval (List.ofFn fun (x9 : Fin x1) => if x9 = x5 then Bool.false else x8 (x6 x9));
    PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ x3 + (2 : ℕ) → (x8 fun (x11 : Fin x2) => Bool.false) = Bool.false → (∃ (x12 : Fin x4.gates.length) (x13 : Fin x4.gates.length), x12 ≠ x13 ∧ x7 (↑x5) (x4.gates.get x12) ∧ x7 (↑x5) (x4.gates.get x13)) → PEqualNP.MetaComplexity.HasCircuitSize x2 x8 x3 := by
  exact PEqualNP.Outside.L_meta_2553.restrict_two
