import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3223_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

-- Adapted from the gate elimination helpers in L_meta_1543.lean.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

abbrev Stat : Type := Bool ⊕ ℕ

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

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
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
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

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

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
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

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

def mappedStats {n : ℕ} (pins : List (Option (Fin n))) : List Stat :=
  pins.map (fun v => v.elim (Sum.inl false) (fun i => Sum.inr i.val))

theorem mapped_init {n : ℕ} (pins : List (Option (Fin n))) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (pins.map (fun v => v.elim false x)) (mappedStats pins, []) := by
  refine ⟨by simp [mappedStats], ?_⟩
  intro i
  simp only [List.getD_eq_getElem?_getD, mappedStats, List.getElem?_map]
  cases hp : pins[i]? with
  | none => exact ⟨trivial, rfl⟩
  | some v =>
    cases v with
    | none => exact ⟨trivial, rfl⟩
    | some j =>
      change j.val < n + 0 ∧ (List.ofFn x).getD j.val false = x j
      exact ⟨j.isLt, by rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]⟩

def AgreeExcept (D : ℕ → Prop) (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, ¬ D i → a.getD i false = b.getD i false

theorem same_gate {D : ℕ → Prop} {a b : List Bool} (ha : AgreeExcept D a b)
    (g : Gate) (hg : ∀ i ∈ g.inputs, ¬ D i) :
    g.op.eval (g.inputs.map fun i => a.getD i false) =
      g.op.eval (g.inputs.map fun i => b.getD i false) := by
  congr 1
  exact List.map_congr_left (fun i hi => ha.2 i (hg i hi))

theorem agree_snoc {D : ℕ → Prop} {a b : List Bool} (ha : AgreeExcept D a b)
    (x y : Bool) (he : ¬ D a.length → x = y) :
    AgreeExcept D (a ++ [x]) (b ++ [y]) := by
  refine ⟨by simp [ha.1], ?_⟩
  intro i hi
  by_cases h : i = a.length
  · subst i
    rw [getD_snoc_eq, getD_snoc_len _ _ _ _ ha.1.symm]
    exact he hi
  · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by simpa only [← ha.1] using h)]
    exact ha.2 i hi

theorem agree_fold (D : ℕ → Prop) (gs : List Gate) (a b : List Bool)
    (hab : AgreeExcept D a b) (hgs : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬ D i) :
    AgreeExcept D (wiresFrom gs a) (wiresFrom gs b) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    apply ih _ _ (agree_snoc hab _ _ (fun _ => same_gate hab g (hgs g List.mem_cons_self)))
    exact fun g hg => hgs g (List.mem_cons_of_mem _ hg)

theorem saved (n : ℕ) (ss : List Stat) (gs : List Gate) (k o e : ℕ)
    (hk : k < ss.length) (hc : ss.getD k (Sum.inl false) = Sum.inl false)
    (hnok : ∀ g ∈ gs, NOk g) (he : e ≤ 1)
    (hor : e = 1 → ∀ g ∈ gs, g.op = .or → k ∉ g.inputs)
    (hout : ∀ c, (elim n gs (ss, [])).1.getD o (Sum.inl false) ≠ Sum.inl c)
    (hdep : ∃ a b : List Bool, a.length = ss.length ∧ AgreeExcept (· = k) a b ∧
      (wiresFrom gs a).getD o false ≠ (wiresFrom gs b).getD o false) :
    (elim n gs (ss, [])).2.length + (e + 1) ≤ gs.length := by
  have hon : o ≠ k := by
    intro h
    apply hout false
    rw [h, elim_getD n k _ gs _ hk, hc]
  obtain ⟨a, b, ha, hab, hneq⟩ := hdep
  have hread : ∃ g ∈ gs, k ∈ g.inputs := by
    by_contra h
    push Not at h
    exact hneq ((agree_fold (· = k) gs a b hab (by
      intro g hg i hi eq
      exact h g hg (eq ▸ hi))).2 o hon)
  by_cases hz : e = 0
  · subst e
    simpa using elim_len_lt n k gs (ss, []) hnok hk ⟨false, hc⟩ hread
  have he1 : e = 1 := by omega
  subst e
  obtain ⟨g, hg, hkg⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  let acc := elim n pre (ss, [])
  let next := elimStep n acc g
  let w := ss.length + pre.length
  have hgn := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : elim n (pre ++ g :: post) (ss, []) = elim n post next := by
    rw [elim_append, elim_cons]
  have hAcc : acc.1.getD k (Sum.inl false) = Sum.inl false := by
    change (elim n pre (ss, [])).1.getD k (Sum.inl false) = Sum.inl false
    rw [elim_getD n k _ pre _ hk, hc]
  have hAl : acc.1.length = w := elim_fst_len n pre (ss, [])
  have hNl : next.1.length = w + 1 := by simp [next, elimStep, hAl]
  have hA2 : acc.2.length ≤ pre.length := by simpa [acc] using elim_len n pre (ss, [])
  have hB2 : next.2.length = acc.2.length := elimStep_none n acc g hgn k hkg false hAcc
  have hFinal := elim_len n post next
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by simp; omega
  by_cases h1 : ∃ g' ∈ pre, k ∈ g'.inputs
  · have h := elim_len_lt n k pre (ss, []) hpren hk ⟨false, hc⟩ h1
    change acc.2.length + 1 ≤ 0 + pre.length at h
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, k ∈ g'.inputs
  · have hNk : next.1.getD k (Sum.inl false) = Sum.inl false := by
      change (acc.1 ++ [_]).getD k _ = _
      rw [getD_snoc_ne _ _ _ _ (by rw [hAl]; dsimp [w]; omega), hAcc]
    have h := elim_len_lt n k post next hpostn (by rw [hNl]; dsimp [w]; omega)
      ⟨false, hNk⟩ h2
    rw [hsplit, hlen]
    omega
  have hnotOr : g.op ≠ .or := fun e => hor rfl g hg e hkg
  have hfix : fixBit g = false := by
    rcases hgn.1.1 with h | h | h
    · simp [fixBit, h]
    · exact False.elim (hnotOr h)
    · simp [fixBit, h]
  obtain ⟨c, hConst⟩ := elimStep_const n acc g hgn k hkg (by rw [hfix, hAcc])
  rw [hAl] at hConst
  by_cases h3 : ∃ g' ∈ post, w ∈ g'.inputs
  · have h := elim_len_lt n w post next hpostn (by rw [hNl]; omega)
      ⟨c, hConst⟩ h3
    rw [hsplit, hlen]
    omega
  have how : o ≠ w := by
    intro h
    apply hout c
    rw [h, hsplit, elim_getD _ _ _ _ _ (by rw [hNl]; omega)]
    exact hConst
  have hpre := agree_fold (· = k) pre a b hab (by
    intro g hg i hi eq
    exact h1 ⟨g, hg, eq ▸ hi⟩)
  have hwidth : (wiresFrom pre a).length = w := by simp [length_wiresFrom, ha, w]
  have hbefore : AgreeExcept (fun i => i = k ∨ i = w) (wiresFrom pre a) (wiresFrom pre b) :=
    ⟨hpre.1, fun i hi => hpre.2 i (fun h => hi (Or.inl h))⟩
  have hnext := agree_snoc hbefore
    (g.op.eval (g.inputs.map fun i => (wiresFrom pre a).getD i false))
    (g.op.eval (g.inputs.map fun i => (wiresFrom pre b).getD i false))
    (fun h => False.elim (h (Or.inr hwidth)))
  have hfin := agree_fold (fun i => i = k ∨ i = w) post _ _ hnext (by
    intro gate h i hi eq
    rcases eq with rfl | rfl
    · exact h2 ⟨gate, h, hi⟩
    · exact h3 ⟨gate, h, hi⟩)
  exfalso
  apply hneq
  rw [wiresFrom_append, wiresFrom_append]
  exact hfin.2 o (fun h => h.elim hon how)

theorem main {n : ℕ} (C : Circuit) (pins : List (Option (Fin n))) (k e : ℕ)
    (hfan : FanInTwo C) (hk : pins[k]? = some none) (he : e ≤ 1)
    (hor : e = 1 → ∀ g ∈ C.gates, g.op = .or → k ∉ g.inputs)
    (hdep : ∃ a b : List Bool, a.length = pins.length ∧ b.length = pins.length ∧
      (∀ i, i ≠ k → a.getD i false = b.getD i false) ∧ C.eval a ≠ C.eval b)
    (hnc : ∃ a b : Fin n → Bool,
      C.eval (pins.map (fun v => v.elim false a)) ≠ C.eval (pins.map (fun v => v.elim false b))) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + (e + 1) ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (pins.map (fun v => v.elim false x)) := by
  let gs := C.gates.map normGate
  let ss := mappedStats pins
  let acc := elim n gs (ss, [])
  have hnorm : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g', hmem, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g' (hfan g' hmem)
  have hgsEval (x : List Bool) : (wiresFrom gs x).getD C.output false = C.eval x := by
    change (wiresFrom (C.gates.map normGate) x).getD C.output false = C.eval x
    rw [wiresFrom_norm]
    rfl
  have hInv (x : Fin n → Bool) := inv_elim n (List.ofFn x) (by simp) gs _ _
    (fun g hg => (hnorm g hg).1) (mapped_init pins x)
  have hVal (x : Fin n → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        C.eval (pins.map (fun v => v.elim false x)) :=
    ((hInv x).2 C.output).2.trans (hgsEval _)
  have hOut (c : Bool) : acc.1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro h
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    rw [← hVal a, ← hVal b, h]
    rfl
  have hks : k < ss.length := by
    have hp : k < pins.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hk
      contradiction
    simpa [ss, mappedStats] using hp
  have hzero : ss.getD k (Sum.inl false) = Sum.inl false := by
    simp [ss, mappedStats, List.getD_eq_getElem?_getD, hk]
  have hS := saved n ss gs k C.output e hks hzero hnorm he (by
    intro h g hg hop
    obtain ⟨g', hmem, rfl⟩ := List.mem_map.mp hg
    rcases g' with ⟨op, inputs⟩
    cases op <;> simp [normGate] at hop ⊢
    exact hor h ⟨.or, inputs⟩ hmem rfl) hOut (by
      obtain ⟨a, b, ha, hb, hdiff, hne⟩ := hdep
      refine ⟨a, b, by simpa [ss, mappedStats] using ha, ⟨ha.trans hb.symm, hdiff⟩, ?_⟩
      simpa only [hgsEval] using hne)
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl c => exact False.elim (hOut c ho)
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), ?_, ?_⟩
    · simpa [Circuit.size, gs, acc] using hS
    · intro x
      have h := hVal x
      rw [ho] at h
      exact h

end PEqualNP.Outside.L_meta_3223_aux

theorem PEqualNP.Outside.L_meta_3223 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Option (Fin x1))) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x3[x4]? = Option.some Option.none → x5 ≤ (1 : ℕ) → (x5 = (1 : ℕ) → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ∉ x10.inputs) → (∃ (x10 : List Bool) (x11 : List Bool), x10.length = x3.length ∧ x11.length = x3.length ∧ (∀ (x12 : ℕ), x12 ≠ x4 → x10.getD x12 Bool.false = x11.getD x12 Bool.false) ∧ x2.eval x10 ≠ x2.eval x11) → (∃ (x11 : Fin x1 → Bool) (x12 : Fin x1 → Bool), x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x11) x3) ≠ x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x12) x3)) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size + (x5 + (1 : ℕ)) ≤ x2.size ∧ ∀ (x13 : Fin x1 → Bool), x12.eval (List.ofFn x13) = x2.eval (List.map (fun (x14 : Option (Fin x1)) => x14.elim Bool.false x13) x3) := by
  intro n
  exact PEqualNP.Outside.L_meta_3223_aux.main (n := n)
