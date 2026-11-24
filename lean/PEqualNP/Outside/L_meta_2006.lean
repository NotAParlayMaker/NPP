import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2006_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Gate-elimination helpers adapted from the project Shannon, Support and Elim files.
-- Source: brilliant-hq/pequalnp-proofs, Apache-2.0, commit 8216299.

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

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

def AO (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem simplify_ao (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ (simplify op m ins).1, AO g := by
  intro g hg
  rcases hop with rfl | rfl
  all_goals
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpAnd, simpOr] at hg <;> (subst hg; simp [AO])

theorem elim_ao (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, AO g) :
    ∀ acc : List Stat × List Gate, (∀ g ∈ acc.2, AO g) → ∀ g ∈ (elim n gs acc).2, AO g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ao _ _ _ (hg g List.mem_cons_self).1 g' (by simpa using h1)


def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def squash (g : Gate) : Gate :=
  match g.inputs with
  | [a,b] => if a = b then {g with inputs := [a]} else g
  | _ => g

lemma squash_eval (g : Gate) (hg : AO g) (F : ℕ → Bool) :
    (squash g).op.eval ((squash g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [squash, GateOp.eval]
  all_goals split_ifs <;> simp_all

lemma squash_ao (g : Gate) (hg : AO g) : AO (squash g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop,hl⟩ := hg
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;>
    simp_all [squash, AO]
  split_ifs <;> simp_all [AO]

lemma squash_short (g : Gate) (hg : AO g)
    (hb : g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    (squash g).inputs.length < 2 := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨_,hl⟩ := hg
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;>
    simp_all [squash]

lemma wires_squash (gs : List Gate) (hg : ∀ g ∈ gs, AO g) (w : List Bool) :
    wiresFrom (gs.map squash) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change wiresFrom (gs.map squash)
      (w ++ [(squash g).op.eval ((squash g).inputs.map fun i => w.getD i false)]) =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    rw [squash_eval g (hg g List.mem_cons_self)]
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk)) _

lemma simplify_short (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (m : ℕ) (ins : List Stat) (h : ins.length < 2) : (simplify op m ins).1 = none := by
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t,l⟩⟩ <;> (try cases s) <;>
    simp_all [simplify, simpAnd, simpOr]

lemma elim_short (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, AO g)
    (hb : ∃ g ∈ gs, g.inputs.length < 2) :
    ∀ acc : List Stat × List Gate, (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => obtain ⟨g,hg,_⟩ := hb; simp at hg
  | cons g gs ih =>
    intro acc
    have htail := elim_len n gs (elimStep n acc g)
    change (elim n gs (elimStep n acc g)).2.length + 1 ≤ _
    by_cases hs : g.inputs.length < 2
    · have hn : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none :=
        simplify_short g.op (hg g List.mem_cons_self).1 _ _ (by simpa using hs)
      have he : (elimStep n acc g).2.length = acc.2.length := by simp only [elimStep,hn,Option.toList_none,List.append_nil]
      simp only [List.length_cons]
      omega
    · have hb' : ∃ k ∈ gs, k.inputs.length < 2 := by
        obtain ⟨k,hk,hkl⟩ := hb
        rcases List.mem_cons.mp hk with rfl | hk
        · exact (hs hkl).elim
        · exact ⟨k,hk,hkl⟩
      have h := ih (fun k hk => hg k (List.mem_cons_of_mem _ hk)) hb' (elimStep n acc g)
      have hlen : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [List.length_cons]
      omega

lemma inv_id_list (n : ℕ) (y : List Bool) (hy : y.length = n) :
    Inv n y y (idStats n,[]) := by
  refine ⟨by simp [idStats,hy], ?_⟩
  intro i
  by_cases hi : i < n
  · have hs : (idStats n).getD i (Sum.inl false) = Sum.inr i := by simp [idStats,hi]
    change ((idStats n).getD i (Sum.inl false)).Valid (n + [].length) ∧ _
    rw [hs]
    exact ⟨hi,rfl⟩
  · rw [List.getD_eq_default _ _ (by simp [idStats];omega),
        List.getD_eq_default y _ (by omega)]
    exact ⟨trivial,rfl⟩

lemma reduce (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hnc : ∃ x y : List Bool, x.length = n ∧ y.length = n ∧ C.eval x ≠ C.eval y)
    (hb : ∃ g ∈ C.gates, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ D : Circuit, Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧
      (∀ x : List Bool, x.length = n → D.eval x = C.eval x) ∧ D.size < C.size := by
  classical
  let gs := C.gates.map squash
  have hAO : ∀ g ∈ gs, AO g := by
    intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    exact squash_ao k (hM k hk)
  have hOk : ∀ g ∈ gs, Ok g := by
    intro g hg
    exact ⟨(hAO g hg).1.imp_right Or.inl,(hAO g hg).2⟩
  have hshort : ∃ g ∈ gs, g.inputs.length < 2 := by
    obtain ⟨g,hg,hb⟩ := hb
    exact ⟨squash g,List.mem_map.mpr ⟨g,hg,rfl⟩,squash_short g (hM g hg) hb⟩
  let acc := elim n gs (idStats n,[])
  have hinv : ∀ y : List Bool, y.length = n → Inv n y (wiresFrom gs y) acc :=
    fun y hy => inv_elim n y hy gs y _ hOk (inv_id_list n y hy)
  have hv : ∀ y : List Bool, y.length = n →
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 y) = C.eval y := by
    intro y hy
    have h := (hinv y hy).2 C.output
    rw [wires_squash C.gates hM y] at h
    exact h.2
  have hcl : CleanL n acc.2 :=
    clean_elim n (List.replicate n false) (by simp) gs _ _ hOk
      (inv_id_list n _ (by simp)) (by intro p g h; simp at h)
  have hmono : ∀ g ∈ acc.2, AO g := elim_ao n gs hAO _ (by simp)
  have hsz : acc.2.length < C.gates.length := by
    have h := elim_short n gs hAO hshort (idStats n,[])
    simpa [acc,gs] using h
  cases he : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x,y,hx,hy,hne⟩ := hnc
    have h1 := hv x hx
    have h2 := hv y hy
    rw [he] at h1 h2
    exact (hne (h1.symm.trans h2)).elim
  | inr out =>
    refine ⟨⟨acc.2,out⟩,hmono,?_,?_,hsz⟩
    · intro j hj i hi
      have helem : acc.2[j]? = some acc.2[j] := List.getElem?_eq_getElem hj
      have hg := hcl j _ helem
      apply hg.lt i
      simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,
        List.getElem?_eq_getElem hj] using hi
    · intro y hy
      have h := hv y hy
      rw [he] at h
      exact h

lemma normalize (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hnc : ∃ x y : List Bool, x.length = n ∧ y.length = n ∧ C.eval x ≠ C.eval y) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x : List Bool, x.length = n → D.eval x = C.eval x) ∧
      D.size ≤ C.size ∧ CleanL n D.gates ∧ D.output < n + D.size := by
  classical
  have hOk : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    exact ⟨(hM g hg).1.imp_right Or.inl, (hM g hg).2⟩
  let acc := elim n C.gates (idStats n,[])
  have hinv : ∀ y : List Bool, y.length = n → Inv n y (wiresFrom C.gates y) acc :=
    fun y hy => inv_elim n y hy C.gates y _ hOk (inv_id_list n y hy)
  have hv : ∀ y : List Bool, y.length = n →
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 y) = C.eval y :=
    fun y hy => ((hinv y hy).2 C.output).2
  have hcl : CleanL n acc.2 :=
    clean_elim n (List.replicate n false) (by simp) C.gates _ _ hOk
      (inv_id_list n _ (by simp)) (by intro p g h; simp at h)
  have hmono : ∀ g ∈ acc.2, AO g := elim_ao n C.gates hM _ (by simp)
  have hsz : acc.2.length ≤ C.gates.length := by
    simpa [acc] using elim_len n C.gates (idStats n,[])
  have hout := ((hinv (List.replicate n false) (by simp)).2 C.output).1
  cases he : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x,y,hx,hy,hne⟩ := hnc
    have h1 := hv x hx
    have h2 := hv y hy
    rw [he] at h1 h2
    exact (hne (h1.symm.trans h2)).elim
  | inr out =>
    refine ⟨⟨acc.2,out⟩,hmono,?_,hsz,hcl,?_⟩
    · intro y hy
      have h := hv y hy
      rw [he] at h
      exact h
    · rw [he] at hout
      exact hout

def sortGate (g : Gate) : Gate :=
  match g.inputs with
  | [a,b] => ⟨g.op, [min a b, max a b]⟩
  | _ => g

lemma sortGate_eval (g : Gate) (hg : AO g) (F : ℕ → Bool) :
    (sortGate g).op.eval ((sortGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op,ins⟩ := g
  rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,tail⟩⟩⟩ <;> try rfl
  rcases hg.1 with rfl | rfl <;> by_cases h : a ≤ b <;>
    simp [sortGate, min_def, max_def, h, GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma wires_sort (gs : List Gate) (hg : ∀ g ∈ gs, AO g) (w : List Bool) :
    wiresFrom (gs.map sortGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have s1 : wiresFrom ((g :: gs).map sortGate) w = wiresFrom (gs.map sortGate)
      (w ++ [(sortGate g).op.eval ((sortGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w = wiresFrom gs
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, sortGate_eval g (hg g (by simp)), ih (fun k hk => hg k (by simp [hk]))]

end PEqualNP.Outside.L_meta_2006_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2006_aux

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_2006 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ x5.output < x1 + x5.size ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 < x10 ∧ x10 < x1 + x6 := by
  classical
  intro n C hC hnc
  let P : ℕ → Prop := fun k => ∃ B : Circuit,
    Monotone2 B ∧ circuitFun n B = circuitFun n C ∧ B.size = k
  have hp : ∃ k, P k := ⟨C.size, C, hC, rfl, rfl⟩
  obtain ⟨B,hB,hBC,hBk⟩ := Nat.find_spec hp
  have hBnc : ∃ x y : List Bool, x.length = n ∧ y.length = n ∧ B.eval x ≠ B.eval y := by
    obtain ⟨x,y,hxy⟩ := hnc
    refine ⟨List.ofFn x,List.ofFn y,by simp,by simp,?_⟩
    simpa only [circuitFun] using (show circuitFun n B x ≠ circuitFun n B y by simpa [hBC] using hxy)
  obtain ⟨D,hD,hDB,hsize,hclean,hout⟩ := normalize n B hB hBnc
  have hDF : circuitFun n D = circuitFun n C := by
    funext x
    exact (hDB (List.ofFn x) (by simp)).trans (congrFun hBC x)
  have hDnc : ∃ x y : List Bool, x.length = n ∧ y.length = n ∧ D.eval x ≠ D.eval y := by
    obtain ⟨x,y,hx,hy,hne⟩ := hBnc
    exact ⟨x,y,hx,hy,by simpa [hDB x hx,hDB y hy] using hne⟩
  have hmin : ∀ E : Circuit, Monotone2 E → circuitFun n E = circuitFun n C → B.size ≤ E.size := by
    intro E hE hEF
    rw [hBk]
    exact Nat.find_min' hp ⟨E,hE,hEF,rfl⟩
  have hgood : ∀ g ∈ D.gates, ¬(g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) := by
    intro g hg hb
    obtain ⟨E,hE,_,hED,hlt⟩ := reduce n D hD hDnc ⟨g,hg,hb⟩
    have hEF : circuitFun n E = circuitFun n C := by
      funext x
      exact (hED (List.ofFn x) (by simp)).trans (congrFun hDF x)
    have := hmin E hE hEF
    omega
  have hpair : ∀ g ∈ D.gates, ∃ a b, g.inputs = [a,b] ∧ a ≠ b := by
    intro g hg
    have hlen := (hD g hg).2
    have hgood' := hgood g hg
    rcases he : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,tail⟩⟩⟩
    · simp [he] at hgood'
    · simp [he] at hgood'
    · refine ⟨a,b,rfl,?_⟩
      simpa [he] using hgood'
    · simp [he] at hlen
  let E : Circuit := ⟨D.gates.map sortGate,D.output⟩
  refine ⟨E,?_,?_,?_,?_,?_⟩
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    obtain ⟨a,b,hab,hne⟩ := hpair k hk
    simpa [sortGate,hab,AO] using hD k hk
  · have hBCsize := hmin C hC rfl
    simpa [E,Circuit.size] using (le_trans hsize hBCsize)
  · funext x
    change (wiresFrom (D.gates.map sortGate) (List.ofFn x)).getD D.output false = _
    rw [wires_sort D.gates hD]
    exact congrFun hDF x
  · simpa [E,Circuit.size] using hout
  · intro j g hj
    have hmap : (D.gates.map sortGate)[j]? = some g := hj
    have hjlt' : j < D.gates.length := by
      have : j < (D.gates.map sortGate).length := (List.getElem?_eq_some_iff.mp hmap).choose
      simpa using this
    let k := D.gates[j]
    have hk : k ∈ D.gates := List.getElem_mem hjlt'
    obtain ⟨a,b,hab,hne⟩ := hpair k hk
    have hkg : sortGate k = g := by
      simpa [k,List.getElem?_eq_getElem hjlt'] using hmap
    have hcl := hclean j k (List.getElem?_eq_getElem hjlt')
    have ha : a < n + j := hcl.lt a (by simp [hab])
    have hb : b < n + j := hcl.lt b (by simp [hab])
    refine ⟨min a b,max a b,?_,?_,max_lt ha hb⟩
    · rw [← hkg]
      simp [sortGate,hab]
    · omega
