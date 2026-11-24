import Mathlib
import PEqualNP.Defs

-- Constant-propagation lemmas adapted from L-meta-1543 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_3223

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega


theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : Sum.inl false ∈ ins) :
    ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · simp at hc; subst hc; exact ⟨false, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · cases b <;> simp [simplify, simpAnd]
      · cases a <;> simp [simplify, simpAnd]
    · simp at hlen
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hc
    · simp at hc; subst hc; exact ⟨true, rfl⟩
    · simp at this

theorem agree (gs : List Gate) (E : ℕ → Prop) : ∀ (w w' : List Bool), w.length = w'.length →
    (∀ i, ¬ E i → w.getD i false = w'.getD i false) →
    (∀ j (hj : j < gs.length), ¬ E (w.length + j) → ∀ a ∈ gs[j].inputs, ¬ E a ∨ w.length + j ≤ a) →
    ∀ i, ¬ E i → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs with
  | nil => intro w w' _ h _ i hi; exact h i hi
  | cons g gs ih =>
    intro w w' hlen h hg
    have hgv : ¬ E w.length → g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      intro hE
      congr 1
      apply List.map_congr_left
      intro a ha
      rcases hg 0 (by simp) (by simpa using hE) a (by simpa using ha) with h1 | h1
      · exact h a h1
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) (by simp [hlen])
    · intro i hi
      rcases Nat.lt_trichotomy i w.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · subst heq
        rw [getD_snoc_eq, show w.length = w'.length from hlen, getD_snoc_eq]
        exact hgv (hlen ▸ hi)
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · intro j hj hE a ha
      have := hg (j + 1) (by simp; omega) (by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hE) a
        (by simpa using ha)
      simp only [List.length_append, List.length_singleton] at this ⊢
      rcases this with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by omega)

theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, xs⟩ := g
  cases op <;> rfl

theorem normGate_sub (g : Gate) (a : ℕ) (h : a ∈ (normGate g).inputs) : a ∈ g.inputs := by
  obtain ⟨op, xs⟩ := g
  cases op
  case not => exact List.mem_of_mem_take h
  all_goals exact h

end PEqualNP.Outside.L_meta_3223

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3223

theorem PEqualNP.Outside.L_meta_3223 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Option (Fin x1))) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x3[x4]? = Option.some Option.none → x5 ≤ (1 : ℕ) → (x5 = (1 : ℕ) → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ∉ x10.inputs) → (∃ (x10 : List Bool) (x11 : List Bool), x10.length = x3.length ∧ x11.length = x3.length ∧ (∀ (x12 : ℕ), x12 ≠ x4 → x10.getD x12 Bool.false = x11.getD x12 Bool.false) ∧ x2.eval x10 ≠ x2.eval x11) → (∃ (x11 : Fin x1 → Bool) (x12 : Fin x1 → Bool), x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x11) x3) ≠ x2.eval (List.map (fun (x13 : Option (Fin x1)) => x13.elim Bool.false x12) x3)) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size + (x5 + (1 : ℕ)) ≤ x2.size ∧ ∀ (x13 : Fin x1 → Bool), x12.eval (List.ofFn x13) = x2.eval (List.map (fun (x14 : Option (Fin x1)) => x14.elim Bool.false x13) x3) := by
  intro n C L p e fan hp he hor hdep hnc
  classical
  let m := L.length
  have hpm : p < m := (List.getElem?_eq_some_iff.1 hp).1
  let inp : (Fin n → Bool) → List Bool := fun y => L.map fun o => o.elim false y
  let gs := C.gates.map normGate
  have glen : gs.length = C.gates.length := by simp [gs]
  have normOk : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok _ (fan _ hg0)
  let init : List Stat := L.map fun o => o.elim (Sum.inl false) fun v => Sum.inr v.val
  have initLen : init.length = m := by simp [init, m]
  let acc := elim n gs (init, [])
  have inv (y : Fin n → Bool) : Inv n (List.ofFn y) (wiresFrom gs (inp y)) acc := by
    apply inv_elim _ _ (by simp) _ _ _ (fun g hg => (normOk g hg).1)
    refine ⟨by simp [init, inp], ?_⟩
    intro i
    simp only [init, inp, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases L[i]? with _ | _ | v <;> simp [Stat.Valid, Stat.val, wiresFrom]
  have value (y : Fin n → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
      C.eval (inp y) := by
    rw [((inv y).2 C.output).2, show gs = C.gates.map normGate from rfl, wiresFrom_norm]
    rfl
  have evalW : ∀ l : List Bool, C.eval l = (wiresFrom gs l).getD C.output false := by
    intro l
    rw [show gs = C.gates.map normGate from rfl, wiresFrom_norm]
    rfl
  have statP : acc.1.getD p (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n p _ gs _ (by simp only [initLen]; exact hpm)]
    simp [init, List.getD_eq_getElem?_getD, hp]
  -- the stat of gate j's wire, and the stats it reads
  have statGate : ∀ j (hj : j < gs.length), acc.1.getD (m + j) (Sum.inl false) =
      (simplify gs[j].op (n + (elim n (gs.take j) (init, [])).2.length)
        (gs[j].inputs.map fun i => (elim n (gs.take j) (init, [])).1.getD i (Sum.inl false))).2 := by
    intro j hj
    have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
    show (elim n gs (init, [])).1.getD (m + j) (Sum.inl false) = _
    conv_lhs => rw [hsplit]
    rw [elim_split_getD n _ _ _ _ _ _ (by simp [initLen, Nat.min_eq_left (le_of_lt hj)])]
    show ((elim n (gs.take j) (init, [])).1 ++ [_]).getD (m + j) (Sum.inl false) = _
    have hl : (elim n (gs.take j) (init, [])).1.length = m + j := by
      rw [elim_fst_len]; simp [initLen, Nat.min_eq_left (le_of_lt hj)]
    rw [← hl, getD_snoc_eq]
  have statPre : ∀ j (hj : j < gs.length) a, a < m + j →
      (elim n (gs.take j) (init, [])).1.getD a (Sum.inl false) = acc.1.getD a (Sum.inl false) := by
    intro j hj a ha
    have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
    show _ = (elim n gs (init, [])).1.getD a (Sum.inl false)
    conv_rhs => rw [hsplit]
    rw [elim_split_getD_lt n _ _ _ _ _ _ (by simp [initLen, Nat.min_eq_left (le_of_lt hj)]; omega)]
  let S : Finset ℕ := (Finset.range gs.length).filter (fun j => ∃ g, gs[j]? = some g ∧
    ∃ a ∈ g.inputs, a < m + j ∧ ∃ c, acc.1.getD a (Sum.inl false) = Sum.inl c)
  have count := elim_count n (init, []) gs normOk S (by
    intro j hj
    obtain ⟨_, g, hg, a, ha, hlt, c, hc⟩ := Finset.mem_filter.1 hj
    exact ⟨g, hg, a, ha, by simpa [initLen] using hlt, c, hc⟩)
  have num : acc.2.length + S.card ≤ C.size := by
    have := count
    simp only [List.length_nil, Nat.zero_add] at this
    rw [glen] at this
    exact this
  have memS : ∀ j (hj : j < gs.length) a, a ∈ gs[j].inputs → a < m + j →
      (∃ c, acc.1.getD a (Sum.inl false) = Sum.inl c) → j ∈ S := by
    intro j hj a ha hlt hc
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, gs[j], List.getElem?_eq_getElem hj, a, ha, hlt, hc⟩
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    have e1 := value y
    have e2 := value y'
    rw [ho] at e1 e2
    simp only [Stat.val] at e1 e2
    exact hne (e1.symm.trans e2)
  | inr k =>
    obtain ⟨l, l', hl, hl', hag, hne⟩ := hdep
    have outNe : ∀ w, (∃ c, acc.1.getD w (Sum.inl false) = Sum.inl c) → C.output ≠ w := by
      rintro w ⟨c, hc⟩ rfl
      rw [ho] at hc
      cases hc
    -- some gate reads p
    have reader : ∃ H, ∃ hH : H < gs.length, p ∈ gs[H].inputs := by
      by_contra hno
      simp only [not_exists] at hno
      apply hne
      rw [evalW, evalW]
      refine agree gs (· = p) l l' (by rw [hl, hl']) (fun i hi => hag i hi) ?_ C.output
        (outNe p ⟨false, statP⟩)
      intro j hj _ a ha
      left
      rintro rfl
      exact hno j hj ha
    obtain ⟨H, hH, hpH⟩ := reader
    have HS : H ∈ S := memS H hH p hpH (by omega) ⟨false, statP⟩
    have card1 : 1 ≤ S.card := Finset.card_pos.2 ⟨H, HS⟩
    have card2 : e + 1 ≤ S.card := by
      rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
      · exact card1
      by_contra hlt
      have hone : ∀ j ∈ S, j = H := by
        intro j hj
        have : S.card ≤ 1 := by omega
        exact Finset.card_le_one.1 this j hj H HS
      -- H is an AND or NOT gate, so its wire is constant
      have hHgate : gs[H] = normGate (C.gates[H]'(by omega)) := by simp [gs]
      have hop : gs[H].op = GateOp.and ∨ gs[H].op = GateOp.not := by
        have hok := (normOk gs[H] (List.getElem_mem hH)).1.1
        rcases hok with h | h | h
        · exact Or.inl h
        · exfalso
          have hmem : C.gates[H]'(by omega) ∈ C.gates := List.getElem_mem _
          have hor' : (C.gates[H]'(by omega)).op = GateOp.or := by
            rw [hHgate, normGate_op] at h
            exact h
          apply hor rfl _ hmem hor'
          rw [hHgate] at hpH
          exact normGate_sub _ _ hpH
        · exact Or.inr h
      have statH : ∃ c, acc.1.getD (m + H) (Sum.inl false) = Sum.inl c := by
        rw [statGate H hH]
        apply simplify_const _ _ _ hop
        · simpa using (normOk _ (List.getElem_mem hH)).1.2
        · intro h; simpa using (normOk _ (List.getElem_mem hH)).2 h
        · refine List.mem_map.2 ⟨p, hpH, ?_⟩
          rw [statPre H hH p (by omega), statP]
      apply hne
      rw [evalW, evalW]
      refine agree gs (fun i => i = p ∨ i = m + H) l l' (by rw [hl, hl'])
        (fun i hi => hag i (fun h => hi (Or.inl h))) ?_ C.output ?_
      · intro j hj hE a ha
        have hjH : j ≠ H := by
          intro h; subst h; apply hE; right; rw [hl]
        by_cases hlt' : l.length + j ≤ a
        · exact Or.inr hlt'
        · left
          rintro (rfl | rfl)
          · exact hjH (hone j (memS j hj _ ha (by omega) ⟨false, statP⟩))
          · rw [hl] at hlt'
            exact hjH (hone j (memS j hj _ ha (by omega) statH))
      · rintro (h | h)
        · exact outNe p ⟨false, statP⟩ h
        · exact outNe (m + H) statH h
    refine ⟨(⟨acc.2, k⟩ : Circuit), elim_ok n gs _ (by simp), ?_, ?_⟩
    · change acc.2.length + (e + 1) ≤ C.size
      omega
    · intro y
      change (wiresFrom acc.2 (List.ofFn y)).getD k false = _
      have hv := value y
      simp only [ho, Stat.val] at hv
      exact hv
