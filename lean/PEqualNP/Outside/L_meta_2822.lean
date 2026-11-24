import Mathlib
import PEqualNP.Defs

-- Constant-propagation lemmas adapted from L-meta-2513 and L-meta-1543 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_2822

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

theorem simplify_nil (op : GateOp) (m : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) :
    (simplify op m []).1 = none := by
  rcases hop with rfl | rfl | rfl <;> rfl

theorem elim_count2 (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ (g.inputs = [] ∨ ∃ a ∈ g.inputs, ∃ c,
        (elim n (gs.take p) acc).1.getD a (Sum.inl false) = Sum.inl c)) →
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
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [List.take_append_of_le_length (le_of_lt hpl)] at hc
      exact ⟨g', hg', hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      have htk : (gs ++ [g']).take gs.length = gs := by simp
      rw [htk] at hc
      have h2 : (elimStep n (elim n gs acc) g').2.length = (elim n gs acc).2.length := by
        rcases hc with h0 | ⟨a, ha, c, hc⟩
        · show ((elim n gs acc).2 ++ (simplify g'.op (n + (elim n gs acc).2.length)
            (g'.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1.toList).length = _
          rw [h0, List.map_nil, simplify_nil _ _ (hok g' (by simp)).1.1]
          simp
        · exact elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
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

theorem elim_succ_take (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hg : gs[p]? = some g) :
    elim n (gs.take (p + 1)) acc = elimStep n (elim n (gs.take p) acc) g := by
  rw [List.take_add_one, hg, elim_append]; rfl

theorem elim_take_getD (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p q a : ℕ)
    (d : Stat) (hp : p < gs.length) (hpq : p < q) (ha : a = acc.1.length + p) :
    (elim n (gs.take q) acc).1.getD a d = (elim n (gs.take (p + 1)) acc).1.getD a d := by
  obtain ⟨k, rfl⟩ : ∃ k, q = p + 1 + k := ⟨q - (p + 1), by omega⟩
  rw [List.take_add, elim_append]
  apply elim_getD
  rw [elim_fst_len, List.length_take]
  omega

def evalG (g : Gate) (W : List Bool) : Bool := g.op.eval (g.inputs.map fun i => W.getD i false)

def Good (B : ℕ → Prop) (n : ℕ) (w w' : List Bool) (g g' : Gate) (m : ℕ) : Prop :=
  ∀ V V' : List Bool, V.length = m → V'.length = m →
    (∀ i < n, V.getD i false = w.getD i false ∧ V'.getD i false = w'.getD i false) →
    (∀ i, ¬ B i → V.getD i false = V'.getD i false) → evalG g V = evalG g' V'

theorem agree (B : ℕ → Prop) (n : ℕ) (w w' : List Bool) : ∀ (gs gs' : List Gate)
    (W W' : List Bool),
    gs.length = gs'.length → W.length = W'.length → n ≤ W.length →
    (∀ i < n, W.getD i false = w.getD i false ∧ W'.getD i false = w'.getD i false) →
    (∀ i, ¬ B i → W.getD i false = W'.getD i false) →
    (∀ j (hj : j < gs.length) (hj' : j < gs'.length),
      B (W.length + j) ∨ Good B n w w' gs[j] gs'[j] (W.length + j)) →
    ∀ i, ¬ B i → (wiresFrom gs W).getD i false = (wiresFrom gs' W').getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro gs' W W' hl _ _ _ hW _ i hi
    cases gs' with
    | nil => exact hW i hi
    | cons _ _ => simp at hl
  | cons g gs ih =>
    intro gs' W W' hl hWl hn hpre hW hgood i hi
    cases gs' with
    | nil => simp at hl
    | cons g' gs' =>
      have hstep : ∀ (h : Gate) (hs : List Gate) (X : List Bool),
          wiresFrom (h :: hs) X = wiresFrom hs (X ++ [evalG h X]) := fun _ _ _ => rfl
      rw [hstep, hstep]
      refine ih gs' _ _ (by simpa using hl) (by simp [hWl]) (by simp; omega) ?_ ?_ ?_ i hi
      · intro k hk
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hpre k hk
      · intro k hk
        by_cases hkW : k = W.length
        · have e1 : (W ++ [evalG g W]).getD k false = evalG g W := by
            rw [hkW]; exact getD_snoc_eq _ _ _
          have e2 : (W' ++ [evalG g' W']).getD k false = evalG g' W' := by
            rw [hkW, hWl]; exact getD_snoc_eq _ _ _
          rw [e1, e2]
          rcases hgood 0 (by simp) (by simp) with hb | hg
          · exact absurd (by simpa [hkW] using hb) hk
          · exact hg W W' (by simp) (by simp [hWl]) hpre hW
        · rw [getD_snoc_ne _ _ _ _ hkW, getD_snoc_ne _ _ _ _ (by omega)]
          exact hW k hk
      · intro j hj hj'
        have e : (W ++ [evalG g W]).length + j = W.length + (j + 1) := by simp; omega
        rw [e]
        exact hgood (j + 1) (by simpa using hj) (by simpa using hj')

theorem good_free (B : ℕ → Prop) (n : ℕ) (w w' : List Bool) (g : Gate) (m : ℕ)
    (h : ∀ i ∈ g.inputs, ¬ B i) : Good B n w w' g g m := by
  intro V V' _ _ _ hV
  unfold evalG
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hV i (h i hi)

theorem wiresFrom_getD_lt (gs : List Gate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
    (wiresFrom gs W).getD i false = W.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs W
  rw [ht]; exact List.getD_append _ _ _ _ hi

def initStat (v : ℕ) (b : Bool) (k : ℕ) : Stat :=
  if k < v then Sum.inr k else if k = v then Sum.inl b else
    if k < 9 then Sum.inr (k - 1) else Sum.inl false

theorem ins_len (y : Fin 8 → Bool) (v : Fin 9) (b : Bool) :
    ((List.ofFn y).insertIdx v b).length = 9 := by
  have hv := v.isLt
  rw [List.length_insertIdx_of_le_length (by simp; omega)]; simp

theorem ins_getD (y : Fin 8 → Bool) (v : Fin 9) (b : Bool) (k : ℕ) :
    ((List.ofFn y).insertIdx v b).getD k false = (initStat v b k).val (List.ofFn y) := by
  rcases Nat.lt_or_ge k 9 with hk | hk
  · fin_cases v <;> interval_cases k <;> simp [initStat, Stat.val, List.ofFn_succ]
  · have hv := v.isLt
    rw [List.getD_eq_default _ _ (by rw [ins_len]; exact hk)]
    simp only [initStat, if_neg (show ¬ (k < (v : ℕ)) by omega),
      if_neg (show ¬ k = (v : ℕ) by omega), if_neg (show ¬ k < 9 by omega), Stat.val]

def initL (v : ℕ) (b : Bool) : List Stat := List.ofFn (fun k : Fin 9 => initStat v b k)

theorem initL_getD (v : ℕ) (b : Bool) (k : ℕ) (hv : v < 9) :
    (initL v b).getD k (Sum.inl false) = initStat v b k := by
  rcases Nat.lt_or_ge k 9 with hk | hk
  · simp [initL, List.getD_eq_getElem?_getD, hk]
    interval_cases k <;> rfl
  · rw [List.getD_eq_default _ _ (by simp [initL]; omega)]
    simp only [initStat, if_neg (show ¬ (k < v) by omega),
      if_neg (show ¬ k = v by omega), if_neg (show ¬ k < 9 by omega)]

theorem inv_initR (y : Fin 8 → Bool) (v : Fin 9) :
    Inv 8 (List.ofFn y) ((List.ofFn y).insertIdx v false) (initL v false, []) := by
  have hv := v.isLt
  refine ⟨by rw [ins_len]; simp [initL], fun k => ⟨?_, ?_⟩⟩
  · rw [initL_getD _ _ _ hv]
    simp only [initStat]
    split_ifs <;> simp [Stat.Valid] <;> omega
  · rw [initL_getD _ _ _ hv, ins_getD]; rfl

def idL : List Stat := List.ofFn (fun k : Fin 9 => (Sum.inr k.val : Stat))

theorem inv_id (W : List Bool) (hW : W.length = 9) : Inv 9 W W (idL, []) := by
  refine ⟨by simp [idL, hW], fun k => ?_⟩
  rcases Nat.lt_or_ge k 9 with hk | hk
  · have e : idL.getD k (Sum.inl false) = Sum.inr k := by
      simp [idL, List.getD_eq_getElem?_getD, hk]
      interval_cases k <;> rfl
    rw [e]; exact ⟨by simp [Stat.Valid, hk], rfl⟩
  · rw [List.getD_eq_default _ _ (by simp [idL]; omega),
      List.getD_eq_default _ _ (by omega)]
    exact ⟨trivial, rfl⟩

theorem simplify_const (op : GateOp) (m : ℕ) (l : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : l.length ≤ 2)
    (hnot : op = GateOp.not → l.length ≤ 1) (hf : Sum.inl false ∈ l)
    (hor : op = GateOp.or → ∀ s ∈ l, ∃ c, s = Sum.inl c) :
    ∃ c, (simplify op m l).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem pair_of (l : List ℕ) (v i : ℕ) (hl : l.length ≤ 2) (hv : v ∈ l) (hi : i ∈ l)
    (hne : i ≠ v) : l = [v, i] ∨ l = [i, v] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hv
  · simp at hv hi; omega
  · simp at hv hi ⊢; omega
  · simp at hl

theorem normGate_of_or (g : Gate) (h : (normGate g).op = GateOp.or) : normGate g = g := by
  obtain ⟨op, xs⟩ := g
  cases op <;> simp_all [normGate]

theorem reader_iff (v : ℕ) (g : Gate) (hok : Ok g) :
    (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains v = true ↔
      v ∈ (normGate g).inputs := by
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, _⟩ := hok
  change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
  rcases hop with rfl | rfl | rfl <;> simp [normGate, GateOp.eval]

end PEqualNP.Outside.L_meta_2822

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2822

theorem PEqualNP.Outside.L_meta_2822 : have x1 : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) => (if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs).contains ↑x1; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x2 →     have x5 : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (x5 : Bool) (x6 : Fin (8 : ℕ) → Bool) => x2.eval ((List.ofFn x6).insertIdx (↑x3) x5);     (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x5 Bool.false x6 ≠ x5 Bool.false x7) → (∀ (x7 : Fin (9 : ℕ)), x7 ≠ x3 → ∃ (x9 : Fin (8 : ℕ) → Bool), x5 Bool.false x9 ≠ x5 Bool.true x9 ∧ ((List.ofFn x9).insertIdx (↑x3) Bool.false).getD (↑x7) Bool.false = Bool.true) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (2 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x8 = x5 Bool.false) ∨ ∃ (x8 : Fin x2.size) (x9 : ℕ), (9 : ℕ) ≤ x9 ∧ x9 < (9 : ℕ) + ↑x8 ∧ (x2.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x2.gates.get x8).inputs = [↑x3, x9] ∨ (x2.gates.get x8).inputs = [x9, ↑x3]) ∧ ∀ (x10 : Fin x2.size), x1 x3 (x2.gates.get x10) = Bool.true → x10 = x8 := by
  intro reader C v hmin f0 hnc hdep
  classical
  obtain ⟨fan, minimal⟩ := hmin
  have hv9 := v.isLt
  obtain ⟨gs, hgs⟩ : ∃ l, l = C.gates.map normGate := ⟨_, rfl⟩
  have hgsl : gs.length = C.gates.length := by rw [hgs, List.length_map]
  have hsize : C.size = gs.length := by rw [hgsl]; rfl
  have hgsget : ∀ j (hj : j < gs.length),
      gs[j] = normGate (C.gates[j]'(by rw [← hgsl]; exact hj)) := by
    intro j hj; subst hgs; simp
  have normOk : ∀ g ∈ gs, NOk g := by
    intro g hg
    rw [hgs] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok _ (fan _ hg0)
  have evalW : ∀ W : List Bool, C.eval W = (wiresFrom gs W).getD C.output false := by
    intro W
    rw [hgs, wiresFrom_norm]; rfl
  have nc : ∀ b : Bool, ¬ ∀ y : Fin 8 → Bool,
      C.eval ((List.ofFn y).insertIdx v false) = b := by
    intro b hb
    obtain ⟨y, z, hyz⟩ := hnc
    exact hyz ((hb y).trans (hb z).symm)
  obtain ⟨accR, hacc⟩ : ∃ a, a = elim 8 gs (initL v false, []) := ⟨_, rfl⟩
  have invR : ∀ y : Fin 8 → Bool,
      Inv 8 (List.ofFn y) (wiresFrom gs ((List.ofFn y).insertIdx v false)) accR := by
    intro y
    rw [hacc]
    exact inv_elim 8 (List.ofFn y) (by simp) gs _ _ (fun g hg => (normOk g hg).1) (inv_initR y v)
  have valueR : ∀ y : Fin 8 → Bool,
      (accR.1.getD C.output (Sum.inl false)).val (wiresFrom accR.2 (List.ofFn y)) =
        C.eval ((List.ofFn y).insertIdx v false) := by
    intro y; rw [((invR y).2 C.output).2, evalW]
  have outNC : ∀ c, accR.1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro c hc
    apply nc c
    intro y
    rw [← valueR y, hc]; rfl
  have finish : accR.2.length + 2 ≤ C.size →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧ circuitFun 8 D = f0 false := by
    intro hsz
    cases ho : accR.1.getD C.output (Sum.inl false) with
    | inl c => exact absurd ho (outNC c)
    | inr k =>
      refine ⟨⟨accR.2, k⟩, ?_, hsz, ?_⟩
      · rw [hacc]; exact elim_ok 8 gs _ (by simp)
      · funext y
        have := valueR y
        rw [ho] at this
        exact this
  let gate : ℕ → Gate := fun j => gs.getD j ⟨GateOp.and, []⟩
  have gateEq : ∀ j (hj : j < gs.length), gate j = gs[j] := by
    intro j hj; simp [gate, List.getD_eq_getElem?_getD, hj]
  have gateSome : ∀ j (hj : j < gs.length), gs[j]? = some (gate j) := by
    intro j hj; rw [gateEq j hj]; exact List.getElem?_eq_getElem hj
  have hAv : ∀ q, (elim 8 (gs.take q) (initL v false, [])).1.getD v (Sum.inl false)
      = Sum.inl false := by
    intro q
    rw [elim_getD 8 v _ _ _ (by simp [initL])]
    show (initL v false).getD v (Sum.inl false) = _
    rw [initL_getD _ _ _ hv9]; simp [initStat]
  let R : Finset ℕ := (Finset.range gs.length).filter (fun j => (v : ℕ) ∈ (gate j).inputs)
  have countR := elim_count2 8 (initL v false, []) gs normOk R (by
    intro p hp
    obtain ⟨hpl, hpv⟩ := Finset.mem_filter.1 hp
    rw [Finset.mem_range] at hpl
    exact ⟨gate p, gateSome p hpl, Or.inr ⟨v, hpv, false, hAv p⟩⟩)
  rw [← hacc] at countR
  simp only [List.length_nil, Nat.zero_add] at countR
  by_cases big : accR.2.length + 2 ≤ C.size
  · exact Or.inl (finish big)
  have noDep : ∀ y : Fin 8 → Bool, (∀ j (hj : j < gs.length),
      Good (fun i => i = (v : ℕ)) 9 ((List.ofFn y).insertIdx v false)
        ((List.ofFn y).insertIdx v true) gs[j] gs[j] (9 + j)) → f0 false y = f0 true y := by
    intro y hg
    by_cases ho : C.output = v
    · exfalso
      apply nc false
      intro z
      rw [evalW, wiresFrom_getD_lt _ _ _ (by rw [ins_len, ho]; exact hv9), ho, ins_getD]
      simp [initStat, Stat.val]
    · show C.eval _ = C.eval _
      rw [evalW, evalW]
      refine agree (fun i => i = (v : ℕ)) 9 _ _ gs gs _ _ rfl (by rw [ins_len, ins_len])
        (by rw [ins_len]) (fun i _ => ⟨rfl, rfl⟩) ?_ ?_ C.output ho
      · intro i hi
        rw [ins_getD, ins_getD]
        have hi' : i ≠ (v : ℕ) := hi
        simp [initStat, hi']
      · intro j hj _
        right
        rw [ins_len]
        exact hg j hj
  rcases Nat.lt_or_ge R.card 1 with h0 | h1
  · exfalso
    have hR : R = ∅ := Finset.card_eq_zero.1 (by omega)
    obtain ⟨u, hu⟩ : ∃ u : Fin 9, u ≠ v := by
      by_cases hv0 : v = 0
      · exact ⟨1, by rw [hv0]; decide⟩
      · exact ⟨0, fun h => hv0 h.symm⟩
    obtain ⟨y, hy, -⟩ := hdep u hu
    apply hy (noDep y (fun j hj => good_free _ _ _ _ _ _ (fun i hi hiv => ?_)))
    have hiv' : i = (v : ℕ) := hiv
    rw [hiv'] at hi
    have hjR : j ∈ R := Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, by rw [gateEq j hj]; exact hi⟩
    rw [hR] at hjR
    simp at hjR
  obtain ⟨p, hRp⟩ := Finset.card_eq_one.1 (show R.card = 1 by omega)
  have hpR : p ∈ R := by rw [hRp]; simp
  obtain ⟨hpl, hpv⟩ := Finset.mem_filter.1 hpR
  rw [Finset.mem_range] at hpl
  have uniq : ∀ j, j < gs.length → (v : ℕ) ∈ (gate j).inputs → j = p := by
    intro j hj hjv
    have hjR : j ∈ R := Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hjv⟩
    rw [hRp] at hjR
    simpa using hjR
  have gOk : NOk (gate p) := normOk _ (by rw [gateEq p hpl]; exact List.getElem_mem hpl)
  by_cases pass : (gate p).op = GateOp.or ∧ ∃ y, y ≠ (v : ℕ) ∧ y < 9 + p ∧
      ((gate p).inputs = [(v : ℕ), y] ∨ (gate p).inputs = [y, (v : ℕ)])
  · obtain ⟨gor, y, hyv, hyp, hins⟩ := pass
    rcases Nat.lt_or_ge y 9 with hy9 | hy9
    · exfalso
      obtain ⟨z, hz, hzy⟩ := hdep ⟨y, hy9⟩ (fun h => hyv (by rw [← h]))
      apply hz (noDep z (fun j hj => ?_))
      by_cases hjp : j = p
      · subst hjp
        rw [← gateEq j hj]
        intro V V' _ _ hpre hVV
        have e1 : V.getD y false = true := by rw [(hpre y hy9).1]; exact hzy
        have e2 : V'.getD y false = true := by rw [← hVV y hyv]; exact e1
        unfold evalG
        rw [gor]
        rcases hins with h | h <;> rw [h] <;>
          simp only [List.map_cons, List.map_nil, GateOp.eval, e1, e2] <;> simp
      · apply good_free
        intro i hi hiv
        have hiv' : i = (v : ℕ) := hiv
        apply hjp
        apply uniq j hj
        rw [gateEq j hj, ← hiv']
        exact hi
    · right
      have hpC : p < C.size := by rw [hsize]; exact hpl
      have hgate : C.gates.get ⟨p, hpC⟩ = gate p := by
        have h1 := (gateEq p hpl).trans (hgsget p hpl)
        rw [h1] at gor ⊢
        rw [normGate_of_or _ gor]; rfl
      refine ⟨⟨p, hpC⟩, y, hy9, hyp, ?_, ?_, ?_⟩
      · change (C.gates.get ⟨p, hpC⟩).op = GateOp.or
        rw [hgate]; exact gor
      · change (C.gates.get ⟨p, hpC⟩).inputs = [(v : ℕ), y] ∨
          (C.gates.get ⟨p, hpC⟩).inputs = [y, (v : ℕ)]
        rw [hgate]; exact hins
      · intro x10 hx10
        have hx : (x10 : ℕ) < gs.length := by rw [← hsize]; exact x10.isLt
        have hr := (reader_iff v (C.gates.get x10) (fan _ (List.get_mem _ _))).1 hx10
        have := uniq x10 hx (by rw [gateEq x10 hx, hgsget x10 hx]; exact hr)
        exact Fin.ext this
  · exfalso
    have hA : (elim 8 (gs.take p) (initL v false, [])).1.length = 9 + p := by
      rw [elim_fst_len]; simp [initL]; omega
    have hconst : ∃ c, (elim 8 (gs.take (p + 1)) (initL v false, [])).1.getD (9 + p)
        (Sum.inl false) = Sum.inl c := by
      rw [elim_succ_take 8 gs _ p (gate p) (gateSome p hpl)]
      simp only [elimStep]
      rw [← hA, getD_snoc_eq]
      apply simplify_const
      · exact gOk.1.1
      · simpa using gOk.1.2
      · intro h; simpa using gOk.2 h
      · exact List.mem_map.2 ⟨v, hpv, hAv p⟩
      · intro hor s hs
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs
        by_cases hiv : i = (v : ℕ)
        · rw [hiv, hAv]; exact ⟨false, rfl⟩
        · have hge : ¬ i < 9 + p := fun hlt => pass
            ⟨hor, i, hiv, hlt, pair_of _ _ _ gOk.1.2 hpv hi hiv⟩
          exact ⟨false, List.getD_eq_default _ _ (by omega)⟩
    obtain ⟨c, hc⟩ := hconst
    have hcR : accR.1.getD (9 + p) (Sum.inl false) = Sum.inl c := by
      rw [hacc, ← hc]
      conv_lhs => rw [← List.take_length (l := gs)]
      exact elim_take_getD 8 gs _ p gs.length (9 + p) _ hpl hpl (by simp [initL])
    have hout : C.output ≠ 9 + p := fun h => outNC c (by rw [h]; exact hcR)
    by_cases hq : ∃ q, q < gs.length ∧ q ≠ p ∧ 9 + p ∈ (gate q).inputs
    · obtain ⟨q, hql, hqp, hqi⟩ := hq
      apply big
      have hc2 := elim_count2 8 (initL v false, []) gs normOk {p, q} (by
        intro r hr
        rcases Finset.mem_insert.1 hr with h | h
        · rw [h]; exact ⟨gate p, gateSome p hpl, Or.inr ⟨v, hpv, false, hAv p⟩⟩
        · rw [Finset.mem_singleton.1 h]
          refine ⟨gate q, gateSome q hql, Or.inr ⟨9 + p, hqi, ?_⟩⟩
          rcases Nat.lt_or_ge p q with hlt | hge
          · exact ⟨c, (elim_take_getD 8 gs _ p q (9 + p) _ hpl hlt (by simp [initL])).trans hc⟩
          · exact ⟨false, List.getD_eq_default _ _ (by rw [elim_fst_len]; simp [initL]; omega)⟩)
      rw [← hacc, Finset.card_pair (Ne.symm hqp)] at hc2
      simp only [List.length_nil, Nat.zero_add] at hc2
      omega
    · push_neg at hq
      obtain ⟨gs', hgs'⟩ : ∃ l, l = gs.set p ⟨GateOp.and, []⟩ := ⟨_, rfl⟩
      have hl' : gs'.length = gs.length := by rw [hgs', List.length_set]
      have ok' : ∀ g ∈ gs', NOk g := by
        intro g hg
        rw [hgs'] at hg
        rcases List.mem_or_eq_of_mem_set hg with h | h
        · exact normOk g h
        · rw [h]; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
      have same : ∀ W : List Bool, W.length = 9 →
          (wiresFrom gs' W).getD C.output false = (wiresFrom gs W).getD C.output false := by
        intro W hW
        refine agree (fun i => i = 9 + p) 9 W W gs' gs W W hl' rfl (by omega)
          (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => rfl) ?_ C.output hout
        intro j hj hj'
        by_cases hjp : j = p
        · left; show W.length + j = 9 + p; omega
        · right
          have e : gs'[j] = gs[j] := by
            simp only [hgs']
            rw [List.getElem_set_ne (Ne.symm hjp)]
          rw [e]
          apply good_free
          intro i hi hib
          have hib' : i = 9 + p := hib
          apply hq j hj' hjp
          rw [gateEq j hj', ← hib']
          exact hi
      obtain ⟨accD, hD⟩ : ∃ a, a = elim 9 gs' (idL, []) := ⟨_, rfl⟩
      have cD := elim_count2 9 (idL, []) gs' ok' {p} (by
        intro r hr
        rw [Finset.mem_singleton.1 hr]
        refine ⟨⟨GateOp.and, []⟩, ?_, Or.inl rfl⟩
        rw [hgs']
        exact List.getElem?_set_self hpl)
      rw [← hD, Finset.card_singleton] at cD
      simp only [List.length_nil, Nat.zero_add] at cD
      have valD : ∀ W : List Bool, W.length = 9 →
          (accD.1.getD C.output (Sum.inl false)).val (wiresFrom accD.2 W) = C.eval W := by
        intro W hW
        have inv := inv_elim 9 W hW gs' _ _ (fun g hg => (ok' g hg).1) (inv_id W hW)
        rw [← hD] at inv
        rw [(inv.2 C.output).2, same W hW, evalW]
      cases ho : accD.1.getD C.output (Sum.inl false) with
      | inl b =>
        apply nc b
        intro y
        rw [← valD _ (ins_len y v false), ho]; rfl
      | inr k =>
        have hmin := minimal ⟨accD.2, k⟩ (by rw [hD]; exact elim_ok 9 gs' _ (by simp)) (by
          funext x
          have := valD (List.ofFn x) (by simp)
          rw [ho] at this
          exact this)
        change C.size ≤ accD.2.length at hmin
        omega
