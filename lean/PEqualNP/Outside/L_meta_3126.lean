import Mathlib
import PEqualNP.Defs

-- Constant-propagation lemmas adapted from L-meta-1543 under Apache-2.0.
namespace PEqualNP.Outside.L_meta_3126

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

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj


abbrev St : Type := List Stat × List Gate × List ℕ

def estep (n : ℕ) (ov : ℕ → Option Bool) (acc : St) (g : Gate) : St :=
  (acc.1 ++ [match ov acc.1.length with
      | some c => Sum.inl c
      | none => (simplify g.op (n + acc.2.1.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2.1 ++ (simplify g.op (n + acc.2.1.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList,
    acc.2.2 ++ ((simplify g.op (n + acc.2.1.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList.map fun _ => acc.1.length))

def erun (n : ℕ) (ov : ℕ → Option Bool) (gs : List Gate) (acc : St) : St :=
  gs.foldl (estep n ov) acc

theorem erun_ok (n : ℕ) (ov : ℕ → Option Bool) (gs : List Gate) : ∀ acc : St,
    (∀ g ∈ acc.2.1, Ok g) → ∀ g ∈ (erun n ov gs acc).2.1, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (estep n ov acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

def EInv (n : ℕ) (y : List Bool) (w : List Bool) (acc : St) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.1.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2.1 y) = w.getD i false

theorem inv_erun (n : ℕ) (ov : ℕ → Option Bool) (y : List Bool) (hy : y.length = n)
    (gs : List Gate) :
    ∀ (w : List Bool) (acc : St), (∀ g ∈ gs, Ok g) →
      (∀ k c, ov k = some c → (wiresFrom gs w).getD k false = c) →
      EInv n y w acc → EInv n y (wiresFrom gs w) (erun n ov gs acc) := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hov h
    set gv := g.op.eval (g.inputs.map fun i => w.getD i false) with hgv
    have hfull : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [gv]) := rfl
    apply ih (w ++ [gv]) (estep n ov acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (fun k c hk => by rw [← hfull]; exact hov k c hk)
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2.1 y with hw'
    have lw' : w'.length = n + acc.2.1.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.1.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2.1 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    have hgvc : ∀ c, ov w.length = some c → gv = c := by
      intro c hc
      have h1 := hov w.length c hc
      rw [hfull] at h1
      obtain ⟨t', ht', _⟩ := wiresFrom_prefix gs (w ++ [gv])
      rw [ht', List.getD_append _ _ _ _ (by simp), getD_snoc_eq] at h1
      exact h1
    refine ⟨by simp [estep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [match ov acc.1.length with
        | some c => Sum.inl c
        | none => r.2]).getD i (Sum.inl false)).Valid (n + (acc.2.1 ++ r.1.toList).length) ∧
      ((acc.1 ++ [match ov acc.1.length with
        | some c => Sum.inl c
        | none => r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2.1 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      cases hov' : ov w.length with
      | some c =>
        exact ⟨trivial, by simp only [Stat.val]; exact (hgvc c hov').symm⟩
      | none =>
        exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem erun_snoc (n : ℕ) (ov : ℕ → Option Bool) (pre : List Gate) (g : Gate) (acc : St) :
    erun n ov (pre ++ [g]) acc = estep n ov (erun n ov pre acc) g := by
  simp [erun, List.foldl_append]

theorem simplify_inr (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hsome : (simplify op m ins).1.isSome) :
    ∀ s ∈ ins, ∃ j, s = Sum.inr j := by
  intro s hs
  cases s with
  | inr j => exact ⟨j, rfl⟩
  | inl c =>
    have := simplify_count op m ins hop hlen hnot ⟨c, hs⟩
    rw [this] at hsome
    simp at hsome

theorem struct_erun (n : ℕ) (ov : ℕ → Option Bool) (NC : ℕ → Prop)
    (hovNC : ∀ k, ov k = none → NC k) (acc0 : St)
    (h0 : ∀ k j, acc0.1.getD k (Sum.inl false) = Sum.inr j → NC k)
    (h1 : acc0.2.1 = []) (h2 : acc0.2.2 = []) :
    ∀ gs : List Gate, (∀ g ∈ gs, NOk g) →
      (erun n ov gs acc0).1.length = acc0.1.length + gs.length ∧
      (∀ k j, (erun n ov gs acc0).1.getD k (Sum.inl false) = Sum.inr j → NC k) ∧
      (erun n ov gs acc0).2.2.length = (erun n ov gs acc0).2.1.length ∧
      (erun n ov gs acc0).2.2.Nodup ∧
      (∀ k ∈ (erun n ov gs acc0).2.2, acc0.1.length ≤ k ∧ ∃ g,
        gs[k - acc0.1.length]? = some g ∧ ∀ a ∈ g.inputs, a < k ∧ NC a) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    simp only [erun, List.foldl_nil, List.length_nil, Nat.add_zero, h1, h2, List.nodup_nil,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and]
    exact h0
  | append_singleton pre g ih =>
    intro hok
    obtain ⟨il, inc, ilen, ind, irec⟩ := ih (fun g' hg' => hok g' (List.mem_append_left _ hg'))
    have hgok : NOk g := hok g (List.mem_append_right _ List.mem_cons_self)
    rw [erun_snoc]
    set acc := erun n ov pre acc0 with hacc
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    set r := simplify g.op (n + acc.2.1.length) ins with hr
    have recLt : ∀ k ∈ acc.2.2, k < acc.1.length := by
      intro k hk
      obtain ⟨hk0, g', hg', _⟩ := irec k hk
      have := (List.getElem?_eq_some_iff.1 hg').1
      omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [estep, il]
      omega
    · intro k j hk
      change (acc.1 ++ [match ov acc.1.length with
        | some c => Sum.inl c
        | none => r.2]).getD k (Sum.inl false) = Sum.inr j at hk
      by_cases hkl : k = acc.1.length
      · subst hkl
        rw [getD_snoc_eq] at hk
        cases hov : ov acc.1.length with
        | some c => rw [hov] at hk; simp at hk
        | none => exact hovNC _ hov
      · rw [getD_snoc_ne _ _ _ _ hkl] at hk
        exact inc k j hk
    · simp [estep, ilen]
    · change (acc.2.2 ++ (r.1.toList.map fun _ => acc.1.length)).Nodup
      cases hro : r.1 with
      | none => simpa using ind
      | some gg =>
        simp only [Option.toList_some, List.map_cons, List.map_nil]
        rw [List.nodup_append]
        refine ⟨ind, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        have := recLt a ha
        omega
    · intro k hk
      change k ∈ acc.2.2 ++ (r.1.toList.map fun _ => acc.1.length) at hk
      rcases List.mem_append.1 hk with hk | hk
      · obtain ⟨hk0, g', hg', hin⟩ := irec k hk
        refine ⟨hk0, g', ?_, hin⟩
        rw [List.getElem?_append_left (by have := (List.getElem?_eq_some_iff.1 hg').1; omega)]
        exact hg'
      · cases hro : r.1 with
        | none => rw [hro] at hk; simp at hk
        | some gg =>
          rw [hro] at hk
          simp only [Option.toList_some, List.map_cons, List.map_nil,
            List.mem_singleton] at hk
          subst hk
          refine ⟨by omega, g, ?_, ?_⟩
          · rw [il, show acc0.1.length + pre.length - acc0.1.length = pre.length by omega]
            simp
          · intro a ha
            have hsome : r.1.isSome := by rw [hro]; rfl
            obtain ⟨j, hj⟩ := simplify_inr g.op (n + acc.2.1.length) ins hgok.1.1
              (by simpa [hins] using hgok.1.2) (by simpa [hins] using hgok.2) hsome
              (acc.1.getD a (Sum.inl false)) (List.mem_map.2 ⟨a, ha, rfl⟩)
            refine ⟨?_, inc a j hj⟩
            by_contra hge
            rw [List.getD_eq_default _ _ (by omega)] at hj
            simp at hj

theorem mem_norm (g : Gate) (w : ℕ) (hw : w ∈ g.inputs)
    (hc : g.op ≠ GateOp.not ∨ g.inputs[0]? = some w) : w ∈ (normGate g).inputs := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | not =>
    simp only [ne_eq, not_true_eq_false, false_or] at hc
    cases xs with
    | nil => simp at hw
    | cons a t =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      simp [normGate]
  | _ => simpa [normGate] using hw

theorem wires_getD_prefix (gs pre : List Gate) (y : List Bool) (k : ℕ)
    (hk : k < y.length + pre.length) (hpre : pre <+: gs) :
    (wiresFrom pre y).getD k false = (wiresFrom gs y).getD k false := by
  obtain ⟨post, rfl⟩ := hpre
  rw [wiresFrom_append]
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix post (wiresFrom pre y)
  rw [ht, List.getD_append _ _ _ _ (by rw [length_wiresFrom]; exact hk)]

end PEqualNP.Outside.L_meta_3126

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3126

theorem PEqualNP.Outside.L_meta_3126 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Option (Fin (7 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x1 →     have x4 : (Fin (7 : ℕ) → Bool) → List Bool := fun (x4 : Fin (7 : ℕ) → Bool) => List.map (fun (x5 : Option (Fin (7 : ℕ))) => x5.elim Bool.false x4) x2;     have x5 : Fin x1.gates.length → Prop := fun (x5 : Fin x1.gates.length) =>       have x6 : PEqualNP.CircuitLowerBounds.Gate := x1.gates.get x5;       ∀ x7 ∈ x6.inputs, x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∨ x6.inputs[(0 : ℕ)]? = Option.some x7 → ∃ (x10 : Fin (7 : ℕ) → Bool) (x11 : Fin (7 : ℕ) → Bool), ({ gates := List.take (↑x5) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x4 x10)).getD x7 Bool.false ≠ ({ gates := List.take (↑x5) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x4 x11)).getD x7 Bool.false;     (∃ (x6 : Fin (7 : ℕ) → Bool) (x7 : Fin (7 : ℕ) → Bool), x1.eval (x4 x6) ≠ x1.eval (x4 x7)) → ∃ (x7 : Finset (Fin x1.gates.length)), (∀ x8 ∈ x7, x5 x8) ∧ PEqualNP.MetaComplexity.HasCircuitSize (7 : ℕ) (fun (x8 : Fin (7 : ℕ) → Bool) => x1.eval (x4 x8)) x7.card := by
  intro C L fan
  dsimp only
  intro hnc
  classical
  let inp : (Fin 7 → Bool) → List Bool := fun x => L.map fun o => o.elim false x
  let full : (Fin 7 → Bool) → List Bool := fun x => wiresFrom C.gates (inp x)
  let NC : ℕ → Prop := fun k =>
    ∃ x x' : Fin 7 → Bool, (full x).getD k false ≠ (full x').getD k false
  let ov : ℕ → Option Bool := fun k =>
    if h : ∃ c, ∀ x : Fin 7 → Bool, (full x).getD k false = c then some (Classical.choose h)
    else none
  have hovNC : ∀ k, ov k = none → NC k := by
    intro k hk
    by_contra hnc'
    have hc : ∃ c, ∀ x : Fin 7 → Bool, (full x).getD k false = c :=
      ⟨(full fun _ => false).getD k false, fun x => by
        by_contra hne
        exact hnc' ⟨x, fun _ => false, hne⟩⟩
    have : ov k = some (Classical.choose hc) := dif_pos hc
    rw [this] at hk
    cases hk
  have hovC : ∀ k c, ov k = some c → ∀ x, (full x).getD k false = c := by
    intro k c hk x
    by_cases h : ∃ c, ∀ x : Fin 7 → Bool, (full x).getD k false = c
    · have e : ov k = some (Classical.choose h) := dif_pos h
      rw [e, Option.some.injEq] at hk
      subst hk
      exact Classical.choose_spec h x
    · have e : ov k = none := dif_neg h
      rw [e] at hk
      cases hk
  let gs := C.gates.map normGate
  have normOk : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok _ (fan _ hg0)
  let init : List Stat := L.map fun o => o.elim (Sum.inl false) fun m => Sum.inr m.val
  let acc := erun 7 ov gs (init, [], [])
  have inpLen : ∀ x, (inp x).length = L.length := by intro x; simp [inp]
  have h0 : ∀ k j, init.getD k (Sum.inl false) = Sum.inr j → NC k := by
    intro k j hk
    simp only [init, List.getD_eq_getElem?_getD, List.getElem?_map] at hk
    rcases hL : L[k]? with _ | _ | m
    · rw [hL] at hk; simp at hk
    · rw [hL] at hk; simp at hk
    · have hkl : k < L.length := (List.getElem?_eq_some_iff.1 hL).1
      refine ⟨fun _ => false, fun _ => true, ?_⟩
      rw [← wires_getD_prefix C.gates [] (inp _) k (by simp [inpLen, hkl]) (List.nil_prefix),
        ← wires_getD_prefix C.gates [] (inp _) k (by simp [inpLen, hkl]) (List.nil_prefix)]
      simp [wiresFrom, inp, List.getD_eq_getElem?_getD, hL]
  obtain ⟨sl, sinc, slen, snd, srec⟩ :=
    struct_erun 7 ov NC hovNC (init, [], []) h0 rfl rfl gs normOk
  have inv (x : Fin 7 → Bool) : EInv 7 (List.ofFn x) (wiresFrom gs (inp x)) acc := by
    apply inv_erun 7 ov (List.ofFn x) (by simp) gs (inp x) (init, [], [])
      (fun g hg => (normOk g hg).1)
    · intro k c hk
      rw [wiresFrom_norm]
      exact hovC k c hk x
    · refine ⟨by simp [init, inp], ?_⟩
      intro i
      simp only [init, inp, List.getD_eq_getElem?_getD, List.getElem?_map]
      rcases L[i]? with _ | _ | m <;> simp [Stat.Valid, Stat.val, wiresFrom] <;> fin_cases m <;> rfl
  have value (x : Fin 7 → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2.1 (List.ofFn x)) =
      C.eval (inp x) := by
    rw [((inv x).2 C.output).2, show gs = C.gates.map normGate from rfl, wiresFrom_norm]
    rfl
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x, x', hne⟩ := hnc
    have e1 := value x
    have e2 := value x'
    rw [ho] at e1 e2
    simp only [Stat.val] at e1 e2
    exact hne (e1.symm.trans e2)
  | inr k =>
    let S : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun i => i.val + L.length ∈ acc.2.2)
    refine ⟨S, ?_, ⟨acc.2.1, k⟩, ?_, ?_, ?_⟩
    · intro i hi
      have hmem := (Finset.mem_filter.1 hi).2
      obtain ⟨_, g, hg, hin⟩ := srec _ hmem
      have e : i.val + L.length - (init, ([] : List Gate), ([] : List ℕ)).1.length = i.val := by
        simp [init]
      rw [e] at hg
      have hg' : g = normGate (C.gates.get i) := by
        simp only [gs, List.getElem?_map] at hg
        rw [List.getElem?_eq_getElem i.isLt] at hg
        simp only [Option.map_some, Option.some.injEq] at hg
        rw [← hg]
        rfl
      subst hg'
      intro w hw hc
      obtain ⟨hlt, x, x', hne⟩ := hin w (mem_norm _ w hw hc)
      refine ⟨x, x', ?_⟩
      have hpre : C.gates.take i.val <+: C.gates := List.take_prefix _ _
      have hlen : w < (inp x).length + (C.gates.take i.val).length := by
        rw [inpLen, List.length_take, min_eq_left (le_of_lt i.isLt)]
        omega
      have hlen' : w < (inp x').length + (C.gates.take i.val).length := by
        rw [inpLen] at hlen ⊢
        exact hlen
      change (wiresFrom (C.gates.take i.val) (inp x)).getD w false ≠
        (wiresFrom (C.gates.take i.val) (inp x')).getD w false
      rw [wires_getD_prefix C.gates _ _ w hlen hpre, wires_getD_prefix C.gates _ _ w hlen' hpre]
      exact hne
    · exact erun_ok 7 ov gs (init, [], []) (by simp)
    · change acc.2.1.length ≤ S.card
      rw [← slen, ← List.toFinset_card_of_nodup snd]
      refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
        (f := fun i : Fin C.gates.length => i.val + L.length))
      intro m hm
      rw [List.mem_toFinset] at hm
      obtain ⟨hm0, g, hg, _⟩ := srec m hm
      have hlt : m - L.length < C.gates.length := by
        have := (List.getElem?_eq_some_iff.1 hg).1
        simp [gs, init] at this hm0 ⊢
        omega
      have hm0' : L.length ≤ m := by simpa [init] using hm0
      refine Finset.mem_image.2 ⟨⟨m - L.length, hlt⟩, ?_, by simp; omega⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [show m - L.length + L.length = m by omega]
      exact hm
    · intro x
      change (wiresFrom acc.2.1 (List.ofFn x)).getD k false = _
      have hv := value x
      rw [ho] at hv
      simpa only [Stat.val] using hv
