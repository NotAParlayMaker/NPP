import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9433_aux

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/Shannon.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers

open PEqualNP.CircuitLowerBounds

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

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitHelpers

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/Support.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end CircuitHelpers

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/Elim.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers

open PEqualNP.CircuitLowerBounds

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

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end CircuitHelpers

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/Parity.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers

open PEqualNP.CircuitLowerBounds

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

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
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
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

end CircuitHelpers

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/Parity3.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers

open PEqualNP.CircuitLowerBounds

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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
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

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

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

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
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
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

end CircuitHelpers

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/Parity4.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

theorem st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Stat.const c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Stat.const c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'

end CircuitHelpers

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/PermInputs.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end CircuitHelpers.PermInputs

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/ForestElim.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers.PermInputs

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := CircuitHelpers.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end CircuitHelpers.Forest

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/Readers.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitHelpers

open CircuitHelpers.PermInputs

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  CircuitHelpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS

theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end

end CircuitHelpers.Readers

end

-- From pequalnp-proofs/lean/PEqualNP/MetaComplexity/Helpers/ReadersPat.lean
section

open PEqualNP.MetaComplexity

namespace CircuitHelpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitHelpers

theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)

end

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

theorem Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc

theorem Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc

theorem Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩

end

end CircuitHelpers.Readers

end

-- From .pnp-tools/Theta9433Bypass.lean
section

namespace Theta9433Bypass

open PEqualNP.CircuitLowerBounds

open CircuitHelpers

def newSlot (p q : ℕ) : ℕ := if q < p then q else q - 1

def wire (n p substitute index : ℕ) : ℕ :=
  if index = n + p then substitute else if n + p < index then index - 1 else index

def redirect (n p substitute : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire n p substitute)⟩

def remove (n p substitute : ℕ) (gs : List Gate) : List Gate :=
  (gs.eraseIdx p).map (redirect n p substitute)

theorem gate_at {n p substitute q : ℕ} {gs : List Gate} {g : Gate}
    (other : q ≠ p) (orig : gs[q]? = some g) :
    (remove n p substitute gs)[newSlot p q]? = some (redirect n p substitute g) := by
  rw [remove, List.getElem?_map]
  by_cases before : q < p
  · simp [newSlot, before, List.getElem?_eraseIdx_of_lt before, orig]
  · have index : q - 1 + 1 = q := by omega
    rw [newSlot, ite_eq_right before, List.getElem?_eraseIdx_of_ge (show p ≤ q - 1 by omega),
      index, orig]
    rfl

theorem old_gate {n p substitute j : ℕ} {gs : List Gate} {g : Gate}
    (atNew : (remove n p substitute gs)[j]? = some g) :
    ∃ q h, q ≠ p ∧ newSlot p q = j ∧ gs[q]? = some h ∧ g = redirect n p substitute h := by
  simp only [remove, List.getElem?_map, List.getElem?_eraseIdx] at atNew
  by_cases before : j < p
  · refine ⟨j, ?_⟩
    simp [before] at atNew
    obtain ⟨h, hh, hEq⟩ := atNew
    exact ⟨h, by omega, by simp [newSlot, before], hh, hEq.symm⟩
  · refine ⟨j + 1, ?_⟩
    simp [before] at atNew
    obtain ⟨h, hh, hEq⟩ := atNew
    exact ⟨h, by omega, by simp [newSlot, show ¬ j + 1 < p by omega], hh, hEq.symm⟩

theorem wire_at {n p substitute q : ℕ} (other : q ≠ p) :
    wire n p substitute (n + q) = n + newSlot p q := by
  by_cases before : q < p
  · simp [wire, newSlot, before, other, show ¬ n + p < n + q by omega]
  · simp [wire, newSlot, before, other, show n + p < n + q by omega]
    omega

theorem wire_raw {n p substitute j : ℕ} (raw : j < n) : wire n p substitute j = j := by
  simp [wire, show j ≠ n + p by omega, show ¬ n + p < j by omega]

theorem wire_before {n p substitute j q : ℕ} (back : substitute < n + p)
    (other : q ≠ p) (fits : j < n + q) :
    wire n p substitute j < n + newSlot p q := by
  by_cases before : q < p
  · simp [wire, newSlot, before, show j ≠ n + p by omega, show ¬ n + p < j by omega, fits]
  · have later : p < q := by omega
    unfold wire newSlot
    simp only [ite_eq_right before]
    split_ifs <;> omega

theorem clean {n p substitute : ℕ} {gs : List Gate}
    (original : CleanL n gs) (back : substitute < n + p) : CleanL n (remove n p substitute gs) := by
  intro j g h
  obtain ⟨q, old, hne, rfl, orig, rfl⟩ := old_gate h
  rcases original q old orig with ⟨op, a, earlier, pins⟩ | ⟨op, a, b, ha, hb, pins⟩
  · exact Or.inl ⟨op, wire n p substitute a, wire_before back hne earlier, by simp [redirect, pins]⟩
  · exact Or.inr ⟨op, wire n p substitute a, wire n p substitute b,
      wire_before back hne ha, wire_before back hne hb, by simp [redirect, pins]⟩

theorem size {n p substitute : ℕ} {gs : List Gate} (hp : p < gs.length) :
    (remove n p substitute gs).length + 1 = gs.length := by
  simpa [remove] using List.length_eraseIdx_add_one hp

theorem eval {n p substitute : ℕ} {gs : List Gate} (original : CleanL n gs)
    (back : substitute < n + p) (x : Fin n → Bool)
    (same : vl gs x (n + p) = vl gs x substitute) :
    ∀ j < n + gs.length, vl (remove n p substitute gs) x (wire n p substitute j) = vl gs x j := by
  have newClean := clean original back
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro valid
    by_cases raw : j < n
    · rw [wire_raw raw, vl_input _ _ _ raw, vl_input _ _ _ raw]
    · by_cases removed : j = n + p
      · subst j
        rw [show wire n p substitute (n + p) = substitute by simp [wire], same]
        have e : wire n p substitute substitute = substitute := by simp [wire, show substitute ≠ n + p by omega,
          show ¬ n + p < substitute by omega]
        have result := ih substitute back (by omega)
        simpa only [e] using result
      · let q := j - n
        have eq : j = n + q := by dsimp [q]; omega
        have other : q ≠ p := by omega
        have qLt : q < gs.length := by omega
        let g := gs[q]
        have orig : gs[q]? = some g := List.getElem?_eq_getElem qLt
        have issued := gate_at (n := n) (substitute := substitute) other orig
        rw [eq, wire_at other, vl_gate _ newClean x _ _ issued, vl_gate _ original x q g orig]
        change g.op.eval ((g.inputs.map (wire n p substitute)).map (vl _ x)) =
          g.op.eval (g.inputs.map (vl gs x))
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a ha
        have earlier := (original q g orig).lt a ha
        exact ih a (by omega) (by omega)

end Theta9433Bypass

end

-- From .pnp-tools/Cactus10440Floor.lean
section

namespace Cactus10440Floor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers

open CircuitHelpers.PermInputs CircuitHelpers.Readers

abbrev Fn (n : ℕ) := (Fin n → Bool) → Bool

def Lower {n : ℕ} (k : ℕ) (f : Fn n) : Prop :=
  ∀ s, HasCircuitSize n f s → k ≤ s

def cofactor {n : ℕ} (f : Fn n) (p : Fin n) (b : Bool) : Fn n :=
  fun x => f (Function.update x p b)

def Nonconst {n : ℕ} (f : Fn n) : Prop := ∃ x y, f x ≠ f y

theorem lower_one {f : Fn 9} {p : Fin 9} {b : Bool} {k : ℕ} (positive : 0 < k)
    (dependent : Dep f p) (nonconst : Nonconst (cofactor f p b))
    (residual : Lower k (cofactor f p b)) : Lower (k + 1) f := by
  intro size fit
  by_contra tooSmall
  obtain ⟨C, fan, count, semantics⟩ := fit
  have cap : HasCircuitSize 9 f (k - 1 + 1) := ⟨C, fan, by omega, semantics⟩
  have smaller := CircuitHelpers.Forest.one_gate_at
    8 f p b (k - 1) dependent nonconst cap
  have impossible := residual _ smaller
  omega

theorem lower_two {f : Fn 9} {p : Fin 9} {k : ℕ}
    (dependent : Dep f p) (nonconst : ∀ b, Nonconst (cofactor f p b))
    (residual : ∀ b, Lower k (cofactor f p b)) : Lower (k + 2) f := by
  intro size fit
  obtain ⟨b, smaller, saved, works⟩ := gate_elim_at 8 f p size dependent nonconst fit
  have enough := residual b smaller works
  omega

def majority (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

abbrev Edge := Fin 9 × Fin 9

def graph (edges : List Edge) (orInputs : List (Fin 9)) (x : Fin 9 → Bool) : Bool :=
  orInputs.any x || edges.any (fun (a, b) => x a && x b)

end Cactus10440Floor

end

-- From pequalnp-proofs/lean/PEqualNP/Outside/L_meta_2752.lean
section

namespace BranchProof2752

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace BranchGraph

variable {V : Type*} [DecidableEq V]

def containsEdge (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∃ a ∈ I,∃ b ∈ I,G.Adj a b

omit [DecidableEq V] in
lemma singleton_no_edge (G : SimpleGraph V) (w : V) : ¬ containsEdge G {w}:=by
  rintro ⟨a,ha,b,hb,hab⟩
  rw [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl w hab

lemma pair_contains_edge (G : SimpleGraph V) (u w : V) : containsEdge G {u,w}↔G.Adj u w:=by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u,by simp,w,by simp,h⟩

def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S,∀ b ∈ S,¬ G.Adj a b

section FiniteGraph

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def neighborsAfter (removed : Finset V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v∧v ∉ removed)

lemma neighborsAfter_subset {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u:=by
  intro v membership
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at membership ⊢
  exact ⟨membership.1,fun vIn => membership.2 (h vIn)⟩

lemma neighbor_equality_survives {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u = neighborsAfter G A w) :
    neighborsAfter G B u = neighborsAfter G B w:=by
  have e (v : V) : neighborsAfter G B v = (neighborsAfter G A v).filter (· ∉ B):=by
    ext z
    simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun hz => ⟨⟨hz.1,fun zIn => hz.2 (h zIn)⟩,hz.2⟩,fun hz => ⟨hz.1.1,hz.2⟩⟩
  rw [e u,e w,same]

def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group,∀ w ∈ group,(neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty → neighborsAfter G removed u = neighborsAfter G removed w

def isolates (removed : Finset V) : Finset V :=
  Finset.univ.filter (fun v => neighborsAfter G removed v = ∅)

def maximalClass (removed : Finset V) (root : V) : Finset V :=
  if root ∉ removed∧(neighborsAfter G removed root).Nonempty then
    Finset.univ.filter (fun v => v ∉ removed∧neighborsAfter G removed v = neighborsAfter G removed root)
  else ∅

def closeIsolates (removed : Finset V) : Finset V:=removed ∪ isolates G removed

def removeClass (removed : Finset V) (root : V) : Finset V :=
  closeIsolates G (removed ∪ maximalClass G removed root)

lemma subset_removeClass (removed : Finset V) (root : V) : removed ⊆ removeClass G removed root:=by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)

lemma isolate_mem_removeClass {removed : Finset V} (root u : V)
    (h : ¬ (neighborsAfter G removed u).Nonempty) : u ∈ removeClass G removed root:=by
  have hn : ¬ (neighborsAfter G (removed ∪ maximalClass G removed root) u).Nonempty:=by
    intro existsNeighbor
    exact h (existsNeighbor.mono (neighborsAfter_subset G Finset.subset_union_left u))
  have hu : u ∈ isolates G (removed ∪ maximalClass G removed root):=by
    simp [isolates,Finset.not_nonempty_iff_eq_empty.mp hn]
  exact Finset.mem_union_right _ hu

theorem dominates_step [Nonempty V] {A B Q : Finset V} (smaller : A ⊆ B)
    (twins : TwinGroup G A Q) : ∃ root : V,A ∪ Q ⊆ removeClass G B root:=by
  classical
  by_cases someActive : ∃ root ∈ Q,root ∉ B∧(neighborsAfter G B root).Nonempty
  · obtain ⟨root,rootQ,rootOut,rootLive⟩:=someActive
    refine ⟨root,?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    by_cases live : (neighborsAfter G B u).Nonempty
    · have oldU:=live.mono (neighborsAfter_subset G smaller u)
      have oldRoot:=rootLive.mono (neighborsAfter_subset G smaller root)
      have same:=neighbor_equality_survives G smaller (twins u hu root rootQ oldU oldRoot)
      have covered : u ∈ maximalClass G B root:=by simp [maximalClass,rootOut,rootLive,uIn,same]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ covered)
    · exact isolate_mem_removeClass G root u live
  · let root : V:=Classical.choice inferInstance
    refine ⟨root,?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    exact isolate_mem_removeClass G root u (fun live => someActive ⟨u,hu,uIn,live⟩)

lemma retained_after_close {removed : Finset V} {u : V} (out : u ∉ closeIsolates G removed) :
    (neighborsAfter G (closeIsolates G removed) u).Nonempty:=by
  have uOut : u ∉ removed:=fun h => out (Finset.mem_union_left _ h)
  have old : (neighborsAfter G removed u).Nonempty:=by
    by_contra empty
    apply out
    apply Finset.mem_union_right
    simp [isolates,Finset.not_nonempty_iff_eq_empty.mp empty]
  obtain ⟨v,hv⟩:=old
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  refine ⟨v,?_⟩
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
  refine ⟨hv.1,fun dropped => ?_⟩
  rcases Finset.mem_union.mp dropped with h | h
  · exact hv.2 h
  · have witness : u ∈ neighborsAfter G removed v:=by
      simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hv.1.symm,uOut⟩
    have none : neighborsAfter G removed v = ∅:=by simpa [isolates] using h
    rw [none] at witness
    exact Finset.notMem_empty _ witness

def TwinSteps : Finset V → List (Finset V) → Prop
  | _,[] => True
  | removed,group :: rest => TwinGroup G removed group∧TwinSteps (removed ∪ group) rest

def removedThrough : Finset V → List (Finset V) → Finset V
  | removed,[] => removed
  | removed,group :: rest => removedThrough (removed ∪ group) rest

def ClassSteps : ℕ → Finset V → Finset V → Prop
  | 0,start,finish => finish = start
  | k + 1,start,finish => ∃ root : V,ClassSteps k (removeClass G start root) finish

theorem dominates_steps [Nonempty V] {A B : Finset V} (groups : List (Finset V))
    (smaller : A ⊆ B) (steps : TwinSteps G A groups) :
    ∃ finish : Finset V,ClassSteps G groups.length B finish∧removedThrough A groups ⊆ finish:=by
  induction groups generalizing A B with
  | nil => exact ⟨B,rfl,smaller⟩
  | cons group rest ih =>
    obtain ⟨twins,next⟩:=steps
    obtain ⟨root,subset⟩:=dominates_step G smaller twins
    obtain ⟨finish,walk,covered⟩:=ih subset next
    exact ⟨finish,⟨root,walk⟩,covered⟩

def EdgelessAfter (removed : Finset V) : Prop :=
  ∀ u v,u ∉ removed → v ∉ removed → ¬ G.Adj u v

omit [Fintype V] [DecidableRel G.Adj] in
lemma edgeless_mono {A B : Finset V} (subset : A ⊆ B) (noEdges : EdgelessAfter G A) :
    EdgelessAfter G B:=by
  intro u v uOut vOut
  exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))

lemma closed_edgeless_all {D : Finset V} (noEdges : EdgelessAfter G (closeIsolates G D)) :
    closeIsolates G D = Finset.univ:=by
  ext u
  simp only [Finset.mem_univ,iff_true]
  by_contra out
  obtain ⟨v,hv⟩:=retained_after_close G out
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  exact noEdges u v out hv.2 hv.1

lemma classSteps_finish_closed {k : ℕ} {start finish : Finset V} (walk : ClassSteps G k start finish)
    (closed : ∃ D : Finset V,start = closeIsolates G D) : ∃ D : Finset V,finish = closeIsolates G D:=by
  induction k generalizing start with
  | zero =>
    change finish = start at walk
    rw [walk]
    exact closed
  | succ k ih =>
    obtain ⟨root,after⟩:=walk
    exact ih after ⟨_,rfl⟩

theorem covering_sequence_reaches_univ [Nonempty V] (groups : List (Finset V))
    (twins : TwinSteps G ∅ groups) (finished : EdgelessAfter G (removedThrough ∅ groups)) :
    ClassSteps G groups.length (closeIsolates G ∅) Finset.univ:=by
  obtain ⟨D,steps,subset⟩:=dominates_steps G groups (Finset.empty_subset (closeIsolates G ∅)) twins
  have noEdges:=edgeless_mono G subset finished
  obtain ⟨A,hD⟩:=classSteps_finish_closed G steps ⟨∅,rfl⟩
  rw [hD] at noEdges
  rwa [hD,closed_edgeless_all G noEdges] at steps

end FiniteGraph

end BranchGraph

namespace BranchGroupsLean

open BranchGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat}

def bucket (label : V → Fin m) (r : Fin m) : Finset V:=Finset.univ.filter (fun v => label v = r)

def below (label : V → Fin m) (r : Fin m) : Finset V:=Finset.univ.filter (fun v => label v < r)

def coveredBy (label : V → Fin m) (done : List (Fin m)) : Finset V :=
  Finset.univ.filter (fun v => label v ∈ done)

omit [DecidableEq V] in
@[local simp] lemma coveredBy_nil (label : V → Fin m) : coveredBy label [] = ∅:=by
  ext v
  simp [coveredBy]

lemma coveredBy_append_singleton (label : V → Fin m) (done : List (Fin m)) (r : Fin m) :
    coveredBy label (done ++ [r]) = coveredBy label done ∪ bucket label r:=by
  ext v
  simp [coveredBy,bucket,List.mem_append]

omit [DecidableEq V] in
lemma covered_before_of_sorted (label : V → Fin m) (out : Fin m) (done rest : List (Fin m)) (r : Fin m)
    (sorted : (done ++ r :: rest).Pairwise (· < ·))
    (roots : ∀ v : V,label v = out∨label v ∈ done ++ r :: rest)
    (beforeOut : r < out) : coveredBy label done = below label r:=by
  have facts:=List.pairwise_append.mp sorted
  ext v
  simp only [coveredBy,below,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro member
    exact facts.2.2 _ member r (by simp)
  · intro earlier
    rcases roots v with isOut | member
    · rw [isOut] at earlier
      exact (lt_asymm earlier beforeOut).elim
    rcases List.mem_append.mp member with doneMember | coming
    · exact doneMember
    rcases List.mem_cons.mp coming with atRoot | later
    · exact (ne_of_lt earlier atRoot).elim
    have after:=(List.pairwise_cons.mp facts.2.1).1 _ later
    exact (lt_asymm earlier after).elim

section Graph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sorted_tail_twin_steps (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (sorted : roots.Pairwise (· < ·)) (allRoots : ∀ v : V,label v = out∨label v ∈ roots)
    (beforeOut : ∀ r ∈ roots,r < out)
    (twinAt : ∀ r ∈ roots,TwinGroup G (below label r) (bucket label r))
    (done pending : List (Fin m)) (complete : done ++ pending = roots) :
    TwinSteps G (coveredBy label done) (pending.map (bucket label)):=by
  induction pending generalizing done with
  | nil => exact True.intro
  | cons r tail ih =>
    have rMember : r ∈ roots:=complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
    have prev:=covered_before_of_sorted label out done tail r (by simpa only [complete] using sorted)
      (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
    have next:=ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
    refine ⟨?_,?_⟩
    · rw [prev]
      exact twinAt r rMember
    · rwa [coveredBy_append_singleton] at next

lemma removedThrough_coveredBy (label : V → Fin m) (done pending : List (Fin m)) :
    removedThrough (coveredBy label done) (pending.map (bucket label)) = coveredBy label (done ++ pending):=by
  induction pending generalizing done with
  | nil => simp [removedThrough]
  | cons r tail ih =>
    change removedThrough (coveredBy label done ∪ bucket label r) (tail.map (bucket label)) = _
    rw [← coveredBy_append_singleton,ih]
    simp [List.append_assoc]

omit [DecidableRel G.Adj] in
lemma no_edges_after_branches (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (allRoots : ∀ v : V,label v = out∨label v ∈ roots)
    (outputIndependent : Independent G (bucket label out)) :
    EdgelessAfter G (removedThrough ∅ (roots.map (bucket label))):=by
  rw [← coveredBy_nil label,removedThrough_coveredBy,List.nil_append]
  intro u v uNot vNot
  have hu : label u = out:=(allRoots u).resolve_right (by simpa [coveredBy] using uNot)
  have hv : label v = out:=(allRoots v).resolve_right (by simpa [coveredBy] using vNot)
  exact outputIndependent u (by simp [bucket,hu]) v (by simp [bucket,hv])

theorem roots_required (label : V → Fin m) (out : Fin m) (branches : Finset (Fin m)) (k : Nat)
    (allRoots : ∀ v : V,label v = out∨label v ∈ branches)
    (beforeOut : ∀ r ∈ branches,r < out)
    (twinAt : ∀ r ∈ branches,TwinGroup G (below label r) (bucket label r))
    (outputIndependent : Independent G (bucket label out))
    (required : ∀ groups : List (Finset V),TwinSteps G ∅ groups →
      EdgelessAfter G (removedThrough ∅ groups) → k ≤ groups.length) : k ≤ branches.card:=by
  let roots:=branches.sort
  have sorted : roots.Pairwise (· < ·):=List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v = out∨label v ∈ roots:=by simpa [roots] using allRoots v
  have early (r) (member : r ∈ roots) : r < out:=beforeOut r (by simpa [roots] using member)
  have twins (r) (member : r ∈ roots) : TwinGroup G (below label r) (bucket label r) :=
    twinAt r (by simpa [roots] using member)
  have valid : TwinSteps G ∅ (roots.map (bucket label)):=by
    simpa using sorted_tail_twin_steps G label out roots sorted covers early twins [] roots rfl
  have last:=no_edges_after_branches G label out roots covers outputIndependent
  simpa [roots] using required (roots.map (bucket label)) valid last

end Graph

end BranchGroupsLean

namespace CircuitProof

export CircuitHelpers (CleanGate CleanL getD_ofFn getD_wiresFrom length_wiresFrom vl vl_congr vl_gate vl_input wiresFrom wiresFrom_append)

def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false

end CircuitProof

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds

open CircuitProof

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b∧a≠cut∧b≠cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b,edge a b → rank a < rank b)
    (localStep : ∀ b,¬ input b → x b≠y b → ∃ a,edge a b∧x a≠y a)
    (sameCut : x cut = y cut) {out : W} (different : x out≠y out) :
    ∃ a,input a∧x a≠y a∧Relation.ReflTransGen (avoid edge cut) a out:=by
  classical
  have track : ∀ k b,rank b = k → x b≠y b →
      ∃ a,input a∧x a≠y a∧Relation.ReflTransGen (avoid edge cut) a b:=by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b,hInput,diff,Relation.ReflTransGen.refl⟩
      · obtain ⟨p,hp,dp⟩:=localStep b hInput diff
        have earlier : rank p < k:=(order p b hp).trans_eq hb
        obtain ⟨a,ha,da,path⟩:=ih (rank p) earlier p rfl dp
        have pOff : p≠cut:=by rintro rfl; exact dp sameCut
        have bOff : b≠cut:=by rintro rfl; exact diff sameCut
        exact ⟨a,ha,da,path.tail ⟨hp,pOff,bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b,edge a b → rank a < rank b)
    (localStep : ∀ b,¬ input b → x b≠y b → ∃ a,edge a b∧x a≠y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a,input a → x a≠y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out:=by
  by_contra different
  obtain ⟨a,ha,da,reaches⟩:=difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y,w x = w y → f x = f y) :
    ∃ outer : Bool → Bool,∀ x,outer (w x) = f x:=by
  classical
  let outer (b : Bool):=if hb : ∃ a,w a = b then f (Classical.choose hb) else false
  refine ⟨outer,fun x => ?_⟩
  have hx : ∃ a,w a = w x:=⟨x,rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate),gs[p]? = some g∧b.val = n + p∧a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val:=by
  obtain ⟨p,g,hpg,hb,ha⟩:=edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val≠vl gs y b.val) :
    ∃ a : Fin (n + gs.length),readEdge gs a b∧vl gs x a.val≠vl gs y a.val:=by
  let p:=b.val - n
  have hb : b.val = n + p:=by dsimp [p]; omega
  have hp : p < gs.length:=by have:=b.isLt; omega
  let g:=gs[p]
  have hpg : gs[p]? = some g:=List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs,vl gs x a≠vl gs y a:=by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a,ha,da⟩)
  obtain ⟨a,ha,da⟩:=differingRead
  have ha':=(hcl p g hpg).lt a ha
  refine ⟨⟨a,by have:=b.isLt; omega⟩,⟨p,g,hpg,hb,ha⟩,da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n,x i≠y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val:=by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n:=⟨a.val,ha⟩
    have sameWire : inputWire gs i = a:=Fin.ext rfl
    have di : x i≠y i:=by
      rw [vl_input gs x a.val ha,vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool,∀ x : Fin n → Bool,(∀ i,¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val:=by
  let Fiber:={x : Fin n → Bool // ∀ i,¬ group i → x i = base i}
  obtain ⟨outer,ho⟩:=unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer,fun x agrees => ho ⟨x,agrees⟩⟩

end PetersenCutTrace

namespace CircuitProof.Readers

export CircuitHelpers.Readers (Dep Least Reads dep_nc reads_lt vl_beyond)

end CircuitProof.Readers

namespace CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

open CircuitProof.Readers

theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x≠f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and∨g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a,b]) : a≠b:=by
  rintro rfl
  have hcl:=L.hcl p g hg
  have hlt : a < m + p:=by
    rcases hcl with ⟨h1,j,_,h2⟩ | ⟨h1,j,k,hj,hk,h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg,hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]

end CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitProof CircuitProof.Readers

open CircuitProof.RunAsm

theorem least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w≠out) :
    ∃ p,Reads gs p w:=by
  by_cases isInput : w < n
  · let v : Fin n:=⟨w,isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p:=w - n
    have wire : w = n + p:=by dsimp [p]; omega
    have pLt : p < gs.length:=by omega
    have notOut : out≠n + p:=by omega
    obtain ⟨q,_,read⟩:=least.live nonconstant p pLt notOut
    exact ⟨q,wire.symm ▸ read⟩

theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y,f x≠f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup:=by
  obtain ⟨slot,atSlot⟩:=List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [args]
  · have distinct:=pq2f_nodup least nonconstant atSlot ops args
    simp [args,distinct]

theorem least_wire_readers_in_range {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val≠out) :
    ∃ (p : Nat) (g : Gate),gs[p]? = some g∧w.val ∈ g.inputs∧n + p < n + gs.length:=by
  obtain ⟨p,g,hit,reads⟩:=least_wire_used least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound:=(List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p,g,hit,reads,by omega⟩

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds

open CircuitProof CircuitProof.Readers

def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot:=b.val - n
    have hs : slot < gs.length:=by have:=b.isLt; omega
    let g:=gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val,by
      have atSlot : gs[slot]? = some g:=List.getElem?_eq_getElem hs
      have before:=(clean slot g atSlot).lt a.val a.property
      omega⟩
  else []

theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have:=b.isLt; omega)).inputs:=by
  simp [predecessors,internal,List.map_map,Function.comp_def]

theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = []:=by
  simp [predecessors,show ¬ n ≤ b.val by omega]

theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs:=by
  have isGate : n ≤ b.val:=by omega
  have which : b.val - n = p:=by omega
  have located:=(List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which,located] using predecessors_values clean b isGate

theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b↔readEdge gs a b:=by
  by_cases internal : n ≤ b.val
  · let slot:=b.val - n
    have hs : slot < gs.length:=by have:=b.isLt; dsimp [slot]; omega
    let g:=gs[slot]'hs
    have wire : b.val = n + slot:=by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g:=List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot,g,atSlot,wire,?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a,mem,rfl⟩
    · rintro ⟨q,h,atQ,wireQ,inside⟩
      have same : q = slot:=by omega
      subst q
      have gateSame : h = g:=Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a',mem,equal⟩:=List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = []:=by simp [predecessors,internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot,g,_,wire,_⟩
      omega

theorem predecessors_nodup {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y) (b : Fin (n + gs.length)) :
    (predecessors least.hcl b).Nodup:=by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [predecessors_values least.hcl b internal]
    exact BranchProof2752.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have:=b.isLt; omega))
  · simp [predecessors,internal]

end PetersenCutTrace

namespace PetersenScratch

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p∨0 < occurrences j p

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)

def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a&&b else a||b

noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool:=by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q

noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit:=if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)

private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k,0 < occurrences k p → x k = y k) : p.eval x = p.eval y:=by
  induction p with
  | lit k s =>
    have e:=h k (by simp [occurrences])
    simp [DMFormula.eval,e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b:=by
  apply eval_agree
  intro k hk
  have ne : k≠i:=by rintro rfl; omega
  simp [pairInput,ne]

private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b':=by
  apply eval_agree
  intro k hk
  have ne : k≠j:=by rintro rfl; omega
  simp [pairInput,ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b,f false b≠f true b

private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b,Q false b = Q true b) : changes P:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp,hQ])⟩

private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b,P false b = P true b) : changes Q:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq,hP])⟩

private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false:=by
  have hi : occurrences i p = 0:=by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0:=by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b',binOp conj (P a b) c≠binOp conj (P a' b') c) :
    ∀ a b,binOp conj (P a b) c = P a b:=by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a:=by
  cases conj <;> cases a <;> cases b <;> rfl

private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p∨hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b,pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b,pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b:=by
  classical
  have pl : hasPair i j p → ∀ a b,pairValue i j base p a b = pairKernel i j p a b:=by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b,pairValue i j base q a b = pairKernel i j q a b:=by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b'):=by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine,hp,hq,pl hp,ql hq]
    · rw [constant_pair hq a b]
      have hn:=nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b,pl hp]
      simp [combine,hp,hq]
  · have hq:=present.resolve_left hp
    rw [constant_pair hp a b,bin_comm]
    have hn:=nonconst
    simp_rw [constant_pair hp,bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b,ql hq]
    simp [combine,hp]

private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b,pairValue i j base p a b = pairKernel i j p a b:=by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue,pairKernel,DMFormula.eval,pairInput,hki]
    · have hkj : k = j:=by
        by_contra h
        simp [hasPair,occurrences,hki,h] at present
      simp [pairValue,pairKernel,DMFormula.eval,pairInput,hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p∨hasPair i j q:=by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p∨hasPair i j q:=by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq

theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b,outerA (pairValue i j baseA p a b) = (a&&b))
    (hO : ∀ a b,outerO (pairValue i j baseO p a b) = (a||b)) : False:=by
  have depAi : changes (pairValue i j baseA p):=by
    refine ⟨true,fun h => ?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b:=by
    refine ⟨true,fun h => ?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p):=by
    refine ⟨false,fun h => ?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b:=by
    refine ⟨false,fun h => ?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have present : hasPair i j p:=by
    left
    by_contra! h
    obtain ⟨b,hb⟩:=depAi
    exact hb (absent_left (by omega) false true b)
  have stableA:=stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO:=stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false≠pairKernel i j p false true:=by
    intro e
    have f:=congrArg outerO e
    rw [hO,hO] at f
    cases f
  have zeros:=hA false false
  have other:=hA false true
  have one:=hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool:=by
  classical
  exact decide (∃ u v,G.Adj u v∧x u = true∧x v = true)

private theorem edgeValue_true {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true:=by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u,v,h,hu,hv⟩

private theorem edgeValue_false_pair {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w,x w = true → w = u∨w = v) :
    edgeValue G x = false:=by
  classical
  unfold edgeValue
  apply decide_eq_false
  rintro ⟨s,t,es,hs,ht⟩
  rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
  · exact G.irrefl es
  · exact h es
  · exact h es.symm
  · exact G.irrefl es

private theorem edge_pair_and {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (pairInput i j (fun _ => false) a b) = (a&&b):=by
  cases a <;> cases b
  · apply edgeValue_false_pair (u:=i) (v:=i) G.irrefl
    intro k hk
    simp [pairInput] at hk
  · apply edgeValue_false_pair (u:=j) (v:=j) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput,hki,hkj] at hk ⊢
  · apply edgeValue_false_pair (u:=i) (v:=i) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput,hki,hkj] at hk ⊢
    assumption
  · exact edgeValue_true h (by simp [pairInput]) (by simp [pairInput,h.ne.symm])

private theorem edge_pair_or {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i≠j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (pairInput i j (fun k => decide (k = u∨k = v)) a b) = (a||b):=by
  have hu : pairInput i j (fun k => decide (k = u∨k = v)) a b u = true:=by
    simp [pairInput,hiu.ne.symm,huj]
  have hv : pairInput i j (fun k => decide (k = u∨k = v)) a b v = true:=by
    simp [pairInput,hvi,hjv.ne.symm]
  cases a <;> cases b
  · apply edgeValue_false_pair huv
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput,hki,hkj] at hk
    exact hk
  · exact edgeValue_true hjv (by simp [pairInput,hij.symm]) hv
  · exact edgeValue_true hiu (by simp [pairInput]) hu
  · exact edgeValue_true hiu (by simp [pairInput]) hu

theorem adjacent_cut_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (factors : ∀ base : Fin n → Bool,∃ outer : Bool → Bool,∀ a b,
      outer (pairValue i j base p a b) = edgeValue G (pairInput i j base a b)) : False:=by
  obtain ⟨outerA,ha⟩:=factors (fun _ => false)
  obtain ⟨outerO,ho⟩:=factors (fun k => decide (k = u∨k = v))
  exact fixed_pair_invariant i j p hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (edge_pair_and hij a b))
    (fun a b => (ho a b).trans (edge_pair_or hij.ne hiu hjv huj hvi huv a b))

end PetersenScratch

namespace PetersenCutFormula

open PEqualNP.CircuitLowerBounds

open PEqualNP.MetaComplexity

open CircuitProof

open PetersenScratch

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x):=by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula,DMFormula.eval,e]
  | and a b iha ihb =>
    simp only [negFormula,DMFormula.eval,iha,ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula,DMFormula.eval,iha,ihb]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p:=by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula,occurrences,iha,ihb]
  | or a b iha ihb => simp [negFormula,occurrences,iha,ihb]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w,hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op,g.inputs with
      | .not,[a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _,_ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true:=by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n = p:=by omega
  conv_lhs => rw [wireFormula]
  simp [hn,hp,hg,op,inputs,ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a,b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n = p:=by omega
  conv_lhs => rw [wireFormula]
  simp [hn,hp,hg,op,inputs,ha,hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a,b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n = p:=by omega
  conv_lhs => rw [wireFormula]
  simp [hn,hp,hg,op,inputs,ha,hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w,hi⟩,vl_input gs x w hi]
      rfl
    · obtain ⟨p,rfl⟩ : ∃ p,w = n + p:=⟨w - n,by omega⟩
      have hp : p < gs.length:=by omega
      let g:=gs[p]
      have hg : gs[p]? = some g:=List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha,negFormula_eval,ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),vl_gate gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),vl_gate gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0:=by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum:=by
  rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha,inputs,negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb,inputs,occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb,inputs,occurrences]

theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum:=by
  rw [hb,wireFormula_count_gate fallback hcl chosen hg,← parentsVal,List.map_map]
  rfl

end PetersenCutFormula

namespace PetersenCutIndependent

open PEqualNP.CircuitLowerBounds

open CircuitProof

open PetersenCutFormula PetersenCutTrace PetersenScratch

theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0:=by
  let i : Fin n:=⟨a.val,ha⟩
  have e : i = chosen↔a = inputWire gs chosen:=by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input,e]

theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out∨∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool,∀ x : Fin n → Bool,(∀ i,¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val:=by
  rcases controlled with rfl | blocked
  · exact ⟨id,fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

theorem adjacent_cut_excluded {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x,vl gs x out.val = edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v)
    (hi : occurrences i (wireFormula i gs cut.val) ≤ 1)
    (hj : occurrences j (wireFormula i gs cut.val) ≤ 1)
    (controlled : cut = out∨∀ k : Fin n,(k = i∨k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out) : False:=by
  refine adjacent_cut_invariant G i j u v hij hiu hjv huj hvi huv
    (wireFormula i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f,hf⟩:=cut_factors hcl cut out (fun k => k = i∨k = j) base controlled
  refine ⟨f,fun a b => ?_⟩
  have agree : ∀ k,¬ (k = i∨k = j) → pairInput i j base a b k = base k:=by
    intro k hk
    simp [pairInput,show k≠i from fun e => hk (Or.inl e),
      show k≠j from fun e => hk (Or.inr e)]
  unfold pairValue
  rw [wireFormula_eval i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)

end PetersenCutIndependent

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop:=∃ a b,reads v a∧reads v b∧a≠b

def Terminal (v : Fin m) : Prop:=v = output∨Branches reads v

def Follow (v w : Fin m) : Prop:=reads v w∧¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b:=by
  by_contra separate
  exact first.2 (Or.inr ⟨a,b,first.1,next.1,separate⟩)

variable (forward : ∀ {v w : Fin m},reads v w → v < w)

variable (live : ∀ v : Fin m,v≠output → ∃ w,reads v w)

include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m,Terminal reads output root∧ReflTransGen (Follow reads output) v root:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v,terminal,ReflTransGen.refl⟩
    obtain ⟨next,edge⟩:=live v (fun e => terminal (Or.inl e))
    have increase:=forward edge
    have closer : distance next < distance v:=by
      dsimp [distance]
      have bounds:=next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root,stopped,route⟩:=ih next closer
    exact ⟨root,stopped,route.head ⟨edge,terminal⟩⟩

include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next,edge,tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_,edgeB,_⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB,edgeB,tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal:=follow_unique reads output edge edgeB
      subst nextB
      have increase:=forward edge.1
      have closer : distance next < distance v:=by
        dsimp [distance]
        have bounds:=next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB

noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)

theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w:=by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w∧first reads output forward live w = first reads output forward live v:=by
  induction route with
  | refl => exact ⟨ReflTransGen.refl,rfl⟩
  | tail _ edge ih =>
    have predecessorBefore:=lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked,label⟩:=ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _:=⟨edge,fun stopped => by
      have self:=first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step,(first_of_follows reads output forward live step).symm.trans label⟩

theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w:=by
  by_contra tooLate
  have earlier:=lt_of_not_ge tooLate
  have same:=(read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b:=by
  have earlier:=lt_of_lt_of_le (forward edge) bound
  have same:=(read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge,fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop:=reads v w∧v≠cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v:=by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label:=(read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier:=lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _:=⟨edge.1,fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same:=(first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b:=by
  let distance (w : Fin m):=m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA,stepA,laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next,stepB,later⟩
      · exact bHere
      have equal : next = goal:=follow_unique reads output stepB edgeA
      subst next
      have increasing:=path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB,stepB,laterB⟩
      · subst b
        have equal : nextA = goal:=follow_unique reads output stepA edgeB
        subst nextA
        have increasing:=path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal:=follow_unique reads output stepA stepB
      subst nextB
      have increase:=forward stepA.1
      have closer : distance nextA < distance source:=by
        dsimp [distance]
        have bounds:=nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b:=by
  have aBound:=le_trans (le_of_lt (forward edgeA)) bound
  have bBound:=le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs,0 < weight a:=by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a,by simp,h⟩
    have hr : 0 < (rest.map weight).sum:=by
      simp only [List.map_cons,List.sum_cons] at positive
      omega
    obtain ⟨b,hb,hbPos⟩:=ih hr
    exact ⟨b,by simp [hb],hbPos⟩

lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs,weight a ≤ 1)
    (unique : ∀ a ∈ xs,∀ b ∈ xs,0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1:=by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons,List.sum_cons]
    by_cases h : weight a = 0
    · rw [h,Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0:=by
      by_contra some
      obtain ⟨b,hb,hbPos⟩:=witness_of_positive_sum weight rest (by omega)
      have equal:=unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero,Nat.add_zero]
    exact small a (by simp)

section Count

variable (parents : Fin m → List (Fin m))

variable (reads_parent : ∀ a b : Fin m,reads a b↔a ∈ parents b)

variable (weight : Fin m → Nat) (source : Fin m)

variable (other_weight : ∀ v : Fin m,v≠source → weight v = ((parents v).map weight).sum)

include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v:=by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a,member,hp⟩:=witness_of_positive_sum weight (parents v) positive
    have edge:=(reads_parent a v).mpr member
    have earlier:=forward edge
    exact (ih a earlier hp).tail edge

include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v,(parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1:=by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier:=forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)

end Count

end FirstBranchRoute

namespace PetersenFirstGroup

open PEqualNP.CircuitLowerBounds

open CircuitProof

open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch

noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)

noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut

theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut↔firstInputBoundary clean out live i = cut:=by
  simp [firstInputGroup]

theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out:=by
  let last : Fin (n + gs.length):=⟨n + gs.length - 1,by have:=out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last:=by
    change v.val ≤ n + gs.length - 1
    have:=v.isLt
    omega
  have lastOut : last = out:=by
    by_contra notOutput
    obtain ⟨v,e⟩:=live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w

theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (distinct : ∀ w,(predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1:=by
  let weight (a : Fin (n + gs.length)):=occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n:=chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1:=by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary,ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length),w≠inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum:=by
    intro w other
    by_cases primary : w.val < n
    · simp [weight,wireFormula_count_input_fin fallback chosen w primary,other,
        predecessors_nil_input clean w primary]
    · let p:=w.val - n
      have hp : p < gs.length:=by have:=w.isLt; dsimp [p]; omega
      have hw : w.val = n + p:=by dsimp [p]; omega
      let g:=gs[p]
      have atSlot : gs[p]? = some g:=List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl

theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out∨∀ k : Fin n,k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out:=by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out:=lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere:=(mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out:=by rwa [firstHere]
  have blocked:=FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1,e.2.1⟩) _ _ path

theorem firstInputGroup_independent {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (distinct : ∀ w,(predecessors clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x,vl gs x out.val = edgeValue G x)
    (witnesses : ∀ i j,G.Adj i j → ∃ u v,
      G.Adj i u∧G.Adj j v∧u≠j∧v≠i∧¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut):=by
  intro i iIn j jIn adjacent
  obtain ⟨u,v,hiu,hjv,huj,hvi,huv⟩:=witnesses i j adjacent
  have iFirst:=(mem_firstInputGroup clean out live cut i).mp iIn
  have jFirst:=(mem_firstInputGroup clean out live cut j).mp jIn
  have iCount:=firstInputBoundary_occurrences_le_one clean out live distinct i i
  have jCount:=firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [iFirst] at iCount
  rw [jFirst] at jCount
  refine adjacent_cut_excluded clean G cut out computes i j u v adjacent hiu hjv huj hvi
    huv iCount jCount ?_
  rcases firstInputGroup_controlled clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))

end PetersenFirstGroup

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitProof CircuitProof.Readers

open scoped BigOperators

def operands (gs : List Gate) : List Nat:=gs.flatMap Gate.inputs

def notGateCount (gs : List Gate) : Nat:=(gs.filter fun g => isNotGate g.op).length

theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs:=by
  obtain ⟨g,gAt,before⟩:=read
  exact List.mem_flatMap.mpr ⟨g,List.mem_iff_getElem?.mpr ⟨slot,gAt⟩,before⟩

theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p≠q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire:=by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g,atGate,_⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands,List.flatMap_cons,List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using first
        have later : Reads rest q wire:=by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire:=List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using second
        have later : Reads rest p wire:=by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire:=List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire:=by simpa [Reads] using first
        have late : Reads rest q wire:=by simpa [Reads] using second
        have different : p≠q:=fun eq => neq (congrArg Nat.succ eq)
        have count:=ih different early late
        simp only [operands] at count
        omega

theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length:=by
  induction gs with
  | nil => simp [operands,notGateCount]
  | cons g gs ih =>
    have gArity:=arity g (by simp)
    have rest:=ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands,notGateCount,h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands,notGateCount,h] at rest ⊢
      omega

theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0) = 2:=by
  intro g gMem
  obtain ⟨p,atGate⟩:=List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [op,args,isNotGate]
  · rcases ops with op | op <;> simp [op,args,isNotGate]

theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches,2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length:=by
  classical
  let W:=(operands gs).toFinset
  have subset : branches ⊆ W:=by
    intro w wm
    have t:=twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W,if w ∈ branches then (1 : Nat) else 0) = branches.card:=by
    have same : (∑ w ∈ W,if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches,if w ∈ branches then (1 : Nat) else 0:=by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W,(operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W,((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W,(operands gs).count w:=by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w:=List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib,aux,total] at bound
  simpa [W] using bound

theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length,w≠out → ∃ p,Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches,∃ p q,p≠q∧Reads gs p w∧Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length:=by
  let W:=(operands gs).toFinset
  let required:=(Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W:=by
    intro w inSet
    have spec:=Finset.mem_erase.mp inSet
    obtain ⟨p,read⟩:=everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1:=by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid),Finset.card_range]
  have twice : ∀ w ∈ branches,2 ≤ (operands gs).count w:=by
    intro w mem
    obtain ⟨p,q,different,pReads,qReads⟩:=twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up:=branch_card_add_wire_card_le_operands gs branches twice
  have used:=Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total:=operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitProof CircuitProof.Readers

open PetersenCutTrace

theorem least_read_edge_live {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length),w≠(⟨out,outValid⟩ : Fin (n + gs.length)) → ∃ v,readEdge gs w v:=by
  intro w notOutput
  have notSame : w.val≠out:=fun eq => notOutput (Fin.ext eq)
  obtain ⟨p,g,atSlot,reads,bound⟩ :=
    least_wire_readers_in_range least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p,bound⟩,p,g,atSlot,rfl,reads⟩

theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q,p≠q∧Reads gs p w.val∧Reads gs q w.val:=by
  obtain ⟨first,next,pRead,qRead,separate⟩:=fork
  obtain ⟨p,g,atP,src,ap⟩:=pRead
  obtain ⟨q,h,atQ,dst,aq⟩:=qRead
  refine ⟨p,q,?_,⟨g,atP,ap⟩,⟨h,atQ,aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))

noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)):=by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w

theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs↔FirstBranchRoute.Branches (readEdge gs) w:=by
  classical
  simp [circuitBranchWires]

def classAt {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut

def classesBefore {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut

theorem class_mem {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ classAt label cut↔label v = cut:=by
  simp [classAt]

theorem classes_before_mem {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ classesBefore label cut↔label v < cut:=by
  simp [classesBefore]

theorem class_twins_of_later_factor {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → W) (cut : W)
    (independent : BranchGraph.Independent G (classAt label cut))
    (code : Finset V → Bool) (decode : Bool → Finset V → Prop)
    (factors : ∀ I O : Finset V,(∀ i ∈ I,label i = cut) →
      (∀ i ∈ O,cut < label i) → (BranchGraph.containsEdge G (I ∪ O)↔decode (code I) O)) :
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut):=by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ classAt label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ classesBefore label cut) : cut < label y:=by
    have ne : label y≠cut:=fun equal =>
      independent x xGroup y ((class_mem label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut:=fun h => notEarlier ((classes_before_mem label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ classAt label cut) (yLater : cut < label y) :
      (G.Adj x y↔decode (code {x}) {y}):=by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut:=by
      have eq : i = x:=Finset.mem_singleton.mp mem
      subst i
      exact (class_mem label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i:=by
      have eq : i = y:=Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ classAt label cut)
      (active : (BranchGraph.neighborsAfter G (classesBefore label cut) x).Nonempty) :
      code {x}≠code ∅:=by
    obtain ⟨y,neighbor⟩:=active
    simp only [BranchGraph.neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at neighbor
    have yLater:=later xGroup neighbor.1 neighbor.2
    have yes:=(single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one:=(factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a:=cannot u uGroup uActive
  have b:=cannot v vGroup vActive
  have sameCode : code {u} = code {v}:=by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨edge,remains⟩
    have pos:=later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_,remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge,remains⟩
    have pos:=later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_,remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds CircuitProof

open Relation

theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i,ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val:=by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n:=⟨w.val,input⟩
      have name : inputWire gs i = w:=Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w:=by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a:=agree i atInput
      simpa only [vl_input gs x w.val input,vl_input gs y w.val input] using a
    · let p:=w.val - n
      have pLt : p < gs.length:=by have:=w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p:=by dsimp [p]; omega
      let g:=gs[p]'pLt
      have atGate : gs[p]? = some g:=List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore:=(clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length):=⟨a,by have:=w.isLt; omega⟩
      have read : readEdge gs wire w:=⟨p,g,atGate,gateWire,inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)

end PetersenCutTrace

open PEqualNP.CircuitLowerBounds

open CircuitProof

open PetersenCutTrace Relation

def setInput {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool:=decide (i ∈ S)

theorem finite_branch_bit_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length),v≠out → ∃ w,readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool,∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I,label i = cut) → (∀ i ∈ O,cut < label i) →
        (vl gs (setInput (I ∪ O)) out.val = true↔decode (code I) O):=by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)):=vl gs (setInput I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n),(∀ j ∈ J,label j = cut)∧code J = b ∧
      vl gs (setInput (J ∪ O)) out.val = true
  refine ⟨code,decode,?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I,label i = cut) at groupI
  change (∀ i ∈ O,cut < label i) at afterO
  change (_↔decode (code I) O)
  constructor
  · exact fun yes => ⟨I,groupI,rfl,yes⟩
  · rintro ⟨J,groupJ,sameCode,yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (K ∪ O)) cut.val = code K:=by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O:=fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput,absent]
    have sameCut : vl gs (setInput (I ∪ O)) cut.val = vl gs (setInput (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out:=lt_of_le_of_ne prior atOutput
    have eq:=circuit_cut_agreement clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut:=by
        by_contra offGroup
        have notI : i ∉ I:=fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J:=fun mem => offGroup (groupJ i mem)
        exact diff (by simp [setInput,notI,notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
          (inputWire gs i) = cut:=isGroup
      have forbid:=FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
        (v:=inputWire gs i) (w:=out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b,avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
        fun _ _ h => ⟨h.1,h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]

open PEqualNP.CircuitLowerBounds CircuitProof

open PetersenCutTrace

theorem circuit_branch_class_twins {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length),v≠out → ∃ w,readEdge gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n),vl gs (setInput S) out.val = true↔BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (independent : BranchGraph.Independent G
      (classAt (fun i => FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)) cut)) :
    let label (i : Fin n):=FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut):=by
  let label (i : Fin n):=FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  obtain ⟨code,decode,factors⟩:=finite_branch_bit_factor clean out live cut prior terminal
  change BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut)
  exact class_twins_of_later_factor G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitProof CircuitProof.Readers

open PetersenCutTrace PetersenFirstGroup

end BranchProof2752

end

-- From pequalnp-proofs/lean/PEqualNP/Outside/L_meta_7402.lean
section

namespace CoreTable7402_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section

variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}

theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (save : Bool)
    (h : Run inv meet join y s (inv a :: kept save a r)) :
    Run inv meet join y (s + 1) (a :: r) := fun P d q u b => u save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h : Run inv meet join y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k ⟨h', ih⟩ => ⟨Run.one k h', one k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest save _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n a : ℕ) : BFn n :=
  fun x => CircuitHelpers.vl gs x a

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i :=
  funext fun x => CircuitHelpers.vl_input gs x i i.isLt

def SCleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

theorem SCleanGate.lt {m : ℕ} {g : Gate} (h : SCleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩ <;> rw [hin] <;> simp_all

def SCleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → SCleanGate (n + p) g

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x

abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x

abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (clean : CircuitHelpers.CleanL n gs)
    (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg (x : Fin n → Bool) :
        val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) :=
      CircuitHelpers.vl_gate gs clean x p g hg
    have hnd0 := nodup_liveList gs n o p
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hjm := hin j (by simp [hinp])
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hjm
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hjm h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have hval : val gs n (n + p) = invF (val gs n j) := by
        funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval, invF]
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one _ IH')
    · have hjm := hin j (by simp [hinp])
      have hkm := hin k (by simp [hinp])
      have hke : k ∈ (liveList gs n o p).erase j :=
        (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
      have hp1 : (liveList gs n o p).Perm
          (j :: k :: ((liveList gs n o p).erase j).erase k) :=
        (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
      have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
          a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
            (kept (decide (Live gs o (p + 1) k)) k
              (((liveList gs n o p).erase j).erase k))) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
          · rw [mem_kept, mem_kept]
            rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
            · exact hnew j hjm h.symm
            · exact hnew k hkm h.symm
            · exact hnew _ ((hmr _).1 h).2.2 rfl
          · rw [hmr]; simp
          · rw [mem_kept, hmr]
            rintro (⟨_, h⟩ | h)
            · exact hjk h
            · exact h.2.1 rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
              · by_cases hak : a = k
                · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨hkm, fun _ => h1⟩
            · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
          then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

open Classical in
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, least, bound⟩ := CircuitHelpers.Readers.exists_least n f s hnc h
  have hcl : SCleanL n gs := by
    intro p g atGate
    rcases least.hcl p g atGate with ⟨op, a, before, pins⟩ | ⟨op, a, b, aBefore, bBefore, pins⟩
    · exact Or.inl ⟨op, a, before, pins⟩
    · have distinct := BranchProof2752.least_gate_inputs_nodup least hnc g
        (List.mem_iff_getElem?.mpr ⟨p, atGate⟩)
      exact Or.inr ⟨op, a, b, aBefore, bBefore, by simpa [pins] using distinct, pins⟩
  have ho : o < n + gs.length := by
    by_contra! after
    obtain ⟨x, y, diff⟩ := least.ncv hnc
    exact diff ((CircuitHelpers.Readers.vl_beyond gs x o after).trans
      (CircuitHelpers.Readers.vl_beyond gs y o after).symm)
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_cases output : n + p = o
    · exact Or.inl output
    · obtain ⟨q, _, reads⟩ := least.live hnc p hp (Ne.symm output)
      exact Or.inr ⟨q, reads⟩
  refine ⟨gs.length, bound, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext least.hev
    rw [← hf]
    exact run_live n gs o hcl least.hcl ho hnd gs.length 0 (by omega)

abbrev fG : BFn 8 := fun x : Fin 8 → Bool =>
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
  (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hm]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hm]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

def lo (k : Nat) := 2 ^ k - 1

def mask (k : Nat) := lo (k + k)

def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k + i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega, show k + i < k + k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k + i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a ^^^ m
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((a ^^^ mask k) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) →
      next (mask k) (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s + 1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k + i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s + 1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil =>
    simp [sumBelow]
  | cons w ws ih =>
    rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]
    omega

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f (goal k))

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s + 1
    · simp [hl]
      by_contra hb
      have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hb)
      exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)) hsum
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (zs) (hz : NatRun (mask k) (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def rowsG : List ℕ := [1, 1, 1, 8, 8, 10, 12, 24, 28, 32, 32, 33, 33, 34, 34, 34, 34, 48, 49, 49, 49, 49, 49, 52, 52, 52, 52, 52, 97, 97, 97, 97, 97, 100, 100, 129, 129, 129, 129, 132, 132, 138, 138, 138, 138, 138, 156, 156, 2, 2, 2, 16, 16, 17, 20, 24, 28, 64, 64, 66, 66, 65, 65, 65, 65, 72, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 98, 98, 98, 98, 98, 100, 100, 130, 130, 130, 130, 132, 132, 145, 145, 145, 145, 145, 156, 156, 100, 3, 5, 9, 9, 40, 14, 44, 25, 60, 40, 160, 35, 37, 38, 42, 50, 162, 112, 51, 53, 57, 113, 177, 53, 54, 60, 116, 180, 99, 101, 105, 113, 225, 101, 108, 133, 137, 161, 193, 133, 164, 139, 142, 154, 170, 202, 157, 188, 3, 6, 18, 18, 80, 21, 84, 26, 92, 80, 192, 67, 70, 69, 81, 73, 193, 104, 75, 78, 90, 106, 202, 78, 77, 92, 108, 204, 99, 102, 114, 106, 226, 102, 116, 134, 146, 194, 162, 134, 196, 147, 149, 153, 209, 177, 158, 220, 228]

def xsG : List ℕ := [0x7c00220bd04285f7e1f8311e3e000001e0200079f07c1807, 0x85f7e1f8311e7c00220bd0420079f07c18073e000001e020, 0x38b1c5f1062c58b1c5f1062c5c1860f800140c1860f800140, 0x190011ffd0301fc28842087f8c0000ffe0180fe00000001f8, 0x1fc28842087f990011ffd0300fe00000001f8c0000ffe0180, 0x2408fe8440001224ffffffea10007f00000000007fffffe00, 0x3224ffffffea0408fe84400010007fffffe000007f0000000, 0x3fff210820801fff210820800fff800000000fff800000000]

theorem rowsG_len : rowsG.length = 194 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 97 := by decide +kernel

theorem maskG : mask 97 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; simp [mask, lo]

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 97 zs &&& lo 97) ≠ lo 97 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 97) (goal 97) s xsG) :
    ∀ s ≤ 11, ∀ zs : List ℕ, zs.Sublist xsG → NatRun (mask 97) (goal 97) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 11, ¬ NatRun (mask 97) (goal 97) s xsG) :
    ¬ HasCircuitSize 8 fG 11 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ 11 h
  have hr : NatRun (mask 97) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 8 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 6 => 2
  | 7 => 136
  | 8 => 1066
  | 9 => 888
  | 10 => 43
  | 11 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 6, 0 => 0xd7bbd8a061460435
  | 7, 0 => 0x47a7d3394729672145d2737945ae89994434299743ca838443013eeb41fd45b040d28957408452113eea036f3e704d023bfcf5033bdcbafd3b600024384fd81f367bbf1a344e10f133e5e89d31b9222a304b918e2fe1627c2e57dcc82e238cf12d16d84f2cbf5bfe2b8a21ea2b7a55442902737427fb547f2662881024cc7a16248442bd22ae0bc4227164af2200e0b221df1c122194e6b21fba22b21fada83d1f6ac73f1efe1c8e1eeee64b1d3883e01b2eec831b06c23919ede80a197839611865f39816c16c2316b8d9f413d4b3800dd51ef60dbd4a640d8718d10d5b3f980a6b202509af1d1a096eb93608993a9904b9d2b60208293301b533eb01b33159
  | 7, 1 => 0xcbd43192cae699b0bff43054bc021fc8ba1c6e8ab9bc9dceb8648d4fb33bcce3b27db793ae4a0340adea4fe8ac3d30baa8a5df83a72179c0a70507909ceac49a9917908a988f72f39418974a936a4a208fe147048d28c27c8c4f37f68c4b4c4d8bdd66d589b5b86a850d197680efef34807baac17c3ca6f9788a755c77a00c52778806ec76c336e37451973d73c703fd7162b1fb7138a7d5710b71b56f3c809d6b51b20d6ad77e0f692379d46806b0ed65d4264a64464bb5636a019b61a7eb235eb9a91a5d1242205bcec7655b2b173859c01a9259462d2658deacb656b4bd2e557ac47c548f1a964dfd980d4c5429c24ba996534aa7e1484a19059b49f70fb1
  | 7, 2 => 0xf9945f9ff91ce1abf44c6b88e5429b95e0831805d5d9be3ed54c003dcf0f7b14
  | 8, 0 => 0x803872a07fc258507f6327507a7acdf078f23af0785757a0761034407443a5c0739a6f90693b60c066ef574064d6eb2064c13cf061b917d05fe136a05d3fbe505c54f9705a5f717058ffc65057f93bf055b7aeb05432aab04e4123f04b94b2a04a0c6020487c166046fd21b046a0c600447896d0426c32703c976d403bb60f103a6a7a0038b502f03470857032f3b7d03293d19031e8f56031a9db10314a76a02bf8a8f02b5620f022f5b960226ba0b01f7e40501f1852b01e24547018423f4017e9f6c0168a1d70163f2e10139f1890133928e0130a5dc00d3389300c0b8c400ac72b4009e518d005bd54500426b500030b569002e140b00203ea40002a385
  | 8, 1 => 0x10961ce1108d06c410798d8f106538bf1052745a105158d610432407102ca4de101175240fdd6c200fdc3b2c0fd7cfc00fbbe7f50f1d566c0f04d9830eec68520eda331f0e8dcf4e0e7d9ab00e6f8b3d0e4dda130e1870d80df760220d983c920d7402380d63662a0d492d3c0cee5d4c0cd866780c90e5e20c7b9dfb0c7051510c47b2dc0c314d6d0c2fb2900c048ef70bffc0af0ba6595a0b974be20b94b9010b73acef0b62b5bd0b612a6f0b3513fc0b1a6ff60af2f98f0a7e850d0a2bc39f0a083fcc09b4285b09ac4e8309556b9b09448c8b08d1197d08cf9f6c08bad27c08b69f2d0891d271088fae420884e81208427702083b7685080f3c17080a9119
  | 8, 2 => 0x18aecc91189cfc581883bb091863cd9c1853765a17f8368b17ebd5cc17e25848171d9b41171ac20e1712498616e0369d16a325001680495016716eeb16626d481634b457162c1e0716232c6715da5a3d158f70ea15843c58156fd5c915527efe154c24db153772eb153408cc152365c1151be7b814fad83614e013ce14921d4614532fb11444127814344d50142ce73e14180a1614132ba513c565a513be99b9138d52f9138b867f133a4b0c1327c71a1327c58f130c76c212fc7a5412f14d3912df759712d3987b126cf29f124f27dc121a26c61206977f11e8ee2a117473a7115e7f4c115429141147516c1117b86610c188e810b1a23d10afb53b10a9cfa1
  | 8, 3 => 0x2320966322f90fbd22d3a50f22781dcc22670f87224f9ba922271afb220e43d822089cf521ebc87021bc56202189c09220f3cadd20ca8c7c208679fb2079771a20778d6b2047100b203ff3df2039c324203915dd1fada83d1f897b391f2fd5d71f0f88e61ef863d11eda12e81ed02cad1ecc2c531e9274621e5ab54a1e54b46b1e4f15671e4cb7371e4844331dea59ac1d7e64101d2569ad1d0d4d2b1ce2dfb61cb76de41c8075831c7acd771c6c70561c60107a1bee757b1b3cbf6a1b23ff3d1b0f5e281aeda2f51ac2ecdc1a9de2b51a7464991a4af73d1a49ad041a3df52d19d3e8c119bee37d198733631921c2c319211ccc18d3b05918c0dc2618be603b
  | 8, 4 => 0x2c74621b2c4233992bead7fd2bcbb4d32b8c06032b57ba6a2b287f572b1eaf0c2b0e5def2acfa4ea2a7c92552a7a746e2a24a50c2a1812fa29ff991629de935e29de54ff29ace2402986cf2829682212293873ec28fb3a8328dafbbf289ef797286c978c283fd8cb282d6759280cf761280131e827d8369327c7273b278d3c6b2777385427701841273b93a62738f1822728123b27234a4326a9c8a2268956de264b7503262d8ed6261868ee25a3032725993d482591eeda256df99a256c5b00254169c0253944512530d71224dbd67424d2632b24bf30dc24a8419624499b1e242e280123ef298823d1768f23b2ba3b233f7659233725a12331daa223304003
  | 8, 5 => 0x36d4db9936c7add236b7ce1a36afbf4936aeac8c36a4fe5736a0612335c250ee35a21f9835898b2f3572e96e35454b6c34bef98634af84fe344378ed34332f6d34244088341fe0af3415a66333fbbe6533f9a53233a5c97733a5b66e339bc9743375eaa7335b9f993321b26a32f51d1f3266ab86324ec45a3242d9c0310cd90a30be0d00308ede2f305a361330597a663032910e302e2b3e3023fe283011805f300df6fd30078cae2fe1627c2f14afb62f0a9d5a2ef6ce872ef58a1f2ed18c692ebed06f2ebdc5cd2e3c4ea92e26bdea2e1023ba2e08601d2dbaab5c2d73a28a2d427df92d33992e2cf492462ce2af292cca4f672c8cdde72c852ee12c7cb966
  | 8, 6 => 0x43bb39e043adce54439893cf4330fa0f42c3fc0442c1db304260dcf1425e13f4424a49dd4244dbc042059d2241c53cf5418fc3c1415a392741563b00414b01754104951a40b1e214402282493fd5a6e43fb44a283f700d9e3f5348373f31927a3f24ef3b3ee5c9443edbe3563eb150203ea623403e6385983e5a12643dcc00503db688b33d86a96c3d50fda23d3f604b3cb7c56f3c28b5113be9ae373b24f47b3b029d0e3ac686f93a8a3b173a7461763a65057a3a4b50f539e9fae539bac40539a2002d3977e037396abb9b38b0e0143848e7173806916f3804c6b937e3768737d6280a37b1f85b375c41e53744ad6637424834372a19f6372058b4371aa564
  | 8, 7 => 0x4d16d8054ce5f2ae4cc803044cc0e99e4cbb00cb4ca0ab664c9a47064c589a294c010f164be1ff764b4331094b24a8824ac08d6e4a9d92c64a8b171d4a5e45874a21b63a49e0732449bb560949b6430a495d7e0a49555f7749552a9e493d3c6e493503dc49317c814907221e48e7797f48b60f17489bba3c484e96ca484ab61a4816535b47d4ce6d47835679476ade6b474edf1d473168c146db9a9646ad812145edc48445de6bf345db672945ad2c0245a56960456343444556005b453165d4452b20274528e51d4527127e451c29ef450c9f9a44ff7a0844f9e31a4481cb30445e3ee7443d1ff7443bc9c14425814b440a0b8f43ed4b5f43de86f343d4c1bd
  | 8, 8 => 0x5a89fbf65a1eea31598ab90459682b80591f21f358fddddc58c2052858644deb5849b5405831c3e557f9f50c57db7705576c5455575efb7d57585eac573a5c6957357746570145a556a605d656841521565e5e535612281855e5e9e255d289055573bf945528bb2154fd096254d18cd554b652d05466889753f0fe7c53f09fee538ec76653741bab5317621b5306ccca52c4f121529e862e5282c13b525e04d052537b87523acdf052082589517d7ed8517a5e565178443e510addbc50df27e5502223fe5013a4814fda41374fd5a40e4fb8fd2b4f9e955f4f7ba7d34f666d1b4f1ddec24f1c8a8b4f003a024eff44464ee85a9c4daf27e74d5c0ccf4d3828c2
  | 8, 9 => 0x661de78c65aa320b659e2b3d659cc2aa65203e67650e920f64d9a5a364b99be764accf2564a8800a64a6ef226476ca5b644781cb63a9d3586369ed27636108c8635addab6344febd6343c965631b47426313087f62fc6a5662550db9624c0b506246cf0761cd10326194857d61728b4261361afe6120e83760e2423060c6c0f860ab6702608450e05f9f12965f6240485ee914a45eca7e455ec8e2d85ec83f085ea6e39a5e8fd0675e4bf2285e3438935e3247c65e05d2ee5ddda5225dc096b45d87e2335cda16045cae67f35c99e0fd5c888bf65c0f0ba05c03affb5ba5140b5b8c95e05b64e0955b374e1b5b1dc2055b16a2d65aa9bb605a8fe69c5a8a8f16
  | 8, 10 => 0x723bf64f71bf24507178450271147ad1710acc9c70d3384770c7c45a70c58ced70c496cc70b2b3756ff877d16fdfb4036fb3569c6e570b726e4a868e6e0e57fe6debed8a6ddaa9f96d5a374f6d5937876d351b5c6d34e3d26d1e05616d01333a6cea1df46cced3ba6cbf5c4e6cb4929f6c72de6c6c5ecf716c36daf16bff64316bf7cbc96bf5b5fc6bd993a56ba5d1186b7d616a6b0540676aeb513c6abf48ab6a23a8af69edd77769c9f6a6698284a96969f24d694c3ba76938c8fc68d1134b68c1fafa68b389d768ad6861688f02446880ee0368627f0e6818ad2867f0a3af67abb9266772ad20676a0ea4670f3bf066f93a6f66f4dba466c54a1b6655042a
  | 8, 11 => 0x7fc64a0a7f9963f47f5803477ed33ad27ebcca0d7ea239667e712b0f7db8d3867db8bb7a7da609917d17059b7cf2530c7cb499c57c5aa4827c158c207b95a57e7b7ce4167b2ea7657b0cc3527afbed1f7af321aa7aabadd57a210b1879d6aff879981cdd798f9f0178df1981788b53a67868935077f14e5677dd8092777fec8a776ee183775654c7771d93b4770c9dd57703ce8e76f5076a76dd9e25768a2d317682e2ce7666d60c764ae8e775ec960275c9e24f7585f9b87582f37275680320755a727e751cbad474cdf40574c1995873ff0bc173f8f1ba73f496fc73e961cb73e1a65973ab65bf737f3a627356780a72d6706e72b3b905726c5ded724998bf
  | 8, 12 => 0x8f1bf8a68f1564c78ef36a7f8eb975508eb3cd178eacf6b18e85903e8e40fd4b8d6f4c748d1470ae8babd4288b640ec88aea179a8aa5db108a11b0c889ff520289f114f089ef5af089d9b5d089ca094c898adc3e897f53f18946a5d6891a6ea88914dace8894e008885958bf87fa84108762737887581c068747c77c872d1f3086fffd9086b4914f86b26cca866bfa278635e88785c6968b859af43585958487854c6cb38497628d846a3d5184643f6883e8618783ba6ee5838d86c9837fc968836cf0638369758d832c888a8310875982e10fd882da9ad282d20da781e9934581b8c669818ae8ea817d8dad816c621480fc721f807a339f805269d57fe8072a
  | 8, 13 => 0x9d4496d09d147f879d0e5ee59d0bc4839c51fdcc9c43b2839c15e3ab9b6a3b679b2006b79af5424d9aea7af49ae4fb159ac83c069a9889fe99ff91f299e34f0299c25f4699a9554a99882bf899607daa98cfede6986bfee79856e38b9806080297dafcdf97b81ffe97679de69734464696f4430996a7cfe196946741965e2f56965516e496031c9395dd3e38955913439558f49b9546aa2095259e2a9513e0a194943eaa940b712593ebdc8993dc14fd93bdf225926c93fb92610d7b9232944d9224ba4b91ace296918e5e6c915d802c91400044913dcb4f90fcdc6290f7984990b70ea4905318ad8fc22d038fb798a28faf61ad8f56ffe88f45cd4d8f27c105
  | 8, 14 => 0xb634de58b6180ec3b6053d39b5c4e97fb59eb91cb526b0bfb4debc56b3e335d3b36f68a3b2e7bb02b28acfe9b269c9a7b1ff1e0fb1b348ecb1aea90db0e41a5bb0cd9c5bb0bcda11b0333a85b01352e5af80b798af6f350aaee6596baebe9aa1ae9694e9ae07d338ad8d2fffac4a52faab28a0e6aad2789eaacda55ea9e519fea95c4681a952ca9ca9137294a8e458c1a865405aa8376cdba81b5073a7c90cd5a7adb495a6d3d6b7a5ae0c33a3c70458a3c5cd88a3a76972a3356e4da32a12dea2b4d27ea219a6aea163bb5ea0858ab2a06abc1f9f902d0c9efdf35f9ec3285a9eb577869ea544b59e7995059e60cd6b9df24f649da997aa9d89b55a9d54f289
  | 8, 15 => 0xd34e2ae9d22cfc33d22198e0d1443d71cff29c34cf15b4a0ced8c286ce549c5bcc106b13cbbb073dcb2ac27fcaa65c2ac9e207bcc9907ee9c915ec54c8ed69fdc8e1545fc8aed920c8689dbdc8686bf6c7bba2cbc7a1e199c6d0ca08c658f39dc63ea630c6358765c61a8e21c58a0b59c51ba784c511ed02c433534bc3bd26d2c39e60c2c318d17fc303449ac2a1e7a1c29518e7c279657ec155c8cfc0c5c86dbffcd662bfd58626bf76ed22beca5543beba81a4bea1a541be690c53be587d93bd7f6631bd51203abd30d0b0bc90573abb1e938ebb164658ba7eb032ba623c03b8de3e6eb85c8807b85582b8b844e1dbb8441380b6f0cdb7b6b3f3f9b65252c4
  | 8, 16 => 0xfe5e8275f91ce1abf39de580f30c5812f2eebaf6ef290e1beec082e6ed97e502ebd6f8d0eb76d5bce9895b3ee8bea0bde7868f07e7439118e6c924f9e6504ce7e52dbea1e523acefe4b3fe87e458036ae29f9157e26ea595e25e6c08e0dbabe9df6e466cde921846de30a86ddd2829fadc11665cdbfdc193da14b500d9e45857d8dc35f0d7c1dc58d6281482d607e605d4b78822d4503c1ad40a3b2dd3ec807fd3e8b2b0d37866da
  | 9, 0 => 0xa68d57b0a63708d0a62070f0a4f61f30a45b6510a2bc39f09c48b2309ac4e8309aab3990990533009861745096c220009667e8b093adaf4093975c208dbded008d959ec08d145f2085f7c11085f1af108427702083a0e4007f76d7507ba0d8b06c1a428068b9e1506861840066ef574062cd7b206283a0105dbec8605d3fbe505b01f8f0581ed820562a02f05467db0050acfb804e3fae604dd95720447896d0418c79e03f6cce403e8408303c86f1d038cd54f0384754e036dccb502acdce302abbbf20273898a01edfe7101e36d8401c5685501ba9e6e01b0b07201affdd101a18ddf0139f189012544c100e4334200ca2805006270ed002d3783000d1794
  | 9, 1 => 0x164d5e4c1620b2e515c4ea5a15843c58156f5f5b1538f80b14fc95a914902def1473708f147088c21424060614132ba513f560fc138f904013880266137aa341136f7501135ae3a613379fb212d1677d128c3700128569d9123eaac9123387d1120700701206f58c12010e3e11eb06e211e8ee2a11cfabdc11ce17d61131d7c610e4974710d94d7c108b13c2106837021055907f104310920ff9cfc30fd53b420fc942d00fae56150f9747e50ec9fc0a0e45cd060e4052470e145eab0dd9f20c0dcaf7530d7492b10d4b360b0cd5f0420cbd25730cba4b300c75ac720c6a367b0c5698550c3701740c3320c10bd327d00b7449fb0b64a1660b5dfb150aa0b789
  | 9, 2 => 0x220e43d821baab8f215d8e272133c71b20d15e95204c44cc20376b8a20162b471ffb3d9c1f897b391f8614c81f800bb01f5298961f3caa981f2484fd1ed64a501e83b5ae1e666dec1e54b46b1e539fe81e4b1c4d1de27e731d42a18d1d148be11caff9911c821f5d1c7b0d4f1c6c70561c6b6a991bee757b1bd3b0f31ba423cb1ba2c35c1b70addf1b6af0a71adde7441aa3cfc81a817c0f1a74649919ceb8a619c3450518d30872189d1906187073d118672502186312e81841b7311837c0d118323afc1828350317cb6b9917b10185179c5e0b179a8079179443c8176ae071174614a3170b2c7f170730a516ed7b6a16d454d316c006da1665d1091655e228
  | 9, 3 => 0x2c516a392bcd39f32b8c06032b74bd872b36f0a02b336a702ad4e2702acfa4ea2a84ec4b2a4642fc2a3d1ed32a1ebf332a1d0b9629d6c10229d3219529b62735296822122935bfd6292c6fe5292a77cb292991ef290e933028c0bf14289ef797288cddd92870e47728689760282e792c280cf7612801253827f8f36427ccc5c7279f12e3279def0f27564a682725a8f326b2ee6526b25b90269b2b9d268cedbf26714829265d92182648ddbb26346d9e26205876261f934b25c277fc2556630d2543d29b24dbd674248a7edd23e3057c2382bd9b237bce98236e2c452357f7b3234efde12328b3b72319628c22ee739722d0acc322b0ca9c2229a281221caf80
  | 9, 4 => 0x377ea3ce3774c87d37711432373eb616370285c936f9e9ed36e356d936da947a36c0a3a2366e0c563654389e36422e9535f8335d35c59a2335a21f98358a20263529690c34dd880934af0e313489f5633455bf0f342074643415a663340cb27633ecbbe7339d06363385f066337b9cef3375eaa73366ce4b332725bb326ce2a831c7742231c276b7316dfc69315724003150b3a43150624530d40c9330826d0c307aca4a306088bd305be80430597a66302e34c0300a48592fe1627c2fd3e9d22f8ea12f2f4f2dce2f44c2b92ec67ce42e8981e82e6f215a2d8d16932d5731c72d3349352cbcc0312cadfa9d2c93178c2c88de9a2c84a89d2c743a862c6bd44d
  | 9, 5 => 0x4461f59c44433efb442bc1dc4410d0b143ae3b674384882243776f15431406e042fa44bf42af191d4286b8774260dcf14232e9a64230621642059d2241f0f05a41a9c4a241a1cdf8419ab1fe4139fe4c40f2f3ea40cd6d713fda21df3fb0461d3f45b0543f03db853ec90e503e6b88703e471ac63dff89883dd7747e3dcc00503d9568fd3d8ff9473d3cfb3d3cec540f3c995c183c92d0703c67b9c43c5c8e443c53ccb63b845e593b6249f13b6006df3b5357193b2b79093b1f8e953abf71143a9983be3a89ec663a62e0b039fb299839f4aa4e39f312dc39d4b68a3966381e38efc6e4386f48663862ed49385e7e4c3853339d3839107b380c000e3804c6b9
  | 9, 6 => 0x504c0b98504b55285014c38c5001a1a34fd233b44fb299df4f3c1c034ea59da54e6fafee4e66db724e2a93db4e2a91a54dd696634da956fc4d8f98164d7bd7da4d6ce6344d45a22d4d3828c24d200f134d018c804cfcb81b4cf39c514c6b93d04c57e84a4c566dcb4c29632d4c2180f94b4af4174b2cbd954b11c71c4ae589544ad6fc654a9036bc4a60612a4980e14d496a0528493d3c6e492fca4f4920eb3948e7797f48bc295248b9ea46489d5e00488d9dc7486f81a5474da3b24721f278470d4b5c46a699c84681cb5d4667dcd64632738f4618554145bbdcd6459ced20457ea4b9453165d445081b0e44e4733744d748de44cefd4644987ec04481cb30
  | 9, 7 => 0x5d82e91a5d1e2f215cbf09575c8c34ab5c0828bd5bdc75195bcfdd4e5bc25b2c5bc00f655bae49bd5b35b3315aaabc295aa651da5a30e4015a13d78f5a002267595eac3959592664593ecf4959398f8858dce12f58da90b158d3754058cc2a905885cce5588091a45849b54057a9f79e5782d480575efb7d565fe37356576a8456499a04563f828c55bcf36d557de172556dd6255562460155193f7e54e74a5454e3a1a654cf183654b67ba854ac849b54a6677b549c4bfd54071364535067ed52b50c1b52a4aeb652a0b13a524969bd523acdf05235d1b151da4416517d7ed8517ac4d35101aaab50f3682550cccd7250a2ac00507eaec05070c86f506d2270
  | 9, 8 => 0x6cf7b1276ccf5b736ca3e4856c376a3a6c1a426f6ba5d1186b59b83e6b1ff0076abf48ab6a81d2ce6a767aa36a5e080a6a3cddd66a3b1c8e69c3c5cb69be6a7e696d69df69566b31693c011d690662c168e50ede68d674e768b389d768a2155968842345686c3e0b6828266467a9a2c1679aa58c6758995867467eb367444029670884dd66dca7966653c1296632a9a86631cbff662108db66045a2065af059e65aa320b64a2ed186496dd1c63aa11ac6238e334623862fa61fbb75161c731d76176ddfb614c1cad6117f06560e2423060c3605d60948264604f952c6045479b5fe196665fa1f5e95f8dd6785f2fba975eae2a0c5de88be05dcd65305db40c09
  | 9, 9 => 0x7f5641d67f4f65777f4b6b2e7f212a807ebe4f2d7ea597f67e5ba4e07dc1d6467d53f3ec7ca801537ca27b7e7c41a0bf7c158c207b6344667a83b53f7a4bbeac7a352adc7a210b1879df9a4b79cc705179a9388d79a4eecc798569b47928346d79025e5978e44db87843fd0a7840741677a1a1bf775654c77741a7ff76654ee1763995237639608075ec856175cc821675b9400d758db184751f2db374cdf405748db9b374361d25740ce6c57347c1377328fc2b731f52f072becce472670b6f71e472137198d160717845027121b324710b0b4870de90bc70db5a8c70aea48b6fb36dff6f6e33586f18be8f6e4a868e6e3af9296debed8a6da9b6446d75148d
  | 9, 10 => 0x8fb798a28fa4ea6d8f7d7f578f6274168f2068958f1bf8a68e7502958e1dd0088d927f388d03c7bb8d0125ba8cb62e328c69c7d88c3d67618c1d3d508be94e1d8b8749738b5111888b1958d28af785ea8aa8829c8a5561548a47d6a18a330168899b3d0f894dc47b88ad4f798888960788748f1a886e5671885958bf87ec0f1a87ebc50e87ac9d4b86e8db4d85fc4cd785f585bf85bbb0548598ae228593442c856256898530f70a84dc7c4a8497628d83f6554a83d93d9883c3ea67835273ba832c888a82d6ae6e82c882fa829821c6827c38b5827b391181f2a8f081e8e96481bd17f381b7921e818484a2817acdbc816c62148149bcfb7fe0ee617fcf871e
  | 9, 11 => 0xaa4c9558a9ee54f8a865afbba865405aa752f579a6f5a932a6b668c5a6b567eaa6473be8a5fc7f40a564cc3ca4b9a911a4429173a349cd04a1be679da163bb5ea161b40aa14f0e96a0a3a397a091a6faa087dceba046c717a0010a8f9fd28a739e75f4419d3849ee9d00db219ca950fd9c37537c9c15e3ab9c025a349b72c64b9ae9bb269a4317f69a21e42c986e23cf9864d9d097a354d99781448b9734464696eb5c9596dcc20a96031c9395fee55395d8b47f9567f79694f2ad8e94d2befd94d19895943e122f93fee1b193f0fe6393ab51e992586d0991ea495091ace296919daa4891288d0b910264929080a64d903e019d9024f9e08fd5f8ca8fc3d304
  | 9, 12 => 0xca8fd156c9dff10ac82a0e90c7f04e79c76d8307c754d024c73be04dc6b6b794c6b3c12cc66459bbc5802ce2c4cc9417c4af607dc2a8678fc2a1e7a1c279657ec2546b5ec19c7266bf001425bea1a541be5ec99dbe2bbe9dbe235678be1d8e45be0c4848bdfb3225bdbff159bc811d14bc53f7e3bbc61c26bb6d9320ba2d33efb9a93e31b8e03528b85707d8b852e344b46eac9fb465e382b44c7454b3e0dd2db3ac5c85b2e56fadb2d5368fb2cd6e10b2c7e83bb24fc653b1f975b1b09714e5af17c1dfaeac6164ae152952ae03bbe1ad8d2fffacfcff49ace41505acb17c07acae9164abcea641ab397f8eab1763d8aaac2491aaa08e4caa67e0c7aa5b4e46
  | 9, 13 => 0xff8ebb79fb873f83fb795490fa87bbb4f9806d37f973255af6882c40f6227e9cf616447df5cd910bf39de580f2eebaf6f2da0e2eef689247ef290e1beeef692dee694147eb76c673eb70b635eb1b6671e9db3e39e8e349cde857790ae7e7a7c3e7885e2de5b87607e523acefe4bb4818e43a9a86e4336287e26ea595e0dbabe9de742515ddb9c31cdcf69efbdce7897bdbb673bfdb7c8e19db756582db263ca7d99c010ed8f5155cd768223ad72bfb70d4cb3165d314347ed30ec467d1c8ce69ceee1ee0cdfe506ccdb6e068ccdc3de0cc7f8a6dcb9de4fbcb7c4cbccaa65c2a
  | 10, 0 => 0xddb9c31cc9dff10ac6b6b794c5802ce2bf001425be0c4848b1f975b1ae03bbe1ace41505a9ee54f8a6b567eaa4429173a163bb5ea14f0e9696dcc20a8fb798a2899b3d0f85bbb054816c621479df9a4b76654ee1614c1cad4721f2784481cb3040cd6d713d9568fd3c92d0703853339d36e356d9326ce2a82fe1627c28c0bf1426b2ee6525c277fc1f800bb01caff99119ceb8a618d3087217cb6b9917b1018509aab39905d3fbe501c56855
  | 11, 0 => 0x2fe1627c
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x640047ff40c07f0a210821fe300003ff80603f800000007e362cb9ce68ea162cb9ce68ea00000000000000000000000007f0a210821fe640047ff40c03f800000007e300003ff806038b1c5f1062c58b1c5f1062c5c1860f800140c1860f800140217df87e0c479f000882f410801e7c1f0601cf800000780807c00220bd04285f7e1f8311e3e000001e0200079f07c1807c893ffffffa81023fa1100004001ffffff800001fc000000372c31acf0801e6ea94a28fb8000000000000000000000000
  | 0, 1 => 0xff9aa528a3fe7420c7ff40c03f800000007e300003ff80603fffffffffea1fffff8c60801fffffffffe00fffff0000000237df8fe1c57bf4518c6fc11801e7c1f0601cf80000078083fff212824841fff651922804fff800000000fff800000000ffc71fc6fcb1e3fffffe1cf7ffe183e07858307fffff0651ffff210820801fff210820800fff800000000fff8000000009023fa1100004893ffffffa84001fc0000000001ffffff80286209a27491813fec2092cbd01860f83e60001fff0001e5f
  | 0, 2 => 0xd8b3ffffffa858b3fe3182004001ffffff800001fc0000003fffff8c60801fffffffffea1fffff0000000fffffffffe0070dc0d6c0bef1611f87e0c10307e03ff87f7ffe07c1f067e095f7e3f9311efc20a22bd15a0079f07c18073e000001e0201f004a93f410e97ff97e2def8f8000007808001e7c1f0601e3c8fca4fd043a7b81e07cfbf3e07f001e020007e0f83e6079bfcc3dfc2c000f6a528a3fe0ffe03ff8060007e0000007e3a7f7f1fa391e7c82220bd0420079f07c18073e000001e020
  | 0, 3 => 0xe3c71fc61cb1e3c71fc61cb1f06183e00050306183e000500fdf7e3fbf15efdf7e3fbf15e3e79f07df8273e79f07df8276fdc05eeffffb76c00000057bffe03fffffffffe0000007fdfd3cc730e7fd99155ffd6344fe00000001f8c0000ffe0180664557ff58d17f4f31cc39ff300003ff80603f800000007e37e42328bd842c5f7e1f8311e3e000001e0200079f07c1807ec90c7ffc2c07f2aa10821fe300003ff80603f800000007e3d0831ffd0301fe6a94a28ff8c0000ffe0180fe00000001f8
  | 0, 4 => 0x7f4f314c29ff660047ff50d03f800000007e300003ff80603a35ffffffea4488fea4440410007fffffe000007f0000000e3fffffe1cf7ffc71fc6fcb1f07fffff0651ffe183e078583fff318c60801fffa94a28ea0fff800000000fff800000000f423ffff40c07f9bfffffffe7001ffff80603f81fffffffe095f7ebfd311ffc28a62bd7fa0079f07c18073e000001e020e6c757d758b16bcf37cc39ff706183e00050306183e00050188cb24cf1ac3e4e2bf129e3ac079f07fff47fe79ff81ff3f
  | 0, 5 => 0xc082070103a84082070103a8706183e081f6306183e081f63324ffffffea0c4afe86401190007fffffe000007f0000000fffc84a2c2007ffca42882463ffe000000003ffe000000001fc013fffd343fdffe5f8b7fefe000fffe1a0fe79f07c19ff3f4518c6fc11a37df8fe1c578f8000007808001e7c1f0601da5ffe5f8b7be7c012a4fd0420079f07c18073e000001e020fffcc6b3c2007ffea528a3ee3ffe000000003ffe000000001ec013df6d34379df65d8b6e6fe000fffe1a0fe79f07c19ff
  | 0, 6 => 0xe6c717c658b163cf37cc18f7706183e00050306183e000501cb93b75462c4a953a0ef9c64c181ff800140c181f07fff40d8b0c631820058b2a528a3a80000000000000000000000003224a94a28ea04083084400000000000000000000000000007f0a298af5fea57dfaff4c478f8000007808001e7c1f0601fa66a94a28fb850830a4d00000000000000000000000000004ea1fd90f3b8286c0882f4473fe07fe0f9fe307e00007877dfc256b5d7007900cf080f4fffe07fffffe07c007f001fe7f
  | 0, 7 => 0xe99bffffffee1423fa9340004001ffffff800001fc0000003fffa94a28fb9fff31acf0800fff800000000fff800000000e9fffd7eafef9f20ca93f410801e7c1f0601cf80000078081fc28a42897fb94013ffd1302fe00000001f8c0000ffe018065004fff44c0ff0a290a25feb00003ff80603f800000007e09df7e3f9715efd34e33bf15e0079f07c18073e000001e020690a210821ee040042934000000000000000000000000000362c21082080162c210820800000000000000000000000000
  | 0, 8 => 0x9020c21100004892a528a3a8000000000000000000000000162c017bbfea162c017bbfea000000ffffe0000000ffffe00dfb08ca2f610f9fdfc7e8e478f8000007808001e7c1f0601ff2c31fff0b01feea94a28ff8c0000ffe0180fe00000001f8f92bfb1921ee4c93ffffffa84001fc0000000001ffffff8021b1d40ed61c47734db30e53d0186007e00c03f860f8000b8fffea528a3a87ffcc63182003ffe000000003ffe00000000362cff8c6080162cffffffea10007f00000000007fffffe00
  | 0, 9 => 0x3f08288af456a57df8fe4c478f8000007808001e7c1f0601f8f3cdf3063dd9b1c5f1962c5c1860f800140c1860f8001407f7ff97e2dffff004ffff4d0bf9e7c1f067fff8003fff86839b1c5f3063c59b1c5f3063c5c1860f8001c0c1860f8001c0fffc852882c07ffc852882c03ffe000000603ffe000000601fc299ffd87f9fc299ffd87f8fe000ffe01f8fe000ffe01f8ff2aa10821fe6c90c7ffc2c03f800000007e300003ff8060074ee4f926ac474ee4f926ac53e7e0f8001403e7e0f800140
  | 0, 10 => 0x9f208882f410e9fdfc7e8e478f8000007808001e7c1f0601fcb9e5f1062c5ab5e5f926ac5c1860f800140c1860f8001404866210821a98bdc4211bf3f807e00000001cffe00007f9ffe7f7f1fa391f7ec2328bd8420079f07c18073e000001e020eac737cc39b962c757d518b1706183e00050306183e000503fe6ffffffff9d08ffffd0301fe07fffffff8c007fffe018010d624e6de01d36c47ff4097807e03ffff81cffe03ff801ffbca76c6487f8b24ee002fda1fe07f00001f8c007f001ff80
  | 0, 11 => 0xd823fb1921a84893ffffffa84001fc0000000001ffffff801b4299ffd87b9fc298e6d87f8c0000ffe0180fe00000001f8fffca42882467ffc84a2c2003ffe000000003ffe00000000000e380e40d38700000078c200079f07e1e9f3e000003e6b87f0a631921fe6c0267ff61e83f800000007e300003ff80603224ffffffea1608fec6486a10007fffffe000007f00000005f02298af5b8a17dfa7f0c478f8000007808001e7c1f0601db0099ffd87a1fc298c6487f8c0000ffe0180fe00000001f8
  | 0, 12 => 0xead7ffffffb93267fad518114001ffffff800001fc0000003264ffffffea2448fe84c10030007fffffe000007f0000000660047ff50d07f4f314c29ff300003ff80603f800000007e0f1144117ac2408e382e44d783e000003e6b80079f07e1e9f6fdf7e318200376f7bdf7da87ffffc0000003fffffffff80191155ffd2305fc288620c7f8c0000ffe0180fe00000001f89223fa91101068d7ffffffa94001fc0000000001ffffff800000def7df7fe000def7df7ff0007ffffffff0007ffffffff
  | 0, 13 => 0xffbaa528a3fe7cb0c7ffc2c03f800000007e300003ff80601fc288620c7f991155ffd2304fe00000001f8c0000ffe0180ca93ffffffb83067fa5508014001ffffff800001fc0000003ab5e5f926ac5cb9e5f1062c5c1860f800140c1860f800140457dbf814c87e00a298ad5eeb01e7fe08661f0000000787630eebbee853dbf71c7d1bb287c1fffffc1947ff860f81e160b17dfa7f0c47df92adaaf7b8801e7c1f0601cf80000078083cb9f5f5462c5ab5edfb2eee5c1860f800140c1860f800140
  | 0, 14 => 0x80f5def7de019bffb800bf3fc07fffffff81cffffc007f9fc85fa0e85c6e07c0dcd7627bd007e0f83e7f83e07fffe1fdf650867ff40c67f0a218a61fe300003ff80603f800000007e2c4afe8640119324ffffffea10007f00000000007fffffe00e7c71fc65cb1e3cf3fce1cf7f06183e00050306183e0005037e4ab6abdee2c5f7e9fc311e3e000001e0200079f07c1807ec92e7ffe3e87f2ae31921fe300003ff80603f800000007e3af3cdf30e7fd9b1d5f5d62c5c1860f800140c1860f800140
  | 0, 15 => 0xd793f77d0bb8b15e026f0c47cf81ffff8788001f801f0601f02eb9ce40fb972081c078ea1c1fffffe1fdfff860f83e7f8040042934000690a210821ee0000000000000000000000002c19fe95420052a4ffffffee10007f00000000007fffffe00fffd94648a017ffc84a092103ffe000000003ffe0000000026ffee002fcfe03d77bdf78073ffff001fe7f01fffffffe07f423bdee40c03799def7de567001ffff80603f81fffffffe3ab5edfb2eee5cb9f5f5462c5c1860f800140c1860f800140
  | 1, 0 => 0x8d1b122ae74ed5ab17c418e6cf9f801fffafcf9f83e0002fffff2308a1803fff2308a1802fff800000000fff800000000b17df87e0c47df908ca2f610801e7c1f0601cf80000078083ebde5f926ac5ebde5f926ac5c1860f800140c1860f8001409123fa130400c993ffffffa8c001fc0000000001ffffff80240820739f7ff22421082095e00000fffffff0000000001ffd8b3ff39a3a858b3ffffffa84001fc0000000001ffffff8027fd759d4a844ea0901facde13ffffffe1e273f86007de678
  | 1, 1 => 0xd8b3ffffffa858b3ff39a3a84001ffffff800001fc000000393d664227b0793d664227b07c1fff001ff87c1fff001ff87a74ffa110057a74ffa110057fffffc00007ffffffc00007fcf9f7c3f3e15cf9f7c3f3e15c3e79f07df8273e79f07df8271b0a66f7613e1b0a66f7613e0f8003ff801e0f8003ff801e085f7e9fc311f7c08a62bd6e20079f07c18073e000001e0209423fa934000699bffffffee4001fc0000000001ffffff80306083c0c1ea306083c0c1ea3c1860f8207d8c1860f8207d8
  | 1, 2 => 0xb267fad518116ad7ffffffb94001fc0000000001ffffff803fff653926845fff653926844fff800000000fff800000000ffce250821fe66c447ff40c03fe00000007e306003ff806039b111ffd0301ff38942087f8c1800ffe0180ff80000001f8ffff97e49ab17fff97e49ab17fff83e000503fff83e00050070e380e78d3870e380e78d383e79f07ffebf3e79f07ffebfe2c46c1b654ee2c46c1b654eb0607c1fffaff0607c1fffaff83f23289d8437a05f17a391ec1f80001e020ff81f07c1807
  | 1, 3 => 0xeac717c438b162c757d418b1706183e00050306183e0005037e4ffffffee2c5ffe9fc311f3e07fffffe20007ff07c1807c8908ca2f6001021f810000000000000780000007c00000000400200810020400200810020000000000000000000000001d38e83be74e9d38e83be74e8f9e7c1fffafcf9e7c1fffafd900006290301942084200318c00000000180c000000001800000421100004802210821a800000000000000000000000008d14631870468d1463187046000000000000000000000000
  | 1, 4 => 0x376df8100057efdc0deeffffbffe7c00007ffffe03fffffff8b10100000018b1010000000c18000000000c18000000000376c00000057efdc05eeffffbffe0000007ffffe03ffffffd90011acd0001fc28842087b8c00000000000fe0000000000e2c717cc18f166c717c418b1706183e00050306183e00050383ffddf42fbd7a081e07cee1c1fffffe1fdfff860f83e7f87f0a218a61fe650867ff40c63f800000007e300003ff8060085ffe1f8311e7c012a4fd0420079f07c18073e000001e020
  | 1, 5 => 0x64004fff40c07f0a290a25fe300003ff80603f800000007e3fff230820801fff2308a1800fff800000000fff8000000005f000882f410a17df87e0c478f8000007808001e7c1f0601e408fc8440001224fdff7eea10007f00000000007fffffe00fffcc7ffc2c07ffea528a3fe3ffe03ff80603ffe0000007e02000220bd0000087e040000000000001e0000001f00000007f0820080046640004a240003f80000000003000000000003fffa94a28ff9fff31fff0b00fff8000001f8fff80ffe0180
  | 1, 6 => 0x15ad75c57800339ce7dffc001ffffffffc001ffffffffc85f7e1f0311e7800220bd0420079f07c18073e000001e020c8b3ffffffa81823fa93f4004001ffffff800001fc0078003224ffffffea6408fe844f4ff0007fffffe070007f001fe7f4802210821a800004211000000000000000000000000000037a081e07cee183ffddf42fbdff860f83e7f8c1fffffe1fdf000043df40c00002210821fe000003ff806000000000007e1900dfffdf7fffc2def7df7ffc007fffffffffe07ffffffff
  | 1, 7 => 0xff9bffffffa87423fe3100007f81ffffff803001fc00000000087e04000002000220bd0000001f000000000000001e000b17ffa7f0c47df93ffffffb8c01ffc1f0601cf81ffffff8820b145b1060448b1c411060c501860f800000018600000040d8b3ffffffa858b3ffffffa84001ffffff800001ffffff8008df7e1f8315efc00231bd0420079f07c18073e000001e0203f0048fef450bf7df87e2c578f80001f78080f9e7c1f0609d95f7fffd331ffc28a62bd7fac079fffe1987fe000001e1f8
  | 1, 8 => 0x480267ff61a8100262110000000003ff80000000000000003b24fffffffa1fcafec6487f9c007ffffff80fe07f00001f820451044080102000080101000000000000000000000000018808040002c180001f100200c00000000140c0000f800100ffcf37cc39ff66c757ff58f17fe183e0007e306183ff807039b111ffd4341ff3cd530a7fcc1800ffe0180ff80000001f87f0a252821fe740047ff40c03f800000007e300003ff80600100002090000842080200118000000000000000000000000
  | 1, 9 => 0x4e800580f3b8206c000000473fe003e0f9fe307e00000077c842080200118100002090000000000000000000000000000217c802000001f0000008000001e000000000f80000000003fff7f1fa391ffff2328bd842fff9f07c1807fff80001e0209bfc8000820000f4842082000ffe00000000007e000000003fffef082fcfffff77bdf7807fffff001fe7ffffffffffe07660047ff40d07f0a214c21fe300003ff80603f800000007e185ffe5f8339e7c002a0bd0420079f07c18073e000001e020
  | 1, 10 => 0xe9bbffffffee1c23fa93f4004001ffffff800001fc007800180001f1002018808040002c0c0000f800100c00000000140e6c757ff58f17fcf37cc39ff706183ff80703fe183e0007e07428842087f810010ffd03003e00000001f800000ffe0180216d785e0c478f000882f410801e7c1f0601cf80000078083fff651922801fff210820800fff800000000fff800000000657cc7ff40c07f0a2108a1fe301e03ff80603f800000007e27c832a4fd043a7fff5fabfbe3e000001e0200079f07c1807
  | 1, 11 => 0x200008010102045104408010000000000000000000000003fc28842087f992011ffd0300fe00000001f8c0000ffe01809423fa110000699bffffffa84001fc0000000001ffffff80190010e6d0301b428842087b8c00000000180c000000001801f00000020102000407e00400f80000000080000001f00001fc28a62bd7fb95f7fffd331efe000001e1f8c079fffe19870bdc0000bf3f8064000000018ffe00007f9fc07e00000001d900010800001fc2000000000c00000000000fe0000000000
  | 1, 12 => 0xc8820781f3a80023f2110000400183e0f9800001fc00000037a4ffffffee1c3fffdf42fbdff87fffffff8c1fffffe1fdf060000825010214d304c0847000000000000000000000000040088000000100011ffd020000000000000000000ffe0000ff2bfb1921fe6c93ffffffe87f81fc00007e3001ffffffe01bf7457bbfffeddb00200415efff80ffffffffff8000001ff5f000ca2f410b17df87e0c478f8000007808001e7c1f0601d3a081e07cee081bdcd7427bdff860f83e7f8c1fffffe1fdf
  | 1, 13 => 0x31f87e0c0018000882f40000007c1f06000000000078001fc2cc530a7f990011ffd0300fe00000001f8c0000ffe0180fffd9c668e01fffc8ca29610bffe000000003ffe0000000038b1d5f5462c5ab1cdf30e6e5c1860f800140c1860f800140600a210821fe440047df40c030000000007e300003ff806037ec210820801e7f2108208003e0000000000007800000000c8908420820010208000000000000000000000000000000038b9e5f1062c5ab1c5f1262c5c1860f800140c1860f800140
  | 1, 14 => 0xc893ffffffa81023fa1900004001ffffff800001fc0000003fff210820801fff2108a0800fff800000000fff800000000640157ff48c07f0a210821fe300003ff80603f800000007e1fc298e6d87f9b4299ffd87b8fe00000001f8c0000ffe0180224510c41811224510c418110000000000000000000000002224ee002fca00087684400010007f001fe000007f0000000dbffffffffbf90f7fef7de01cfffffffff9fc07fffffff81fa7ffffffffbe7c8fea4fd043007ffffffe073e07f001e020
  | 1, 15 => 0xa24712c4181162c717c418b1400180000000000183e00000383ffffff7fbf7ffefe07feffc1ffffffffdfffffff83ffffcb93ffffffb8b167fa570c01c001ffffff800001fc0000000800101f801007c00000080400000007c00003e0000000020a2c71044183102c516c41811406180000010006183e000002ddb20000015fbf7217bbfffefff8000001fffff80fffffff489005eeffa8102000000000000003ffff800000000000003bf7ffffffffeddbfe844015ffffffffffffffffff00001ff
  | 2, 0 => 0xe2c737c418b162c717c658b1706183e00050306183e000500a5f7e1fa311e7c82220bd0420079f07c18073e000001e0206000477d00c05e02010021b8300003ff80603f800000007e393ffdffd2fbdfe289e27cff9c1fffffe1fdfff860f83e7f8dbfc8420820010f4842082000ffe00000000007e0000000007c01224bd042a5f7e1f8b11e3e000001e0200079f07c18079f23fa93f410e9ffffffffefcf81fc007808001fffffff81c0047e1f830004000200000000001f07c1800000000000000
  | 2, 1 => 0x3d38e83be74e9d38e8bbe74e8f9e7c1fffafcf9e7c1fffafffff210820801fff290a20800fff800000000fff80000000093fd98009e1780f59ce6de01cffffc007f9fc07fffffff81e408fe8440001224bbeefdea10007f00000000007fffffe0000037bdf7da800037a1100004001ffffff800001fc0000003224ffffffffe408fef7df7ff0007ffffffff0007ffffffff7f08000000006400042000003f8000000000300000000000000056b5d7006000ce000f4ff0007fffffe070007f001fe7f
  | 2, 2 => 0xcc93ffffffa8312bfa1100004001ffffff800001fc00000018808060042c181145f102204c00000000140c0000f8001009823fa93f40048b3ffffffa84001fc0078000001ffffff8020bd77bdf7846effee112fcff01fffffffe073ffff001fe7fe2c737c418b162c757d518b1706183e00050306183e000503624ffffffea1408ff8c400010007fffffe000007f00000001000080000000011f87e0c0000000000000000007c1f060019f7015b02ffedd300000015efff80ffe1ffffff8000001ff
  | 2, 3 => 0x7f0a250821fe660047ff40c03f800000007e300003ff80600408108440001224897bbfea000000000000000000ffffe0048937fffffa810237a1100004001ffffff800001fc000000090011bdd0101fc28842087f8c0000ffe0180fe00000001f85802210821a8400047ff4080000000000000000003ff80003224ffdffbea0408ba84400010007fffffe000007f0000000644447ff40c07f0a210821fe300003ff80603f800000007e2408200000001224210820800000000000000000000000000
  | 2, 4 => 0x600a210801ee440007814080300000000076300003e080603ffffddf4affdfa091fffcfe1fffffffe1fffff860fffe7f85f0a210821fe6400477f40c03f800000007e300003ff80602c4afe86c111b364ffffffea30007f00000000007fffffe000075d8760c019b000800b410801e7c1f0601cf8000007808287f7fbff791e7ffee20bfcff01fffffffe073ffff001fe7f1f011882f410a17df8fe1c478f8000007808001e7c1f0601c000ded74f7fe000d6f5df6e70007ffffffff0007ffffffff
  | 2, 5 => 0x7f0a2108a1fe657cc7ff40c03f800000007e301e03ff80600dc2000000159900017b90300fe00000001f8c0000ffe01807f6e210821ffefdc47ffffffbffe0000007ffffe03fffffffffb81e07cfffbfffdffffffffffe0f83e7ffffffffffffffffde07effffff7fff77d0bffffff83ffffffffffffff87ffd8b10171062c4891000000044c1800f800140c18000000140efdf17eefffff7ef17c418f7ffff83ffffffffff83e0007fc64e3a0cf9c3a64e3a0cf9c3a3e79f07ffe3f3e79f07ffe3f
  | 2, 6 => 0xe2c715c418b122c516c41811706183e00050306183e00050190010c640301b008842087a0c00000000180c000000001807f0a210821fe64dc47ff4bef3fe00000007e307e03ff87f7e000c48000001020c5f10628100060000000000060f800000f2e7ffd518b16ad7ffffffb97061ffe000503061ffffffd03224ffffffea0408fe95420010007fffffe000007f00000007f4e210821ff66c447ff58f13fe00000007e306003ff807007c00220bd04385f7f1f8311e3e000001e0200079f07c1807
  | 2, 7 => 0xd18002ae74e9528000000468f9e001fffafcf9e0000002fe7c8200020001a7f2108208003e0000000000007800000000c08317c418a0000312000000400183e000000001800000003ab5ffffffee5cb9fff5462c5c187ffffff40c187ff800140c893ffffffa81023fa9340004001ffffff800001fc0000003fff2328bd843fff7f1fa391efff80001e020fff9f07c18071f0000809010217d906408010f8000000000001e000000002000fe8440001200fec6486a10007f00000000007f0000000
  | 2, 8 => 0xec90842082007f28800000003000000000003f80000000001fff017bbfffffff017bbfffefff80ffffffffff80fffffff640007c64080630a210800f6300003e000403000000000501fc28842087f990431ffd0300fe00000001f8c0000ffe01806400010800c06400010800c03000000000603000000000601fcaa842087f9b0011fff0300fe00000001f8c0000ffe01801f0000008000217c802000000f8000000000001e0000000026bfec002ecfc03d75bd768053ffff001fe7f01fffffffe07
  | 2, 9 => 0x9823fa1120004893ffffffa84001fc0000000001ffffff803224ff8c60800408fe84400010007f00000000007f0000000376f7bdf7dffefdf7ffffffffffffffffffffffffffffffff8f1c5f1062c58f1c5f1062c5c1860f800140c1860f8001400a000882f4102065f854080100000000780000007c00000037bd210820801eff210820800fff800000000fff80000000000d404e6de01936c00000017807e03ffff81cffe0000001fd3e6016abdffad5b00000011efff80ffffffffff8000001ff
  | 2, 10 => 0xe2d797e418b172c717c418b1706183e00050306183e0005039b1c5f1562c58b3cdf3067fdc1860f8201c0c1860f8001d8ff8a2508a3fe64fcc7ff42c03fe00000007e307e03ff80600900103f90100fc20802081580000007c00003e00000000209a23fa93f41068f7ffffffa94001fc0078000001ffffff803fffa90820801fff318c60800fff800000000fff8000000007f4f394e2dffe7004fff54d0bf800000007e300003ff80601bf7897bbfffeddb10844015efff80ffffffffff8000001ff
  | 2, 11 => 0xe2c407c4008062c6050000b0306003e0004030600000005038f3cff3873df9f1c7f1972c7c1860f800140c1860f80014082c71000183100c516c41801406180000010006183e000003effeff12feff8bdf7fdf7ac7ffffff81ff7fc1ffffffff47400047ff4080100220000000000003ff800000000000000038b1e5f1062c58b1e5f1062c5c1860f800140c1860f8001406fdc05eeffffb76d10440857bffe03fffffffffe0000007fe408fc844000122481fbffea10007f000000000060ffffe00
  | 2, 12 => 0x800352110000488337cc39a8400180000000000183e000003408fec640201224ffffffea10007f00000000007fffffe00ff9aa528a3fe757cc7ff40c03f800000007e301e03ff806039b1c5f1062c58f3c5f1062c5c1860f800140c1860f80014080f5def7de01dbffb908bfbfc07fffffff81cffffc007f9ff224ffffffea0c08fe84400010007fffffe000007f00000009021fa1100004892adaaf7a800007c000000000000007800070c320cf9c2264e3a0e69d3a3e79f07ffebf3e79f07ffebf
  | 2, 13 => 0x9bbaa800b73e80f5de77ce01cffffc007f9fc07fffffff81c0c0022085042851461183006000000000000000000000000237df87e0c47bf440882f410801e7c1f0601cf80000078082dff210820801fff210820800fff800000000fff8000000009923fa93f400c9b3ffffffa8c001fc0078000001ffffff803fff210820801fff210a20900fff800000000fff800000000657ce7ff40c67f0a218ae1fe301e03ff80603f800000007e1fc288622c7f995f75ffd2304fe00000001f8c0780ffe0180
  | 2, 14 => 0xc89287a1f3a81023f2110000400183e0f9800001fc00000037a081e0fcee187ffddf42fbdff860f83e7f8c1fffffe1fdfe2c717e418b172c717c418b1706183e00050306183e0005009d3def7df7fe9d3def7df7fffffffffffffffffffffffffffffcc43082007ffc8420a2003ffe000000003ffe000000003224ffffffea0408fea4440010007fffffe000007f0000000fffc862082007ffe852082a03ffe000000003ffe0000000026ff2108208006ff2108208003ff8000000003ff800000000
  | 2, 15 => 0xfffc84a2c2007ffca42082003ffe000000003ffe000000002effee082fcfe7fd77bdf78073ffff001fe7f3ffffffffe07eac717c418b162c717c418b1706183e00050306183e0005037ee210820801f7f210820800fff800000000fff800000000e8fff77d8bef5ea28781f3b8707fffff87f7ffe183e0f9fe1f4e3a4ef9f3bf4e3a4ef9f3afe79f07fffbffe79f07fffbf80ffb0000b2f00800681d200407ffc000797c06183e0f9800c4288020011910011ffd020000000000000000000ffe0000
  | 3, 0 => 0xb023fa1900404c93ffffffa84001fc0000000001ffffff803408fec440281224ffffffea10007f00000000007fffffe0060dc056c0bef160000000010307e03ff87f7ffe00000007e203d779d678066bde6002fce701fffffffe073ffff001fe7fc893dff7ffa81023fa1100004001ffffff800001fc0000002000fe8440000000fe84400010007f00000000007f00000007f0a230821fe640247ff40e03f800000007e300003ff80600842181f801187c00020980400000007c00003e0000000020
  | 3, 1 => 0x7f0a210821fe6c0047ff40c03f800000007e300003ff80601f828842087f990011ff50300fe00000001f8c0000ffe0180cc93ffffffa8792bfb1921ee4001ffffff800001fc0000002c5f2008000017e42108208000078000000003e0000000000fffdb46c8a477ffc84a2d2103ffe000000003ffe000000001891c471062c589145f106244c00000000140c0000f800100ffcc0400000066c4042000003fe0000000003060000000003fff210820801fff212820800fff800000000fff800000000
  | 3, 2 => 0x440047914080680a210821ee300003e08060300000000076064e2a0029c3a00c320cf18023e79f001fe3f0079f07ffe0765086fff44c6ff0a298a65feb00003ff80603f800000007e203d77bdf78066c8ee002d043007ffffffe073e07f001e0202108280a0446850008824400800000000000000000000000085f6e1b8311e5c00220b50420079f07c18073e000001e020e99bffffffee9523fa934400c001ffffff800001fc0000003fe28942087f990011ffd0300fe00000001f8c0000ffe0180
  | 3, 3 => 0xff98842082007420842000003f80000000003000000000003a35ffffffea0488fe84400010007fffffe000007f00000001e000080f010207df07c08470f8000007808001e7c1f0601f7e083e0fdee387fffdfc3fbfff860f83e7f8c1fffffe1fdf7f0a631921fe640267ff40c03f800000007e300003ff80600599000000047af7015b2fffefff8000001fffff80fffffffe2c737cc18b162c717c418b1706183e00050306183e000501900def7df7ff900def7df7ffc007ffffffffc007ffffffff
  | 3, 4 => 0xa17df87e0c47df800c82f410801e7c1f0601cf8000007808085f280a001187c00020b00000078000000003e0000000000fffc842082007ffc852882803ffe000000003ffe000000001d0013ffd0301fc6fe5f8b7f8c0000ffe0180fe01f07c19f8e2c71fc418b162c71fc61cb1706183e00050306183e000501fc6a84a087f9d0011ffd0300fe00000001f8c0000ffe0180c28317c418b0204712440801400183e000000001800000003224ffffffea1608fe84400010007fffffe000007f0000000
  | 3, 5 => 0xfffc84208257fffc84208257bffe0000007ffffe0000007fd200def7df7fe000def7df7ff0007ffffffff0007fffffffffffcac2a8646fffc8ca2c600bffe000000003ffe000000001837dddf42fbc58080e05c6e1c1fffffe1fdfff860f83e7f8de824791f3b868fff77d2bef7fe183e0f9fe307fffff87f7c857001b8311e5c00000000420078007c18073e00000000206ffdfdfeffffbf6c0882f457bffe7ffffffffffe0000787ffa77fffffffbc588fea4d40410007fffffe000007f0000000
  | 3, 6 => 0x7fde25eefffff76c47ff40d7bffe03fffffffffe03ff807fc2f7ce002fcfe01956b5d70073ffff001fe7f01fffffffe07e0c717c418a1020312801010400183e000000001800000003a24ffffffea0408fea4400010007fffffe000007f0000000440047ff4080790a210821ee000003ff800000000000000038f1c5f1062c58b1c5f1862c5c1860f800140c1860f8001407f0a210821fee55c47ff4cc7bf800000007e301e03ff8661f7a4a1e87cee1c3ffddf42fbdff860f83e7f8c1fffffe1fdf
  | 3, 7 => 0xfbffbc00bf3fe2f5def7de01fffffc007f9ff07fffffff81fa24fffffffa0508fe84400010007fffffe000007f00000009022a00000004890c7ffc280000000000000000003ff80003264ffffffea0408fe84c00010007fffffe000007f0000000640047ff40c0370a210821fe300003ff80603f800000007e2488fe8440041a24ffffffea10007f00000000007fffffe00240042ff40407f0a210821fe0000001f00000f80000000081bc20042087f8900000000100fe00000001f8c00000000180
  | 3, 8 => 0xe0c7174408a14282078010b0706183e00050306183e0005038bffdff46ffdfb1c5f17eee5c1fffffe1fdfff860f83e7f81f0118c6fc10a17df87e0c478f8000007808001e7c1f0601ffff216ab0b01fff294a20b18fff800000180fff8000001806fdc04208200376c000000003ffe000000003ffe000000003fff217bbfffffff21082095efff80ffffffffff8000001ff217c882204009f0008028400801e000000000f800000000001400220910028420a028111a000000000000000000000000
  | 3, 9 => 0xd893ffffffa81033fa3100004001ffffff800001fc0000001b0011ffd8301fc29846087f8c0000ffe0180fe00000001f87f08010800c06400052800c03f8000000060300000000060376ebbcef9fbb76ebbcef9fbbffffffffffffffffffffffffbfffb800bf7feffddffffffffffffc007fffffffffffffffdfc28a42a97fb95f33ffd1302fe00000001f8c0780ffe0180de800400820060fc842002003fe000000000307e000000003fffa1e87cee1ffffddf62fbdfffe0f83e7f8fffffffe1fdf
  | 3, 10 => 0x240043df40c06f0a210821fe300003ff80603f800000007e2448fe8440001224ffffffea10007f00000000007fffffe001c000001e3080038e039034e0f800000f9ae001e7c1f87a7d95157ffd3307fc28a628d7fac0000ffe0180fe00000001f8f6e4c7ff40c07fdea528a3fe306003ff80603fe00000007e390031ffd0301fc2a842087f8c0000ffe0180fe00000001f8172800000056eddc056eefefbffe0000007ffffe03fffffffa75ffffffea64c8fea4c50430007fffffe000007f0000000
  | 3, 11 => 0xc8b3ffffffa818b3fa11bf284001ffffff800001fc007f8039b1c5f1062c59b1c5f1062c5c1860f800140c1860f800140000313c418b1000313c418b1400183e00050000183e0005038b1dff7df7ff8b1dff7df7ffc187ffffffffc187ffffffff1d3bfbffffff9d3bfbffffffcf9fffffffffcf9fffffffffe43d2108208016ff21082080001f8000000003ff8000000005f00098af490a17df87e0c478f8000007808001e7c1f0601c85f7e9f8311f7c08260bd2c20079f07c18073e000001e020
  | 3, 12 => 0x660047ff40c07f4e210821fe300003ff80603f800000007e000002209d0420005e178311e00000001e0200001f07c18071f037bdffdffa17ffbff7dffcf81ffffffffc01fffffffffcfc20220bd04295f7e1f8311e3e000001e0200079f07c1807e7fcc7ff40c07fce2508a1fe307e03ff80603fe00000007e085f761d8311e7c00220bd0420079f07c18073e000001e020faf4842082007af484208200306000000000306000000000383ffddf42fbd7a089e27cee1c1fffffe1fdfff860f83e7f8
  | 3, 13 => 0x9023fa937410c893ffffffefc001fc0078080001ffffff81c85f7e3f9311e7c00a20bd0420079f07c18073e000001e020170008827410a15d787e0c478f8000007808001e7c1f0601d7428842087b8100108ed01003e00000000b80000007e00806400463100007f0a210821a83000000000003f80000000002408ee000000002477bdf78010007f00000000007fffffe009bfffa11bf3fc8f7ffffffa9cffffc007f9fc07fffffff81d9b111ffd63c5fd38842087fcc1800ffe01c0ff80000001f8
  | 3, 14 => 0x217cc07e00401f000000a010001e001f00000f800000000808428842087f810010f7d03000000000001f800000ffe0180e2c514c4181162c514c41811306000000000306000000000190019ffd0301fc28862987f8c0000ffe0180fe00000001f87f0a218a71fe654d77ff48c73f800000007e300003ff806007c08a20bd04285f7e9fc311e3e000001e0200079f07c1807eec737cc39f966c757dd18f1706183e00070306183e000701ac28842087f990011f5d0200c00000000140c0000f800100
  | 3, 15 => 0x6edc05ecfbff366c000000573ffe03fffffffffe0000007fffcaa842287f9b7f31fff0b00fe00000001f8c0780ffe0180c8f5def7de019bffb800bf3fc07fffffff81cffffc007f9fc000dcf75e7fc000dcf75e7fd0007ffffffff0007ffffffff210b7bdf7dff84037bdf7dffc001ffffffffc001ffffffffd95711ffd331ffc28842087fac0780ffe1987fe00000001f8193bb800bf3f8031daf7de01cf9ffc007f9fc01fffffff81ff2c210820801fee210820800c00000000000fe0000000000
  | 4, 0 => 0xfffc852082807ffc852082803ffe000000403ffe00000040005f6e000301e0000220b50020079f000180700000001e000bbfff87ebf7f9ff5def7fe11cffffc1f7f9fcfffffffff89c742080208538100100ed01003e00000000b80000007e00807f3ae93be7fefd38efffe7cebf9e7c1fffffff9e7fffffefd94211ffd0301fc28842087f8c0000ffe0180fe00000001f80810e83be7081020e811000000007c1fff8000007c000000376efffffffba74efe8ef9d3b3e7ffffffebf3e7ff07ffebf
  | 4, 1 => 0x7f000fc6f490e37ff97e0cf7bf8003e07848301e7c1f0651cfc00222bd14295f7e1f8311e3e000001e0200079f07c1807ddb8ec3be74e9d38e83be74e8f9e7c1fffafcf9e7c1fffafe608fe846000122cffffffea10007f00000000007fffffe009dfdfeffff4f9ffff83bff7fcfffffffffafcffffc1fffbfffcab8c6487f9b24b9fff8fa0fe00000001f8c0000ffe0180fffcc73982c07ffea528a3e83ffe000000603ffe000000603224ffce68ea0408fe84400010007f00000000007f0000000
  | 4, 2 => 0xa17df87e0c479f008882f410801e7c1f0601cf80000078082c5bfe974211d3a4ffffffee10007f00000000007fffffe00fffc842082407ffc8528a3fe3ffe000000603ffe0000007e07400200b900204e3a0e8111a3e000001e0200079f07c18071f38e8bbf75ebd7df87fef4f8f9e7c1fffafcf9e7c1fffafe03d77bdd78066a0ce002fcff01fffffffe073f87f001fe7f1f000882f410e97df87e0c478f8000007808001e7c1f0601cddb00000015e9f70139b795efff8000001fffff80fffffff
  | 4, 3 => 0x1d38ea3be74edd3ae93be7ee8f9e7c1fffafcf9e7c1fffaff87f7f1f8311e7c00220bd0420079f07c18073e000001e0203f000882f410a17df8fe0c478f8000007808001e7c1f0601ffff211920801fff210820840fff800000000fff8000000007f0a210a21fe650047ff40c03f800000007e300003ff80601204fe5f8b6a04001284400000001f07c1800000000000000070008825410a14d384e0c478000000000000000000000000040def7df7fe040def7df7ff0007ffffffff0007ffffffff
  | 4, 4 => 0x440047bb40c07d0a210821ee300003ff80603f800000007e2effee022fdfe13d77bdf78073ffff001fe7f01fffffffe07000001ce7dff800000000057800003ffffffc0000000007ff7a0dff7fffff83fffffdffffff87ffffffffc1ffffffffff80b0ceb3d60099ffb800af2fc07fffffff81cffffc007f9fdbf7037bbfffeddb02008115efff80ffffffffff8000001ffe2c717c418b162c717cc18b1706183e00050306183e0005026ffffbdffcfe6ffffbdffcff3ffffffffe7f3ffffffffe7f
  | 4, 5 => 0x121f812040089000882f40080007c00000000000000780019808042003c190001f300300c000000001c0c0000f8001801f1088a2f410b17df87e0c478f8000007808001e7c1f0601c7c000200c040811541f821043e00000000200000007c0000dbffbc20bf3f90f5def7de01cffffc007f9fc07fffffff81f7bdf7fdffee7effffdf6ffffffffffffffffffffffffffff600047d500806a02210821b8300003e000403000000000500000deb5df4fe000deb5df4ff0007fffffe7f0007fffffe7f
  | 4, 6 => 0x377df87e0c57ffdc0deeffffbffe7c1f067ffffe03fffffff8b10120040418b1451102004c18000000000c1800000000000026b9b75fe80037b5f6defc001ffffffffc001ffffffffcddb56b5d715fbf7cf7bbffffffffffffffffffffffffffffc8b3ffffffa85823fb9bf5a84001ffffff800001fc0078001fc28a42087f990013ffd1300fe00000001f8c0000ffe01809bffb802bf3f81f5def7de01cffffc007f9fc07fffffff81e6ffee202fcfe83d77bdf78073ffff001fe7f01fffffffe07
  | 4, 7 => 0xb023fa5500004a93ffffffb84001fc0000000001ffffff802dff77bdf795ffffef7bbffffffffffffffffffffffffffff9023fa1304004893ffffffa84001fc0000000001ffffff8000447e1f830024400200810020001f07c1800000000000000de820580f3b820fdd6750a477fe183e0f9fe307fffff87f7d7c08842086e0800109fc01003e00000000200000007c0000657c842000007f0800008000301e000000003f8000000000085b00000011e3c00020bd0420078000000073e000001e020
  | 4, 8 => 0x902392000000489397e49aa0400180000000000183e00000383fed5b02fbc5a001a074841c1fffffe1fdfff860f83e7f882c716c4183102c716c41831406183e00010006183e0001006c28800084f800011bdd00003e000000007800000ffe0000ffffb908bfffe4f5dfffdec1fffffc007ffff07fffffffe1c00080e05c6e0000dcd7427bd00060f83e7f80007fffe1fdf8023fa1100000803fa93f4004001fc0000000001fc0078000ddb08020015fbf7017bbfffefff8000001fffff80fffffff
  | 4, 9 => 0x136f38003d3f80d55ef7de01cffffc007f9fc07fffffff81f2247f1fa38004082200000000001f07c1800000000000000fefff7fdfbff7efff7fdfbff7fffffffffffffffffffffffe408b88440001224b9fff8ea000000000000000000ffe00000021fa1100004802298af5a800007c0000000000000078003fff650820801fff212824800fff800000000fff800000000ffeea50821fe6ed4c7ffc2c03fe00000007e306003ff8060203d759d428046a080002cce101fffffe1e073f860001e678
  | 4, 10 => 0xead48420820072e4840000003060000000003060000000001bf7097bbfffeddb00209015efff80ffffffffff8000001ff620007c410906247114408b1300003e0004030000000005018b1c5f1062c4891c4f1062c5c1860f800140c1860f800140da820701b3b840f7d7750ba97fe183e0f9fe307fffff87f7ec19fe84400012a4ffffffea10007f00000000007fffffe001538c833c6469d38a82ae74e8f9e7c1fffafcf9e7c1fffafc0001a06d953a0001a06d953a0001f07ffebf0001f07ffebf
  | 4, 11 => 0x2037bdf7dffa0477bdf7dffc001ffffffffc001ffffffffe448fe8440001264ffffffea10007f00000000007fffffe00c2c717c418b162c7174418b1706183e00050306183e000500840121f811027c00200890420000007c00003e0000000020650047ff40c07f0a210821fe300003ff80603f800000007e2408f68440001224ffdf6fea10007f00000000007fffffe009020ca1100004893fd7eafa800000000000000007c1f06001fc288620c7f990055ffd0300fe00000001f8c0000ffe0180
  | 4, 12 => 0xfefc842082007efc842082003ffe000000003ffe0000000039b155ffd2305ff389620c7f8c1800ffe0180ff80000001f81f000882f410e17df97e0cc78f8000007808001e7c1f0601ffff214a28ff9fff210820900fff8000001f8fff800000180c893b7ecbba81023d2110000400183e00000000180000000190019ffd0301fc28842087f8c0000ffe0180fe00000001f8680a210821ee440047914080300000000076300003e0806039b1c5f3963c59f3cdf3063ddc1860f8001c0c1860f8001c0
  | 4, 13 => 0x217df87e0c479f00288af410801e7c1f0601cf80000078081bf7017bb0b00ddb000000158fff80ffe0180fff8000001f8d8b3ffffffa858b3feb3f6004001ffffff800001fc007800203d66002780603d66002780701fff001fe0701fff001fe07274c00000057a74c01ce7dffbffe0000007ffffe03ffffffc5000220900008467e1f831180000000000000001f07c1800c093f77d0ba81002020100004001ffff87800001800000003a3ffffffffbd7a8ffe47cee1c1ffffffffdfff87ff83e7f8
  | 4, 14 => 0x2129f81800460c000882f40000007c0000000000000078001fff3b7fffffefdf3a0ef9d7efff9fffffffffff9f07fffff7f0a218821fe640047ff40c03f800000007e300003ff80603f7fffdffbfbf7eebbeefdffbffffffffffffffffffffffff336c00000057ced405e6ffb9bffe0000007ffffe03ffffffc9d300000015e9d300000015efff8000001fffff8000001ff7f0b310821fe640047ff50c03f800000007e300003ff806025bd77bdf7847effef5b2ffffffffffffffffffffffffffff
  | 4, 15 => 0x7b0a210821fe440047f740803f800000007e300003ff8060054a1a06d953a3461a0ef9d3a3e79f07ffebf3e79f07ffebf7f0a2108a1fe6420c7ff40c03f800000007e300003ff806008157e1f830044800220040400001f07c1800000000000000c893bdeeffa81021da1100004001ffffff800001fc0000003428ff8440001224ffffffea10007f00000000007fffffe00fffffe3182007ffffe3182007ffffc0000003ffffc0000000000def7df6a0000def7df6a10007fffffe000007fffffe00
  | 5, 0 => 0xbf7ffafffc57ffffffffffffcf9ffc1f7e09cf9fffffff89c400000000000000101f800000000000000000000007c00003f0820082056240040fe40400f80000000080000001f000038b1c5f146ee58b1c5f146ee5c1860f8207d8c1860f8207d81d38e83ae4469d38e83ae4468f9e7c1f7e09cf9e7c1f7e09e6fffef7ffffe03dfffffffff3fffffffffff01ffffffffff1d38802082001d38802082000f9e000000000f9e000000003fff3b0ef9d3bfff3b0ef9d3afff9f07ffebffff9f07ffebf
  | 5, 1 => 0x4083a04400002043a0ef9c200001f00000000001f07ffe007f2bf91821fe6c004ffff4c03f807c00007e300003fff860000080000000100001f10020000000000000000000f8000003f7df87e8c47bf7c88a2f4108f9e7c1f0601cf9e000078082811c491020050a0c5f1062c100060000000000060f800000207df07c08471e000080f010001e7c1f0601cf800000780817808040086e180011df40300fe00000001f8c0000ffe0180
  | 5, 2 => 0xc282078010b060c7174408a1706183e00050306183e000503c08fff540201aa4ffffffee1c007ff800100c007ffffff40ffffffffffb97ffffff59ab17fffffffffd03fffffe00050004e3a0e8111a7400200b90020079f07c18073e000001e020b023fa7f00405f93ffffffb84001fc1f00000f81ffffff8808197e15020042800220bd0400001f000000000000001e0009003fa1100004003ffff40804001fc0000000001ffff80000900000000101bc20042087f8c00000000180fe00000001f8
  | 5, 3 => 0x9000882f4008121f812040080000000780000007c00000038ff210800001ff1010020000c1f800000000ff8000000000f6e7ffff58f17fdfffffffff7061ffff80703fe1fffffffe3220c7f1bf280008fe840000100060f81e0000007f00000009003fa1100000013fa7f0c004001fc0000000001fc1f06001bf711ffffffffdb8842087fefff80ffffffffff8000001fffffffeb3f610ffffffffffeffffffc0078083fffffffff81f920d5ffd6381fc2ccc2087f9c0060ffe0180fe06000001f8
  | 5, 4 => 0xe203130000b0608317c418a0700180000050300183e00040188081f1002c188081f1002c0c0000f800140c0000f8001400000401000000800000020000000000000000000000000003fffffce68ff9ffffffffffa1fffff00001f8ffffffffff802044000000000200000000000000000000000000000000000c5ffe1f8311f7c013fffd2420079f07c18073e000fffe0201f00080020102011f87e0c400f800000000800007c1f06003cb9ff8440001ab5ffffffea1c187f0000000c187fffffe00
  | 5, 5 => 0xe2d7fffe1cb172c71fc418b17061ffff0650306183e000503ffffddf62fbdfffa1e87cee1fffffffe1fdffffe0f83e7f8c093fffe1ca010031a0000004001ffff06000001800000000400000000001000010800000000000000000000000000000ffff97e49aa07fff962082007fff83e000003fff8000000000190000000062f700002fcfe01f8000000073ff80001fe7fdf93ffffffa8317ffa3100004f81ffffff80001ffc000000243dffbdf78076ffffffffeff01fffffffe073ffffffffe7f
  | 5, 6 => 0xfffc8ca2f6007ffdfc3082003ffe000078003ffe7c000000185f7fffd331e7c08a20bd0420079fffe18073e000001e02000011000000000000080100000000000000000000000000006c002002d04201d761d830063e000001e0200079f07c180722440000001162c405c418b1306000000050306003e000503fff7f3fbf95ffff7f3fbf95efff9f07df827fff9f07df8271f0220002010600047ff40c00f8000000008000003ff8000285ffe9fc311e7c0fea4fd043007ff07c18073e07f001e020
  | 5, 7 => 0xdfffbf81ffbfe0ffffffdfefffffffe0fffff07ffffffff7d85f7fff8331ffc08260bd2c2c079fffc1907fe000001e160400001080080000000000000000000000000000000000000054a00000011a346000ab9d3a3e78000000bf3e78007ffebf9f23fa1120106893ffffffe84f81fc0000080001ffffff80203145b1060040b1c400060c501860f8000000186000000401f000000a010217cc07e00400f8000000008001e001f00001fc29bfffd7fbfdfffffdb7fefe000fffe1f8fe79fffe19ff
  | 5, 8 => 0xf000082f410a16c000000478f8000007808001e00000001c8000008000007c00000000000000000000003e00000000003f7df87e2c57bf0048fef4508f9e7c1f0609cf80001f780802047e3fbf0004087e04000000001f07df8000001f00000007f7dfffffcd7ff7ff9fefdffbf9e7ffffe69ff9e7c1f7e7fcfdb0220bd15fbff7f7fbfffefff80001e1fffff9ffffffff317df87e0c479f11f8fefc10801e7c1f0601cf807c1f7e0839b1c5f9062c5ff3c5f1062c5c1860f800140ff860f800140
  | 5, 9 => 0xffffffffffb8fffffe7f8e47ffffffffff883ffffc1f0601ffff31fff0a01fffa90820800fff80ffe0000fff8000000000002210821fe000043df40c000000000007e000003ff80603fb1c5f17eee58bffdff46ffdff860f83e7f8c1fffffe1fdfeac71fc6fcb162e7ffd418b1706183e078503061ffe000501fc00328bd043fdf7e1f8311efe000001e020fe79f07c1807c803fb1921a80003fa1100004001fc0000000001fc00000027c0c6a0bd04387fffff8739f3e060001e020007ffffc1807
  | 5, 10 => 0x8021da1100000893b800bf284001fc0000000001fc007f803ffffffffffffffffffffffffffffffffffffffffffffffff600047fe00c07f02010020b0300003ff00403f800000005808467e1f831185000220900000001f07c18000000000000000003735d09ef0002038171b84001ffff87f7c00183e0f9fe07c0020089042840121f811023e00000000200000007c0000900332000000408357ff58a0400180000000000183ff80003fff33fffdb43fffff5fabffefff80fffe1a0fff9f07c19ff
  | 5, 11 => 0xffffffffffffff23fffff4d0ff9fffffffffff81fffff868081b00000011d3a001603cee0c1f8000001dfff800f83e7f8657df97e0cc7ff00098af4d0b01e7c1f0661ff80000078680f5f7e1ffbd3e7ce3a2efdd7a3e79f07ffebf3e79f07ffebf9f23fa11800069ffffffffa84f81fc000000001fffffff8000007e04000000000200000000001f00000000000000000000c000882f4002129f818004600000000780000007c000000085ffeffdf7fe7c0def7ff7ff007fffffffff3e07ffffffff
  | 5, 12 => 0x604517c408816202018010b0300003e000403000000000500000000000000000080200000000000000000000000000000b76ffa110057efdffffffffffffffc00007fffffffffffffffff21082095ffff217bbfffefff8000001fffff80fffffff0400403b40401d082008214e0000001f80200f800000002e3ffff5fff6bc5fffedfb2effdfffe0ffe01c0fffe0f8001f88000800000000000800000000000000000000000000000001fc28040002c190001f900200fe0000000140c0000f800100
  | 5, 13 => 0xffc40c82f410e3fdfc7e0c47bfe000007808307e7c1f0601f83f2108008017a0010020800c1f800000000ff8000000000dfb3ffffffb8f9ffffffffefcf81ffffff88001fffffff81ffffef7bbfffedff77bdf795fffffffffffffffffffffffffe40357ff40c07f8b37cc39fe700183ff80603f8183e0007e1900014a00301fc2004200300c00000000180fe0000000180e2f7dff7deb1fbffbfc4bfbff07fffffffd1ffffffe07fdfd2008a62bd6a00087e844000000000001e0000001f0000000
  | 5, 14 => 0x8003120000000003120000004001800000000001800000000fdf200820000fdf2008200003e78000000003e7800000000ffc717c498b163ff97e418b17fe183e00050307f83e000503c3fffdf42fbd7a4ffffffee1c1fffffe1fdfff87fffffff8217df83000001f000882f400001e7c0000000f8000007800000000000015e00000739f7fe0000000001ff00000fffffffff9bfffffffe7f2bffff61fe7f81fffffffe3f81ffff807e3fff7f1fa3801fff230820800fff9f07c1800fff800000000
  | 5, 15 => 0x6247114408b1620007c41090300000000050300003e000402400808040001024fddf42ea10006000000000007fffe1e0001000000000000000002000000000000000000000000000000000220b500205f6e000301e00000001e0000079f0001807ff8a2789f3fe64fff7ff4bef7fe183e0f9fe307fffff87f7c408fe040000120013fffd2000001f000000000000fffe00064000000000064000000000030000000000030000000000038b1d5ffd62c5cb1cdf1062c5c1860ffe0140c1860f800140
  | 6, 0 => 0x9d3bfa3be74eddbbffffffeecf9ffc1fffafcf9fffffffaffff1c5f10e2c58b1d5ff863c5ff860f800160c1860ffc01400800000080000020800000000000000000000000000000003800c5f1002018a0c5f1062c1c0060f800100c0060f800140fffffffefcf7fffffffefcf7ffffffff7e59ffffffff7e59feffffdf6ffff7bdf7fdffee7ffffffffffffffffffffffff0000421100000002200000000000000000000000000000001fc211ffd0301fc2894a087f8fe000ffe0180fe00000001f8
  | 6, 1 => 0xc08317c418a0408317c418a0400183e00000000183e000003fff7ffff3b1ffffab6abdffafff9fffe1987fff80001e1f800002000000000000082400000000000000000000000000038b1fff5462c58b1fff5462c5c187ff800140c187ff800140ff7ffb7f2dffff93fffffff8ff9ffc1f067fff81ffffffe804008a00000010047fffd32000000000000000001fffe1800657dfc7e0c47ff080882f410b01e7c1f0601ff80000078081fc200002000195f210800000fe0000000000c07800000000
  | 6, 2 => 0xedffffffffefff2bfb9bf5fef01fffffffe1ff81fc00787e1f4e3bfff9f3bfceba4ef9ffafe79ffffffbffe79f07fffff80f7ffffffff9bfffbdfffffc07fffffffffcfffffffffffc7c002002000085f7e1f830003e00000000000079f07c18007f7ea12821fe7f0047ffc0c03f9e0000007e3f8003ff806007c00220bd0408087e1f801003e000001e0200001f07c0000214d304c08470600008250100000000000000000000000000000020000000000020081000000000000000000000000000
  | 6, 3 => 0x6fdf7fffffffb76f7bdf7dffffffffffffffffffffffffffffca200000001b24210820800fe0000000000c00000000000ffbbfffffffe7cb3ffffffe87f81fffffffe3001ffffffe01b008842087a190010c640300c00000000180c00000000180fffffffffffe7fffffffc2c07ffffffffffe3fffffff806018c28842003d990001f190200c00000000140c0000f8001007f0a298af5fe6421ffff40c03f800000787e30007fff80603d5fffffd331ffe6ffffffffbc07ffffe1987fe07fffffff8
  | 6, 4 => 0xa17ffa7e0c47df831fc6fcb0c01ffc1f0601cf8183e078082008fc844000122081e07cea10007f000000000060f83e600e6c4042000007fcc040000003060000000003fe0000000003fff311fa0901fff210828840fff8007c0000fff8000000209023fbdf7dffc893ffffffffc001ffffffffc001fffffffff224ffffffea1428fff5462810007fffffe000007ff800000f420842000007f98842082003000000000003f8000000000190011ffd0301d00884200300c0000ffe0180c00000000180
  | 6, 5 => 0x7f0a27cc21fe660247ff40f03f8003e0007e300003ff807027fd77bdff846efffe1fafdff3ffffffffe273ffff07dfe7f0400000000002108000000000000000000000000000000003ff5ffffffee7cffffffc73dfff87ffffff60c1fffffc1947640005ee40c0370800000056300003ff80603f800000007e1fc2010800001fc2010800000fe0000000000fe0000000000ebffffffffffffe7ffd7fcb1f07fffffffd1ffe1ffe078580004200800000400000000000000000000000000000000000
  | 6, 6 => 0xc88337cc39a8000352110000400183e000000001800000002000000000001020010000000000000000000000000000000e893ffffffa87223fb1100b07001ffffffc03001fc0000503fffffff8f7ffff1d7ffff3c7fffffffc19ffff860fffe1e0eed7fffffff97fefffdd39ff7061fffffff03fe1ffe0007e3b24ffffffea1fcafe8440001c007fffffe00fe07f0000000200000440000020000000010000000000000000000000000387fffdfc3fbf7e083e0fdee3c1fffffe1fdfff860f83e7f8
  | 6, 7 => 0x6400447e00407f08000020103000001f00003f80000000083fff21f920a01fffa14820ac0fff80f800100fff800000140fffffffe9ef7ffff9fe6feb1ffffffff0651ffff83e078581fc299ffd87f9d0099ffd0300fe000ffe01f8c0000ffe01809023fa1100004893fe3182004001fc0000000001fc0000002000fe8440001020fff5462810007f00000000007ff800000ec93ffffffe87423fb1900c07001ffffffe03001fc0000600a5f7e3fbf11e7c87e24bd0420079f07df8073e01f001e020
  | 6, 8 => 0x7f0a20000000640047ff40803f8000000000300003ff800000000000000000004411020000000000000000000000000006400417e00c07f00010820d03000001f00603f80000000683ebdffffffee5ebdffffffee5c187ffffff40c187ffffff40ffcf77ff79ff7fcf77ff79ff7fe183ff807e3fe183ff807e110011ffd0200c4288020011800000ffe0000000000000000dfbaefbbf7fefdffff7fefefffffffffffffffffffffffffffffb9fff8ff9fffb9fff8ff8fff80ffe01f8fff80ffe01f8
  | 6, 9 => 0x7fdc0deeffffb77df87e0c57bffe03fffffffffe7c1f067fdfdf200800001fc0010820000fe7800000000fe0000000000ff0bfb1921fe6403ffff40c07f81fc00007e3001ffff80600100000000000800000200100000000000000000000000000fe8247fff3f87ffff77d2bff7fe183fff9fe3fffffff87ffe7fffe0effdfe77f7fbfffd3f3ffff07ffeff3ffffffffebf600004000000620000000000300000000000300000000000110001e0502018028842007b8c0000f820180c000000001d8
  | 6, 10 => 0x7f0047ff60d07f0a617e21fe3f8003ff80683f80001f007e0400128440001204fe5f8b6a00000000000000001f07c1800d893ffffffa85023ffff40804001ffffff800001ffff80001fc28a42087f99047fffd3300fe00000001f8c001fffe1980e7ffffff5cf7ffcf3fcefdfff07fffff8671ffe183e0787e100011ffd02016008842086a000000ffe00000000000000007202210000b0600047ff4080300000000050300003ff80400000008000001000804000280000000000000000000000000
  | 6, 11 => 0x2000000000000000008000000000000000000000000000000040000000000040000000000000000000000000000000000f7ef17c418f7efdf17eeffffffff83e0007fffff83ffffffdddb11ffd035fff7897bbfffefff80ffe01fffff80fffffff9020880000004891fc7e8e0000000000000000007c1f060012000000000000000000000000000000000000000000000009033fa7f0c005893ffffffa84001fc1f06000001ffffff8038b18140002c18b101f100200c18000000140c1800f800100
  | 6, 12 => 0x3fffffffffea1fffffffffea1fffffffffe00fffffffffe0060000100008060000100008030000000004030000000004038b1c5f1062818b1c58000001c1860f800000c18600000000
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x100200c0501c0660140400c02004006
  | 7, 0, 0 => 0xa004090140400c2870000a0240700827098257000010140400c130902370000a00405024020882170000a0240101c0200c2070000a0040501c1f0781d70000a02401008030701b7000090140400c1a0640e700005010030081805c1670000a0040501c0400c1570000a00405010140241370000a0040501c0400c1270000102405010030081170000901c040081003c0e7000010240501c0d0300b70000a0240101c04008087
  | 7, 0, 1 => 0x70100200c390243870000a0040500c370241370000a0040501c030083670000501003008070043570000400803014340241870000a02407010010a83370000901c04008030283270000a00409014070340b70000a004070140400831700009004070100200c3070000a004090140707c2f7000090140400c2e0b42c700004008030040f0241870000a024070142b0982570000901c040082a0280f7000010140402402088297
  | 7, 0, 2 => 0x10240501c030084870000a0040501c0d02c1d70000a00409014030ac1b700004008030143401c4770000a0140701003008467028010240501c0400c02800005010030081800440700005010030040911444700007010020142a02840700007010020040310c3e70000a0040901403008427000070100200c051044070000901c04008030fc3e70000901c040080a03c3d70000a024010103c0ec1e70000a004090140b01c3a7
  | 7, 0, 3 => 0x901c040083f1744d70000a00409014070345c70000a010030085b1682370000a0240400c59160527000010140700c571581670000a024070100200c5570000501c04004091145470000a024070082a14c5270000101403024020842970000a004070100200c5170000901c0400c4f0283470000a004070100200c5070000901c0400c4f0044170000a024070084e0fc4d700001024030084c12c4a700007010030084905c167
  | 7, 0, 4 => 0xa0240700c6e1b40b70000901c0500c1a1b00e70000a02401014040086b70000a0240101c050086a70000a02401014030ac6570000101402028071a46870000a02407008030706770000a024070141f1981e70000a0240100c270086570000a0240101c050086470000101407010030086370000a024010142b188257000010140700c610300b7000010240501c1f078607000070100200c5f1045270000a0100200403178437
  | 7, 0, 5 => 0xa0240501c0d1b40b70000101c050087c1ec2570000a024010142b0947a70000a00405010030087970000901c02028050f4787000010240501c0d02c6070000a024010104f1d44d70000a0240101c2b0947770000900407014040087670000a00404008751d04d70000a00409014140dc2c70000a024010141e01c7370000901003028051c87170000a004090140d1940b70000a02407008010a87070000400c02004091106f7
  | 7, 0, 6 => 0xa0040501c030088770000101407010832181e70000101407010572141670000501c03004091148470000101403008370284770000a004050103b20c1e7000010140701003008827000070100200c0905c6f70000a0240101c1f0f01e70000400803028051c48170000a0040901c0400c8070000a02404004030cc5e70000a0240501c0400c7f7000050100301c130043870000a0240101c051f825700005010030087d028177
  | 7, 0, 7 => 0x10240501c030089170000701002028050f4817000010140300837024247000010240501c0400c9070000501003008070908f70000a00409010030088e7000010240501c1f2181e70000a01407010030088d70000a00409014070108c70000a0240700c5914c5270000a004070142b0941d70000a00409010030088b70000a00405010132282370000a00405010142242c70000901c04028050f47270000a0040901407010887
  | 7, 0, 8 => 0xa00409014070789870000a004090140707c1e7000010140700c0225c9670000901c04008030fc4170000a00409014070ac0d7000090040200c952509370000a00409014072481e70000a0240101c1f078777
  | 8, 0, 0 => 0x24070100200c77028348004050100302402028a4802809004020140301ca38028010240501c032889b8028010240301c020dca18028070100200405024a080280901c03014020049f80240501c0400c9e0289d802809004070109c0f01e8028090140301c020b89b8028010240501c040083a802809004020100309c628028010240400c022684a80280901c04008770042a802801010030089916c2380040501c0300809158608
  | 8, 0, 1 => 0x240400c021e80101441800405010032880901c248004090140400c022c4b080040700c0226c0a024498024070140201003098608028010140400c02024af80040501c0400c02024ae80280400c021e8010145f8024070100300405028ad8028010140701003008ac802405010030082e028ab80240501c0400caa2786080240101c04008032a4a880240101c02014031385d802807014040080900ca78024070140200ca624ca58
  | 8, 0, 2 => 0x280900405010022e4b8801c0400803024010286f8028010140401c02050898024070100200c01014b78028010240501007008b6802809010021e8010142a80280701404008b2024b58024070100200c0a014b4801c0400803014b30284080280900405010030ac628028010140400c0220c7a801404008032940a02418802809004070100500c4f80280900407014b20102b80040501c0400c022181d8004090140300804250608
  | 8, 0, 3 => 0x240400c0200407028c18004090140400cc00b42c8028090100301c022842e8024070100200c012fca880040501c030089b0746080280101c05008be2f49b80240101c020100309c7b8024040080300405160608028090040700c05008bc80240400c021e80a014348028010140400c0901c138028070100200c39024bb80280901c0400ca21dca5802809010030087a2cc528028010240701002014ba802809004070100200c778
  | 8, 0, 4 => 0x240101c04008b21dc6080280101c05010022f8cf80280900407010023384d80240701404008cd330a58004090140400c0232cca8028010240301002014c980280901c0201404004c8801407010030081d0281780280901c02004030e49b8028010240400ca201ca18028090100200c0531cc68004090140700c0207c868028090040701402314258028010240700ca2310c38004090140302802010c280280901c0326c01014598
  | 8, 0, 5 => 0x280901c0400cdb368a58028010140400c02264d9802801014040240704c8a80040501003008d82ac1d8024050100200c010646080240101c05010030ac7b802807010020240500cd7802801010021dc0901c8a80040901403008d63546080240101c0200c0a010d48028090140400ca21e8a5802407014040080a004d38024070140201003004d280240101404008b2028d1800405010030280711cd08024070140200c0a0046c8
  | 8, 0, 6 => 0x140400c02024071686080280901c050109c078a580240100803028042547a80280901c050100239ce680040501c032880a024568028010240500c2c010e5801c04008031dc0a0044080280101c0200c9b390e380280101c050080400ce280280901c042880500c3f8024050100300407028e180040501c040080a024e08004090140700cdf02c6080040700c0202404028de8004050100301c02028dd8028010100301402024dc8
  | 8, 0, 7 => 0x280701404008f0024ef80280101407010020346180280901c0201003004ee800409014070100200ced802801014022c80901cec80240101c02014031749b80040700c0202809158498024070140400c010686080040901c0400c0a008eb80280101407010020341d8014070100302402004ea80140400c0201c47004e98028090140401c02050a580240101404008b21e8608004070140202403028e88028090080301c05130a58
  | 8, 0, 8 => 0x280102405008031e8fb801c050100200c0a024fa80280501c0400c023e4f8801c0500803028011b04080280901002014031d4a5800409014032880a010948004090140700c040080c802809014072880400c268028050100301c02024f780240101c0400803014f68028090140201003004f580280101003024021f4f480280900407008033cc1c8028090140400c023c8f180280901c02014031383f802801014040087a0248a8
  | 8, 0, 9 => 0x28010140401c030250280140400c020280711ca58028010140400cc00241380240101c04008030f0608014070100300817028168028010140400c022642380040501c03009010285680280901c04009003c0778028010140700c02024ff80240101c05008b22989380280102407010033f8da80280901c0501003008fd8028090140700cdf1b40b80140400c021e80a0044080040501c040081d0288580280901404008fc2e0a58
  | 8, 0, 10 => 0x24070100200cce00441802407014040080342d0a80240101c0400803425088028010140700ca226c1d8028090100328801014588028010240501c03008f380280701402010031f0a580280101c02014030250780240501c04004020290680040500c0226c0901c2480280102405010034150480280901c0400c4f004b38028090140301002194a580240501003008070050380280901c04008030fc3980280901c040082a014528
  | 8, 0, 11 => 0x280901c02004050a85380280701002004030e443801c040080302405029128028010140700d114049b80280900407010b22887780280901c0200c9b1dca580280501c0400c01009108004050100301c0222460802809004070080500d0f800405010030280915c18802407008030040514c418004050100301c020250e8028090100200c010150d802807008030040514c5f800405010022c80a024188028010140700c040090c8
  | 8, 0, 12 => 0x28010140400c0704c1d802401014020100302919801c050100200ca5460168024050100301c020291780280101c04008031dc1d802405010032880a004198028010240700c02458c38028010240301c022849b8028010140400899228238028010240500ca2358d580280901c0200cb314c528024070100200cce0283480280501c0400c02454a580280901404009003c07a8028010240700c04009148028070080300405025138
  | 8, 0, 13 => 0x280900407010b236cda80280101c04008ce1341d801407010030080a0251d8028090100200c010151c8028070100200ce30051b802805010032880901c5a802809014030089b1e8a580280101c05008c50941d8024040080301c0512ca58028090140700c040091a80240701002014030fc5d8004090140400c070082d802809010030040516458802801010030080901c5b800405010030087d0291880280101c0301002184778
  | 8, 0, 14 => 0x2809004070100248d228028010240501c030340b80280101c05010030252180280901c04008030f06680280101403010021847a80000a00409014070340b7028010140400c021e81d802809004070080307c7780280901c02014030fc9b8028010240501c1e02c25802407010021dc0a004108004090140400c070092080140700c020740a0046c80040900c0201c040291f8028050100200c072951e80280901c0200c01014538
  | 8, 0, 15 => 0x280901c05008030989b80240701002004050a84180280101c05010024acbd80280102407010a200c3c80280701002004050a85f8014070100328801024388028010140700c024a929802407014040080329460802801024030080501d28802801024070100349d2680040501003024021f460802809004070080400d25802809004022c8070144c801c04008030040517c418024070100200c0a0d00f80280101c040140200d248
  | 8, 1, 0 => 0x280901c040080100d3580280501c03009344cca580280501c0301002025328024070100200c0a0040f8028040080301458024bb80280901c0200c04295318004070100302405029308024070100200c051043480040901c0400c024bc60802405010021e80a004108024070100200cb310452800409014030089b028948028070100200cb317c5280280901c04008034b92d80240701402028010406c80280901c05010024b0f08
  | 8, 1, 1 => 0x280101c05008b20107c80280900407010030ac778028090080326c010145880040501c03010021840c8004090140700d3a01139802809004052c8040086580280501003008074e0bb80040501c03010020301d800405010022c80a01c478028010140400ca201c89802801014030080901d378028010100200c4a0253680280900407008c509c258028050100301c022242e80280901c04008b30a8528028010240501c03008928
  | 8, 1, 2 => 0x4090140700d414e89b802801024050103b0081e8028010240501003009408028010140701003008838028010140700c024d13f8028090140301c020dca580040501c0400c094f93a8024070100200c01014418024070140200d3d4f060802809004020100309c7a80280701002024032d4778028070100200c010145f80140400c02028090601780280101402010031887c80140701003009010043880280701002014030253b8
  | 8, 1, 3 => 0x280101c050080400d48802405010030080151cab80280501c0400c02518bb80040500c02010d5024248024070100200c0a014348028010240500c02514d5802807014042c8010091580280900407008030101c8004070100302402029448028010240400c0250c4a80040901c0400ca2424a88004070100202403029428028010140700c023cc1d80280901c02004030147080280900407008b226c7780280900407014c50ac258
  | 8, 1, 4 => 0x2401010022c8070144b80140700c02004090288480240101002028033447780280701003014020054f80140701003008bb0294e80240701404008035340e8004090140700c020294c80040501c0400d1815c1680280501002024032d47a800409014070109c2181e8028090140700c9e0114b80040501003008230284780040701404008b24601680240101c040080500d4a80280900405010030ac7a80280101c0400803391498
  | 8, 1, 5 => 0x2809004070140400c7e802801010030080716c1d8024050100301cab0041a8028090140701003288a5801c04008030040502552802801024070100200d518024070140326c0a0041a8028010140400cc00b01d802809004070104f00c4d8028010140400ca20247d8028010240501c0400c0280280900405008b226c7a8028070100200c010155080040701402010031f07b8028010240500c650080b80280500c0226c0901c5a8
  | 8, 1, 6 => 0x280900407008030f09b802809004050080301d5680240101c05010022c86080140700c0226c010243880040901c03010021b86080280901c0201403138a580240101c040080a2c955802801008031dc0901cec80240101c0200c0a010958028010240501002550b8802807014030040400953802807008030040514c1d8024010100200c771e860801c04008032940a024498004050100202809214188004050100301c020b41d8
  | 8, 1, 7 => 0x240101c0200ca624c77802809004070080500d608028090140700ca24f53c80040901403008d50295f801407010030081d2946080280701404008be2f4a5802801024070140200d5e8028010240500c025755c802801014040080901c8a802405010030095b318608028010240501c0407c1e80140700c02004090295a80040501c0400c0915c608028010140700c040095980280501c0400c01009588024070140200403029578
  | 8, 1, 8 => 0x2401010020280500d6980040901c0302804009688004050100300889028ab802801014030087a024ec80240701002028050043d802801014030080759d33801c050100200c0a004408028040080301c050056680280901c04008030e4a58024070100300402029658004090140301c02029648028010100200c0901d63802809014030100201d6280280901c0400c05164a58028010240501c033cc2b8004050100201c03029618
  | 8, 1, 9 => 0x40500c0201c0402571800409010030080501d70802809004050080400d6f801c0400803004051041d8028070100200ce438ca580240101c0200c9b424a8802801024070080d014c380040501003008d82ac47802809004052c8070083780280900407014035b80b80040901407010020296d8024070100200c010156c80280901c052c8040086d80280701404004030096b8004090100301c020156a800404008031dc0a024188
  | 8, 1, 10 => 0x28010140400cb8024138028010240400ca21e87780280901c05010b2008668028010240501002034658028070100200cb31481d80280101003009431281d8024070140200c9b3a40e8028010100301c022848980240500c02004070297580140701003008010257480280701002004050a81d8004050100201c030257380240101c04008cd33077802807014020100302572801407010030091805c1680280901c0501002400f08
  | 8, 1, 11 => 0x240101404008cd3307a80240101c050080400d7c80280102405010a200c3b80240501c0400c0a0057b8028010140700c0207c83802801024052880400c628028010240501c04288b2802801024030080501d7a8028010240501003301798028010240700ca20106e80280901c050080326ca5802809014042c8070082e80280101c04008035e0e38028090140400c020ec66802407014040080a2c9778028090040501007009768
  | 8, 1, 12 => 0x40500c02028070246880140701003009822ec6080280100c0201c040258180280901c03008da004538028010240401c0205077800407010030280915c4980280501c0400ca2074a580280101407010030081d80280900404008b8015808028090040200c7701c4c8024050100301c020057f80040901c03028024bc9b802401014040080a00d7e80240700803004050297d802809004070109c078778028090140400ca256cc68
  | 8, 1, 13 => 0x40700803028042541d80240101c0200c04624a880280501c0400d11404a580280900404008031d47780240101c0201003015888028010140400d114047d802801010020140301d878028010240400cdb3687a802807008030140400586802809004040140313c7580280101407010034458580280900407008b20144e801407010030080905c608028010240400c070098480280901c040080500d838028010140700c04008618
  | 8, 1, 14 => 0x280102405010020507a800409014072880400c7b802809004070100200d8e80280100c02024073b05b8028090100301c02284a5802805010030240201d8d8004070140400809630cc8028010240501c030081f80240501003028010681980280901c042c8010145980280901c0200cc430ca5802407014040080a0041080040701404008b20746080040501c04009182141680240101c020140400d8b80280900407008030158a8
  | 8, 1, 15 => 0x280901c020140300599800409010030080501d988004090140701002034608024070140400803198868028010140400803025978028010240500c023599680280101404024021f422802801024040140200d9580280901c040080100d94802801024070101e0159380280900404008ce1d44d802801014040080901d9280280101c02010031f07780280901c040140200d9180240700803004040299080040400c02024070298f8
  | 8, 2, 0 => 0x28090140700c026853c8004070100200c774601680140400c0202407029a080280101402010031f07a8024070100200c0167ca880040701002014031d0608028010240501c02034c580240701003008da00441801c04008030040f0251880240701402010030299e80280900407014046759c80040901407010a200c8680280400c02024070059b80280901c040080500d9a801c0400803014a802417802809004070080400c278
  | 8, 2, 1 => 0x28010240501c9c078f380280501c0400ca2608bb80280901407010020346d8028010140400c07691018004090140700ca226c608028010140700c02025a380280901c03010c3004598028090040200c9b1dc7a80240701003008da02834802807014040080900cb58024010100200c7701c4b802809004070140400c2b8004050100301c130291880240101c04008b20145d801c050100202801040408024070100200403029a28
  | 8, 2, 2 => 0x24070100200c410045280280101407010a22c81d8028070140200c9b2941d8028010100200cb80245b800405010022c80901c2480280101407010026a9a9801c0400c02028091241780240101c040140313c6080280901c020140400da8800405010030087a4601680040501c0202404029a780240101c04008cc015a680040501c0326c0a0245780040400c0201407025a58028010240700c021b89b801407010032880a024178
  | 8, 2, 3 => 0x280101c03009344cc77802407014040080a005b080280101c05010b24450180140701003009010281780280901c04008b21dca580240501c0400d414e8a58014070100300801025af8024050100200ce90640e802401014040080a00cd18024070100200c01015ae800405010030240704c6080040901c040140200dad80040501c0400c0a025ac80240101c04008031dc60802801014040080901dab8004090140400ca2360ab8
  | 8, 2, 4 => 0x1407010020740a0041080280901c05008036d53c80280901c0201003015b48028050100302402005b38028090040700803015b280140400c02004090e0448028010240501c0d0100b8004090140401c020502d80240101c05008031ec9b802809004042c807008a180240101c04008ce1346080040901c0400d414bd3a8024050100200ca50281980280102405010c00502c80280901c0400c01009b180280901403008d6354a58
  | 8, 2, 5 => 0x4090140700c022189b800409014030080a011bf80280101403009344cc7a802809010020140301dbe8004070100200ce3029bd80280901c0400803015bc800405010030080a025bb80280101c0301002015ba8028010140400c02025b980280101c0400c026e1b78028010240301c020dc7780280901404008b21e8a580040501c042880a024858028050100301c13004bb8028010140700c0207c1d800405010030080a025b68
  | 8, 2, 6 => 0x28010240501c0371dc680280901c05010b22a89e80280901c04008030f0a5801c050100200ca50243880140400c02028070248f80040501003008180241680280901c0501003005c5800409010030140201dc4801c050100200c011011880040501c0400c0270dc28004090140701002704cc802801024050102c00dc080280101c020140313874800407014022c80a024568004090140700c02298938004050100202807024698
  | 8, 2, 7 => 0x280101c05010030ac1d802801024070100328877800405010030089908c6080140700c0226c0a0241780280501c030089b608bb8028090100301c020b877802401014022c80a0109480140701003004090e04580240101c0402803009ca80280901402010031882680240101c0501002725c880240101c0200ca62549380280901c05008b20102680040501c0400901028858028010140202407228ec8028010240500c020dc7a8
  | 8, 2, 8 => 0x280901c050080400dd180240101c0501002334cc80280101c05008b226c1d802809014070100200dd080280901404008031987a802809010022c801014588028010240501ca2314258014070100302402029cf8028090100301402005ce802801014070109c20c1e802809004070140313c4e8004090140700c023cc608028050100301c02224a58004090100300807734a88028010240501c03009cc8028090140400c0272cc68
  | 8, 2, 9 => 0x28010140201c04025d880280101c04008be2f4778024050100200c0a005d7802801024070100336cda80280101c0400803015d680240101c05010b25053a8028090040701402315d580280102405010032887a8028090140400c020b87a80240700803028050d078802801024050100200dd480280102407010a23384d80040500c0202404029d380140400c0200409029d280280102403009431304a80240101c0200c4e028a88
  | 8, 2, 10 => 0x28010240501c042701e8028010240700cdf1b80b8028070100200c091dddf80040900c0201407029de8004090140700c02775dc8004090140700c0276c93802405010022c80a0041980040701002014031d05d80040501002028033441d80280900407008ce1384d8028010240501c020349b80040400c021e80a024498004070100200c091ddda80240701002004030143e8028090100301c05005d98004070100200c77074608
  | 8, 2, 11 => 0x280901002004030e47a8004090140700ca20100c802809004040080500c75800405010030087a0746080280101404008be2f47a80280501003024021f4a5802801010030240201cf48004090140701003799e580240101c0401403029e48024010140201003029e3802805010022c80901c5a802407008030040514c6080280901c0400801015e2801c050080300404025e1802801024030080501c4c8028010140400c0901de08
  | 8, 2, 12 => 0x28010240501ca200cf380280901c0201003005f080280101c050080400c7c80240101c04008031747780040501c0400c0a009ef8028090140401c02005ee80280101403024021f4218028010140400ca2264238024070140400c0a005ed80280901c0200c04005ec80040501003008ab025eb8028010140400c027a9e9800405010030080711c168028010140300809011e88004090140301002029e780280101403008073b01d8
  | 8, 2, 13 => 0x409014030080a011f9802809004070080326c77802801010030087a390e380140400c0202407005f8800409010030094312c4a80240101404008b8029f780240101c040080a00df68004090140700c02029f580280900404008030f03b8024070100200c0103c608028010240501c033cc0b8028010100201403025f4802809004070140313c9b8028010240301c04009f38028070100300405025f280280900c0200407015f18
  | 8, 2, 14 => 0x28010140701003009ff80280900407008ce1349b8004070100302402029fe8028010140700c023cc9780040501c0400c0220c608028090140400cc00b82c80040501c0400c024601680240101002014031747a80040501003024021f4298024070100200c0a005fd8004090140701003009fc80240101c040080500dfb800405010030081d028188028010140326c0901c138028090040700c27008df8028010140400803075fa8
  | 8, 2, 15 => 0x1407010030040202a0c802809004070080382cc380040400c02028070260a800404008030240501e09800405010030087a02424801c04008030240502a08802401008030140401e078028050100200c0101d1e802801024050100281a058028090040700803812038024070100200c050d06080040501c020280921456802401010020140302a02800409010030094312860800409010030080501c4b80280901c0500803806008
  | 8, 3, 0 => 0x28090040200cc430c7a80280901c040084d0043980280901c05010022c8a580280901c03010021b8a5800405010030240702a11802801014042c8090087d802805010030080901e1080240101c04008030f0868028010240500c0283cd580280901c04008030e4528028090100200c771e8a580040901407010030086080240101c04008030295580240701404008b23a40e802809004040140301e0e8024070140200c0a0060d8
  | 8, 3, 1 => 0x2807014040080319883801c05010020240102a17801c050100200c090e01780280101c020140400e1680140701003009822ec388024050100200c07296158028010240501c0385213802801014030089b2642380240101c042c80a0092f8028010140700c024d133800407008031dc0a024568028090140400c020eca580040901c0400c0a00a128028010140401c020501d8028090140201003188a580280901c04008030fc778
  | 8, 3, 2 => 0x2407014020040402a1e80280900407010030161d802401014020100301e1c80280101403010021946180280901c05008b24f53c80040500c021e80a024568028010240400c0201e1b80280101403010021941d80280901c0400805868f080280901002014030fc7a8028010240500c0700837802809004050100301e19800409014070100300a1880280901c04008ce0fc4d8028010240501c9c07c1e8004050100202407228608
  | 8, 3, 3 => 0x28090140400c070082e801c0400803014b302438802809004070080400e2380040501003008990281880280701003004051645f80240701404008030297780280101403010d502413802801014070100300a2280280100c0201407026218028010240400c028804a8028090100200c7700458802801014030080901e1f80280901c0400ca22cc528028010240400ca250c4a80280901c04288010142a80280901c05008c5098258
  | 8, 3, 4 => 0x280101c020100309c7c800407010030080a0244980280901c04008010e42a80280101403008d5026298028010240700cdf02c77800409010030080501e28802809004050080400e278028010240500c0b01ce5802809004040080500e2680040501c0400c024622580040400c020240716c248028010240501c0400ca280240101c0501002890cc80240701404009003c0608024070100300405164418028010240501c1f0081e8
  | 8, 3, 5 => 0x28010240500cdf02c7a80280101c05010022f8bd800407014042c80a024578028010140700c02010978028010240500c0400a308004090100301c022842d80280101407010028bcbd80280102403008078b8c3802407010031dc0a0041a802407014040040302a2d80040901407010a22c8608028010140300837024998028010240501c042702f8028010240700cda0122c802405010030080a0062b80280900407010028a84d8
  | 8, 3, 6 => 0x280901c040083f0144d802405010031e80a0041a8024070100200c0a016348028050100201c030263380280101c0400c0202632801c04008031dc0900438802805010030087a0245a80240501003008d82aca5801407010032880a00440801c040080301441024bb8028070100200c05025df80280901c040080100c39802801024050100300a3180280901404008b256cc680240400c0201cab0040f8024070080326c0a0040f8
  | 8, 3, 7 => 0x2404008030143401cab80240101402010031887b8024070080326c0a0143480280501c03010021846d802801024030089b50c4a80280901c05010f000a3c80280101c0400803390e3802801014040080901e3b80280901c0400cda0063a80240101404008038e4ab8028010140700c0220c9b80280901c05010028e2378004090140700c0207c608004090140700c028d89380240101c050080400e35802809004070142b00c258
  | 8, 3, 8 => 0x2801024030080501e4580280701404008031981d8028010240501c030089b8028010240400c029124380240101c05010023364280240701003028050d072801c05010022940a0248580240101c020100309c6080280701002014031d0a58028070140400803904bb80280901c040080500e40802801014020100301e3f80280901c04008038f85280280900404008030f07a80280701404008030063d8004090140700cdf0300b8
  | 8, 3, 9 => 0x280400c020240716c5a8028010240501c049341e8028010240501ca200c1f80280901c05008c5094a58028090040700803310c380040400c020140702a4c8024070140200ce91b00e802801014040080792cbd80040701402010030264a80140400c020280711c8f800409010030087a424a880040700c020240402a49801c0501002024032d460802801024070100336e4880040501c030093302a478028010140400c0901e468
  | 8, 3, 10 => 0x4090140700c023cc9680280101c04008b20147480040501c030080a0265480280901002004050a858802801024050100700a53802404008030280103c19800407014020100302a5280280901c0200c01016518004090140700c0229a5080040501003009180601680280901c040080500c3f802801014040240201c2280280701003004051641d8024050100200c0a0064f8024070140200ca50286c80240701404008f002a4e8
  | 8, 3, 11 => 0x40501c0400c0202a5e802809004070080500e5d8028010240501002970b88024010080302804254948004090140400c0202a5b8028010240300865014c380280101c040080500e5a8028010240501ca22c89b80040701002014031741d8004050100301c0202a5980240501c0301002030a580280901c0301002006588024070140200c0195c9380280101c040080500e5680040501c040280915c858028010240500c02954d58
  | 8, 3, 12 => 0x2801014032880901cec80280101003014070266580040901c0400cdb3686080280400c020240716ca58004070100300809016648028070100200c772941d80040900c02014071304b802407008030140402a6380280900402010031887780280701404008be2d4bd80040501003008070901d80280901002014030066280280901c0400c0128a6180280900407010b20144f802801024030140201e608004090140700c0400a5f8
  | 8, 3, 13 => 0x405010032880a0241880040400c020280711e0a80240101002014031d460802809004070100200c3c80140701002028092141780140701003008010243880140700c02004090e084800409014070100300a6780240101c02010031ec7780040900c020140713060800409014070109c07860802809004070084e00c4d802809004070080309c9b8024070140400c0a0041a80280901c04008030fcb38024010140202803012668
  | 8, 3, 14 => 0x240101c0200c9b1dc608028070100200c0517ca580240101c0400803181f680280901c030086d014c3801407010030080a0266b8028010140400d0101e6a80040500c02028042501d80040701402010031f06080280701402010030981d802809004070141e0116e80280901407010039a66880040501c0400c02181ef80240101c04008032187780240101402010031ec7a801c050100200c090e00e80280701402024032d49b8
  | 8, 3, 15 => 0x28010240501c039d00b8028090140400c0700a7380140701003004090284580280501c0400c0260a7280280101c020100302671802401014042c8070082d80280901c040080100e708028090140401c020502e8028010140401c020266f800405010030080a01e6e8004090140700c020109680240101c0400803424a8801c0501002028030266d8028070100200c77608bb8004050100300901028188028010240400c0250e6c8
  | 8, 4, 0 => 0x280901c05008f00127c8028010240700cdb3689b80280101c05010b200883802809004070080307c3c80240101c0400c4f028a88004090140301c020dc60802805010030080901e7b801c05008030040402a7a801407010030080a9e4bb80140701003008010267880240701404008b2294608028010240500ca20106580280101c04008bd016778028010140700c029d933802801024030100201e75800405010032880a01c478
  | 8, 4, 1 => 0x240701404008a5028108004090140700c02a068080240700803010c30283480040701003028024bc1d80280900405008072c95680280101c05008031f09b80280901c0200c0126dec80280501c0400c02074a580280900404008ce1347a8028010240400c0700a7f8024070140200c0a0067e8028010240700c040086e80040500c02028091581880280900404008031dc7a8028010240501c9c0789b802407010030040202a7d8
  | 8, 4, 2 => 0x28010240501c0300a8480000a004090140707c1e70280501c0400c02608bb8028010240501c0300a838004090140700c0226c6080040901407010030088680040501003008070911880040900c0226c0501c4b8004090140400c02a08ab80280900407008033cc778
  | 9, 0, 0 => 0x2809004070100200c05a2240a01c0501002004033c01d9028070140400803294090764010240501c0400ca20294190280901c0400803004052ce40a00409014030100202c7a902801024070100336c0236a40a0240101c030140400a2c902801014070100300809a1e400028010240501c032889b80280501c0400ca20040960a40a004070100301402026869028010240501003008a21ea40a00405010030087a02423902809004070100200c05a1640501c0400c0200409028389
  | 9, 0, 1 => 0x280101c040080900c05a3640a0040700803014040268c90280101c050080400cc51f240a004070100300805075b7902805010030080901c9916a40a0040501c0300804075299028010240501c030089b85240002809004070100500c4f80280501c0400ca2004092ee40a00409014070109c0081e900409014070100a00803a2e40a0240100803014043107a9028010240501003288070b24010140701003024024046090280101c050080900c04a2a40a00409014070100328a899
  | 9, 0, 2 => 0x280901c050080100c046d640a0040500c0201c043541d90240101c04008031dc0a42640a004090140700c0237c9b90000a0240101c05008c5096009004070100200d09028a890280900407008030100581240a0240101c04008031de8f9028010140700c0201009a3a40a0040501c042880900cbe90280102405010a201c032e2400028010140400c0901c1380280901c0200c0530c014f24090040701402010030946090040501c0400c094040a4ea40002809004070100200c778
  | 9, 0, 3 => 0x2809004070140201003a5240a0240701003004020163a90280900404008070140360240a004050100201c0302693902809004070100233803136400024070140200c0a0046c8028010240400ca20140750e4000280900407010023384d8024070140400803028013a640a014070100300901004bb902801014070080901003a4a40a01c040080300405026919028010140700c020113307640a024050100200c0101e9090040501c030089b0280946240a0240101c05008c500c259
  | 9, 0, 4 => 0x280501c0400c0100809a6e4010240400c021e80a01509901c050100200ca50280905a40901c04008031dc0a0040e9028010140400c0202407a6a40a0040901c0328805010c39004090140400c020287a32a40a00405010030240201c7d90040501c0400c090080aa6640a0240501c030089e0113c9028010240400c020140788240a02405008030040401e98902809004070140200c04a5e40901c050100200ce90280e902801014030080701009a5a40901c05008030040402a959
  | 9, 0, 5 => 0x280901c050100100c02a7e4010240501c03028040093990040901407010030086018240a014070100300982024bb9028010140400c07008c022640900407014020100302a9e902801014030080701009a7640a024070140200c0126e009028090140700c0400801a724010240501c0300804181dd90040901407010030089c18240a0240500c0201c04358a5902809004040080700cfc1de40a0240101c0201003014279004070100200c0a014096f640a00409010032880501c4a9
  | 9, 0, 6 => 0x4090140400c0201cd818240a0240101404008033f07a90280901c05008034f4044f240a0140700c0226c010258290040501c0400c090080a4fa40a0040701002024032f47790280101c040080901403a8a409004070100200c0a0150890280101c0400c0901402a864010140700c0202804026a090240101c050080400cc51824090140400c021e80a0040e9000010240501c030100203200a0040501c0400ca202501901c050100200c0a004e910240a00407010022c809014e39
  | 9, 0, 7 => 0x40501c030080a0251815a40a004050100201c03026a590280501c030089b004092ee400028010240501c03008f38028010240300807010058ba40a004090140301c020b09b9004070100200c090140aa9240a0140701003004022a81d9028010240501ca20100309640a0240101c0200c0526e0390240701404008030280142e400028010140400c022642380280101c05010022c8090764010240501c03028025049b9028090100200c770040731a40900407014020100302aa39
  | 9, 0, 8 => 0x2809004050080700cb826e409014070100302802006a99028090140400c020040756e40a0040901c0400c05008da90280101c040080302477aa240a0040501002024032f47a9004090140700c020280494240a004070080302405012a790280900407014020100375640901c0500803004044f06090280901c050100200c1e29640a0040900c0201407012a69028010140701002024036aa409004070080302804298779028070100200c01014b307640a0240101c05010030096e9
  | 9, 0, 9 => 0x28010100200c071280938e40a0040900c0226c0501d439004090140700c020109318240a004070100201403024749004070100200c090140aab240a024050100301c02300a590000a004070100200c770760010240501c0400c0a0093a90240101404008032e00a2ae40a0040501c0300809011349028090140400c021e80131a40901c05008030040402aab90240101c04008030147718240a024070100200c01016aa90240101c0400803014a818240a0040701402024032f89b9
  | 9, 0, 10 => 0x280101c0400c0900805ac640a0240101c0200c9b014c390000a02407008030040514e0010240501c030080402a81901407010030081d028013a640a0040901407010a200c9c902807014040080900403ac240a024010100200c7701c7a90280900407010020140313640a0240501c0400c02278a590280901c050080100c04abe400004090140400c070082d80040901407010030080aaba40002801010030080901c5b80280901c050080400c01ab640a024070140400803270669
  | 9, 0, 11 => 0x901c050100200ca518200102405010032880a01cd89028010140400c0201c1da6a40a004070100200c77024e490280900405008b201c0435a40a00409014072880400cc59028090140400c0256c0731a40a024010100201403338759028010240501003008070ee400028010140400c021e81d802801024030089b0140712a40a024070100200c010145290040701404008b20280905a4010240501c0400c0202ab2902809004050080400c0718a4010240501c0400ca2028609
  | 9, 0, 12 => 0x240101c0400c0a01402ae6400024070100200c0a0040f8028010240400c0700805ae240901407010030040202ab790280901c05008030113d29640a0040501c03024024049b9028090140701003004a29a640a02405010020040700eb690280101c050080400c09ad640901c05008030053c0289390240101c040080a00ccc1de4010140400c02028072ac47902801024050100301c02ad240901c0501002028013a41090280102405010030087a1ea40a024070140200c04296b39
  | 9, 0, 13 => 0x28090100200c0701401af64090040701402010030287b9024070140400803004a518240a024070140200c01012bc9028010240501c030100202e40a0040901c0400ca20147790280101c0400c0500809aee40102407010032880a014a8902809004070080301077aea40a024070140400803400a5902801010030087a0240539240a0040901003008051ea4490280901c0500801010039f240a0240101c05008030949b9028010240501c0400c0228a40a0240501c03288010113c9
  | 9, 0, 14 => 0xa0040501c0400c0220e00a024070140400803006c4902801024050100300807b0e40a024070140400c02296c290040501c0400c090091118240a0240101c05010b20081e902809004070080301404312400024070100200c010144180280901c0400c02368012ce40a0040501c040240200ec1900409014030080a01c04b024090040501002028033307a90000a01c04008030040517e00a02401014040080700ebf90280501c0400c02024013e640a004090140201c0400ebe9
  | 9, 0, 15 => 0x280101c0400c05008da07640a00409014030082c010d590000901c0400803028050d200a0040501c0400803075aa902801024050100301ca241240102405010030280700aca90280901c0400801014030aa400028010240400c0250c4a8028070100200c0901401b2640a00405010022c80901c99902407014040080a00ccd29640a0040501c030240400ac8902801014070100302402b1e409004050100201c0302ac6902801024070100500803b164010240501c032880a010939
  | 9, 1, 0 => 0x28010240501c030089c26e4090140400c020040702ace9004090140700c020109b18240a024010140200cb8010d590280901c05010b20040227a4010140701003028024e81d9028090140701003004a29a2409004070100200c05182cd902809004070140200c04b324010240501c0400c0202886902801024070100336c0536a40a0240701003004050085990280900405010b201c0230240a0240501c0300402012cb90040901c0400c05008db18240a0140400c020040756c1d9
  | 9, 1, 1 => 0x28010240501c0400c02a3e40a0240101c04008031dd229004090140400c0201c0a32a4010240501c0400c0a00ad3902809004070100500c02b4a40a0040701002014031341d9024070100200c0a014010d24010240501c030089b0286090280900407014040080300e40a004070080301404026d190280901c04008032cc0114a400028090140701003288a58004090140400c070080ab424090040701002014033386090000a00409014070100300a00901407010030040202acf9
  | 9, 1, 2 => 0x280901c050100200c0100640a0240100803014c301cd590240101c050100200cb218240a024070140400cf00089e9004070100200c0938c0a2a240a01c0400803004051481d9000090040701404008b218200a02407014040080329638901c050100200c013a4094624010240501003008d801cab90280101c0501002024034ae40a02401014020100301ed59000090040700803028042560010240500c0226c0a01cd890280901c040080101403b52409004070100200c0a015099
  | 9, 1, 3 => 0x28090140700c04008df29640a0040501c0400ca20251190040501c030080a0100991e40a004070100200c770241d90280901c050080326c014f240a01c050100200403026da90240701404008030280103a40501c0400c02004092ec389028090140400c0101c02b664010240501c0400c0a009e590240101c050100200c60b6240a004070100200c091ded79028010240500c070100283e4010240501c0400c02182d690000a00405010020240722a00a02407014022c8010113d9
  | 9, 1, 4 => 0x40901403008070100ab8a40501c0400c020040902ae19028010140701003008a207640a00405010030080708c1d90240101c0200c0a01005b8240a024070100201403006df902809014070100300402b7a40a024010100201c0500edd902809004070140201003b724090040400803014a801cab9028010240501c03010a271a40a0240101c0200c9b01477902809004050100201c033f2409004070080326c0a014a890040501c0400c0a00809b6e40001c050100200c0a004408
  | 9, 1, 5 => 0x28090140400c020040731a40a004090140700ca20109b90280901c0501002004038de40a0040501c0400d110090190280501c0400c020041d3e640a00407014040080900cbd90280501c0400c02024013e240a024040080301c05004c79028010140400c021e80907640a004050100301c02026e69004090140700c0226c0a24e40a01c050100200c09296e59028010140700c040080b07640901c050100200c0102ae49028010240500c0201c9bb8e40a0040901c0400ca2014db9
  | 9, 1, 6 => 0x280101c040080301409aa240a0240101c02014033384e9004090140700c0a01002bbe4010240501c0400c0a28aee90280501c0400c0900801bb64010240501c030080a010a69028010140400c0202407bb240a0040500c020240401eeb9024010100200c0a01407baa40102405010032880a01cab902809004070080301077ba640a024070100301402006e8902809004050080700c04b9e4010140400c020280901deb90040901407010030280279a4000280901c0501002400f08
  | 9, 1, 7 => 0x240101c0200c0a010a625640a0040501c0400c02026f490040501c0400c020240a70e40a00409014070100328ad690040501c040080a02403bce40901c050100200c0a006f290280900407010031340236a40a024070140400900004f09028010240501c04288032ca409014070100302802504a59028090100200c0701401bc6400028010240501c04288b280280901c050080400cc509a40901c05010020040302af090000a024070140200c9b29600a01c050100200ca5025829
  | 9, 1, 8 => 0x4070100200c0a0150907640a0240501c0400caa0089e9024070140200c0a004041b240a0040501c0400c020768f90280101407010030080920e40102405010030080a01cb09004090140300807010d518240a0040500c020240401e2990040901407010030080abda400028010140700c04008618004090140700c0a00804bd640a01c050100200ca5024bb9028070100200c010140917e4010240701003028025052f9028090040701402314040964000280101407010030081d8
  | 9, 1, 9 => 0x280101c040080500c09bea40a024040080301c0550ca590040701404008b20280946240901c05010020280100c109028010240700c04008df1ba400028010240501c030081f8028010240500c02010d61ea40a0040501c03024024449b90000901c0501002028010420010240400c020140702af9902809014030080101c04be240a0140700c0202404006f790280501c0400c01008aa45640a024010140200cc501cd590280901c050080326c0129640a004090140400c0201c7a9
  | 9, 1, 10 => 0x240101c040080500cce17640900404008030280501f0090000a0240101c020100309e0010240501c030080a011db902809004070080500c04bfe40a004070140400803026fe902801014040080700cfc07640a0040901c030140236c9b902809004070100200c1e1de40a01c050100200403026419028010140400c020247a7a640a00409010030080501e6c902809004070100200c05bf640a00409010030080701644902809004070100300877bf240a0240101c0400803016fb9
  | 9, 1, 11 => 0x28010140400c022640708e40a0240701404008012c8e690240501c0400c0a0080127640a0240101c02014033389b9028010240400c07008c01de40a0040901c0400c0500a489028010240501c030089b26e40a024040080301c05128a590280101c04008032f40538e4010240501c0400d410093a9028010240501c0300804c0e40a00405010030240726413902801024050100301c02c0a40a0240501c042880100cf09028010100200c770240726640a0140400c0202407007019
  | 9, 1, 12 => 0x407010030080a0240512640a00405010030087a0249990280102407010030080549e40a0040501003024024047d90000a01c0501002024032d600a0140400c02004073181d9028010240501c03008043ce40002809004070140400c2b80240501c0400c01008aa18240a0040501c03008040270790280101407010030240261640a0240101c04008032703c9028010240700c0500804c1a40a0240101c0200c05012ba90240501c0400c010080ac1640a0040500c0202407013049
  | 9, 1, 13 => 0x280501c030080102404c3240a0040901c0400c02015269028010240501c030089bb5a40a0040701002014030270b90040501c030080a010a607640a0040701003014020270a900409014040080a01c03c2640a004090140400c023007a90040901c0400c050080ac224070140400803028010244090240101c05010b20280250640901c0501003028010081a902809004070140200cb226e40a0040501c0328809011339028010240500ca201c0435640901c0400803004052cc609
  | 9, 1, 14 => 0x280101c05010022c8092fa40a0240101404008b201cb890040701404008092f40a33240a0240701404008012c8e79004090140700c020280477240a0140700c02004090130f90280901c0200c010113d1de40101407010030080a075c39028070140400809004033be409004050100201c0302b0e90000900405010020280334600a004090140400cc001c2c902807014040080900c012d64000240101c04008031dc6080280900405010b201c020b240a0040701002014030270d9
  | 9, 1, 15 => 0x28010240400c020147a90e409004070100200c0a0171590040501c0400c0a02402c5240102405010030080a1e8cb9028010240501c030081e3ce4090040701002028030171390280900407010020140348a40a0040501003008071e81d90280901c0400c0101402c4a40a024070100200403400779024070140400803004e918240a02407008030040501053902809004070080501003c4640a0040501c0400c02027109028010140700c02404044ce401024050100301c020282d9
  | 9, 2, 0 => 0x2809004070080400c05c6a40a0040501c0400c020241d90280901c050080400cc5296400004090140700c0229893802809014040080100d001ea40a0240101c05010022c99c90280101c040080301409b5e40a0240701003004020171990280101c0400803014e407640901c050100200ca50286090240101c040080a00ccd1de40a004050100201c030271890280901c050100200c9c29640a0240500803004044f47a902809014040080700c01c5e40a00409014030080401f169
  | 9, 2, 1 => 0x28010240400c0250c0712a40102405010030080a01cb19028070100200c0101409c7640901c0400803004050284190040501c040080a0251821640a0040501003008091e9ea9028010240501c030089b84e40901c050100200c011810b90000a0040901c0400ca21de0090040501002028033347a902809010030080101c05c7240a0040400c02024072645b9024070100200c010140ac6e40a00409014070100237c0d9028010140700c040080918640101c0501002028033301d9
  | 9, 2, 2 => 0x280900407008033100530e4090140400c020040756c6090040901c0400c05008da18240a0140700c020240400722900405010030080901c0ac8640a0240101c0200c05012e99000090040701404008cd33200a02404008030040501f2090040501c0400c0202809c7e40a0240701003004052cc599028010140700c02024049da40101c04008030240502b1e902809004070140400c0267640901c0400803028052a0a590280900407014022c8040964010240500c02010d5028ab9
  | 9, 2, 3 => 0x2801014070100300809c9a40a0040901c030100237c7790040901403008070100ac9640a004090140700c020100490280102405010030080701e40002801024070100336cda80040901407010030093a18240a02407014040080100d2c90000a004090140400ca21ea00901c05008030280424ca5902401014040080700c0ac924010140700c02024044d060900407014040080900c0a63240101407010030080a027239028010240400c0700805286409004070100202803014a99
  | 9, 2, 4 => 0x28010240500c04008df1ea40a0240701402010030072990000a0240101002014031d600a004050100300807025e99024070100200c010145218240a01c0400803014b3024bb902407014040080100c0aca240a0040501c020240400f2790280102405010070080305240901c040080302805004bf9028010240501c0202c0309640002801024030080501c4c80240101c040080500c4d182400028010240501c042701e8004070100200c77028094624090040701404008030280a9
  | 9, 2, 5 => 0x4090140700c024e80424e40a0240101c0400c021df2e90280101407010030081d076401024050100301c0202b2d90240101c040080a0140369a40a0240501c03010020072c902809004070100301402bf24000280101c050080400c7c80240101404008b2028073624010240501c030080402a809028010140400c0202407cae40a024070080326c01014b390280101c0400803014e307640a0240101c05008b2010c5900405010030087a028094624010240400c020140702b2a9
  | 9, 2, 6 => 0x28070100200c77024012ee4000040501c0400c0246016802801024050100301c0230240a02401014020100301f319028010240400c070082c1de4010240501c0400ca20293a90280900407010022c8051de40a00409014070100200f30902801024030080701005cbe4010240501c030100237c0c9028010140700c020249ba3a40a014070100302402444a59028090140400ca20040756e40002809004070080326c778028070100200c770240160a40a0040901407010030081e9
  | 9, 2, 7 => 0x280901c0400ca20040514a40a00409010030140201c9a902809004070080400c05cd240a024070100201403338a590280102405010030082c1ea40a0240500c0201c040073390280901c05008030109b2964090140400c02028070073290040901407010030089c21a40a0040701002024032f877902809004040080700cb81de4010240501c0400c0a28aae9000010240400c020140712e0090140400c0201cab004e99004090140700c0a008048da409004070080301404310609
  | 9, 2, 8 => 0xa0240701404008b229600a0240101c0200c0430c779028010140300807010d60764010140700c020240402b36900409014070100a0080370640a00409010030080701643902809014030080701001cd640a01407010030080102672902801014040080900cbe1ea40a0240101404008032e07a9004090140400c0201c0a32e40a024070140200c01012b39000010240501c0400c0218200101407010030081d0281690280900404008031dc0750e4090140400c02028072aca59
  | 9, 2, 9 => 0x28090040200c05010c31ea40a024040080301c05007399028010240500c0201c0465a40a0240501c040040200f3890280901c0200c0501001cde40a02407014040080100d009028010240501c0400ca228a40a004090140700c020101f9028010140400c023000926640a00405010032880901c2390280901c050100200ca5b5a400028010140700c024d13380280900404008031dc0712a40501c0400c020040902a799028010140400c09008076924010240501c0400c021828f9
  | 9, 2, 10 => 0x4090140400c024e8072ae4010240501c03028024e89b9028010140400c0201c097aa4070140400803028010273b9028010140400c024040708e40a0040501c030089b0253490280101c05010b20240244640a01c0500803004040273a90240101c05010020280333640a0240500c0226c0101d5b9028010140400c0201c1dcae40a024070140400c0100ac290280901c05010022c80129640901c050100200c010386090000a004090140301c020de00a004070100302402404779
  | 9, 2, 11 => 0xa00409014070100328a00a0240101402010030947a902401014040080a00c07cfe4010240501c0400c02181e6902405010030080101cc6182400028090140400c070082e80280901c050100200cf029640101c0501002024032f46090280900407010b20140236e40a0240501c03010020046d9028010140400c09009011ea4010240500c0201c0402b3e90240101c050080400c0acf640a0040501003008072641d902809004070100200c7748e40a0240400c02004070173c9
  | 9, 2, 12 => 0x2809004070140201003d064090140400803028013a419902809004070100200c9c1de4010240400c020140702b4090040901c0400c0a008054be4010240501c0300804298609024070140200c010100a95e40000407010030080a024498028010240501c0400ca2a3e40a0240101c04008b2014ce90280901c0200c9b0040514a40a0140701003004022781d90280101c0400c020141d6e240901c0400803014a80040e9004090140700c020289ba0640a004050100301c2c025019
  | 9, 2, 13 => 0x2809004040080500c07d1640a0240101c0200c9b014c49028090140400c020040772e4010140400c0202423028ab9028070140200c0101009d12401024050100300807180b09028070140200c010113d0764000280901c040080100c3980040501c0400c024600905a40a004090140700c04008df90000a0040701404008be2f600a02401008030140401f439028090140400c0100807d0a40a0140700c02024044cca590240101c04008031dc0a18240a0240500c0201c04354a59
  | 9, 2, 14 => 0x28010140700c024d0094ce40a014070100300801025829004090140700ca20280429a40a0240501c0400c022a8a59028090140200c010113c1ea40a0240101c0400c0500b2e900405010030080a0240706240900407008030280424c779004090140700c022980a24e4010240501c03008a6010939028010140700c0400809d1a409004070100200c77028a89028010240501c0400c020be4000280101c0400803390e380280102407010050080364e40a0240700803004044f0779
  | 9, 2, 15 => 0x240701404008032940a3a640a00409010030080501d439024070140200c9b0280103a400028090040700803310c38028010240500c0201c04d2a4010240500c0201c0402b49902809004050100201cb2d2240a00407014040080900cbe90240101c05010023340a3324070140400803024bb0280e902801014030080901c993b240101c0400c02028090174790280501c0400c02004092ee40a004090140700c0226e8f900409010030087a028052a2400028010240501c030089b8
  | 9, 3, 0 => 0x2809014030089b0040731a40a00409014030080b01cd590280101c050080900cbd26e40a00409010030080501c4a90000a0240701002014030fe0010240501c042880a00ccc90280900407008030140430e40a004070100201403338749028050100300807318092ee40a004090140400c07289059028070100200c0900405d3640a004070100328809014e49028010240400c0700805d3240a0040900c02014070104c9004090140700c020106077240a0240101404008072cb4b9
  | 9, 3, 1 => 0x409010030080501c0a12e40a004070100200ce4024e39028010140400c070082c07640a024070100301402368a590280901c04008b2004052ce409004070140400803029c990240101c04008033380a2a240900407010020140302b4e90280900407008030109b1de40a0240101c04014033384f90280901c040080500c010fe40a0040701404008be024bd90280101404008072e0092f64010240501c030089b028a690280101407010030240240640900407014040080a00e249
  | 9, 3, 2 => 0x240701404008033c00a3a640a0040700c02024040175190040901407010030080a182400024070140400c0a0041a80280101c0400ca20240538e40a0240101404008032c87a9004090140700c020280477640a0240101c05008042ca979028010240501c0400c0227240a0040500c0201c040275090280901c0200c0430c012ce40101407010030080a075c290240701404008b2028013a64010140701003008091832390280101407010030081dd3e40a0240101c04008031ded69
  | 9, 3, 3 => 0x2801024050100301c025e64010240501c030080a0109390280102407010030780536a4010240501c0400c02078609028070100200c0901401d5640a0240501c030100202ca590280101c0400c0900805d52409004070100200c0a014a8902809004050080400c07d4e40a0240501c0400c02288a590280901c0500803004044f240a0140400c020040901f529028010240500c07008040de4010140400c0201c990291890000a0240101c04008030f2000014070100300801024388
  | 9, 3, 4 => 0x280501c0400c020040951a40a024050100201c033f0a59028010240501c030089c07e40a004090140700c1e0100b9028010240400c023680712a40a01c050100200403027599024070100200c0a01509296409004070080302805013589028010240400c0500807d5e40a004090140328807010d69028090140701003008019a240a004050100301c020275690040501c0400ca20280905a4010140400c02028094601890280101c05008b2024044d24000240101c0400803424a88
  | 9, 3, 5 => 0x2809004070140400c020ae4010240501c030080a26e8090000a01407010030081d29600a0240101c0200cc4010c39028010240501c0400c02b5a40a0240501c040040200e3c90000a0040901c03010021ba0000280900404008031dc7a80040501c0400c0a00809d6e40a004090140700c020109b902801010030080901c0516e40901c04008030040502b5a90280901407010032880127a40a004070100200c051dc1d9028010240500c04008df196409004070140400803334609
  | 9, 3, 6 => 0x24070140200c0a00404d8240501c0400c02004092ec6090000a0140701003009822ee000004090140700c0226c6080140701003008010258218240a0240101c02010030175f9000010240501c0400c0221a00a004070100200c0901549900409014030080a010072524010240501c0400c0202b5e900405010030080901c9909240a0040901407008df00cc590280901c050080300404d7640a024050100200c0101f5c902801024030080501d4313240a004090140700c020789b9
  | 9, 3, 7 => 0x409010030080501c4a18240501c0400c020040902b62900409010030080501d4318240a0240400c021e8010145290040901407010024e80333240a00409014070100300a4d9028090040200c0501007d864010240400c020140750c4b9
  | 10, 0, 0 => 0x2809004050100201c033f240901c050100200c0a0040e90240101c040080302805426400028010240501c0400c0280280900407008030140431240a004090140700c040080b9028010240501c0400c0228a40a024070100200c01014529028090040701002014031364010240501c0400c0a0093a9028010140700c02024044d240a02405010030080101d5b90280102407010030140236a40901c050100200c0a004e990000a0240101c04008031de00a024070100200c01014b39
  | 10, 0, 1 => 0x280501c0400c02004092ee400028010240501c030089b80280501c0400c020040960a40a004090140700c04008df90000a00409014070100328a00900407014040080a00ccd90280901c05010020040340240000409014070100300860802801024050100301c0230240a0040901407010030081e90280101407010030080907640a004090140400c0201c7a90000a0040501c0400c020760010240501c030080a010a69028090140400c020040731a40a00407014040080900cbd9
  | 10, 0, 2 => 0xa004090140700c020109b9004090140700c020280424e409004070100200c0a014a890280901c0500803004044f24010240501c0400c02028609028010240501c0400c0227240a0040501c0400c09009019028010240400c020140712a40a0240101c0200c05010c39028010240400c020140750e40a00407014040080900cbe9
  | 11, 0, 0 => 0x28010240501c0400c028
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 6 => 64
  | 7 => 84
  | 8 => 84
  | 9 => 94
  | 10 => 94
  | 11 => 84
  | _ => 0

def idWidth : Nat := 10

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 194 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dA : Nat := 0x1fffffffffffe000000000000ffffffffffff

def dG : Nat := 48

def setA (xs : List Nat) : List Nat := xs.map (moveBits dA dG)

theorem runA {s ws} (h : NatRun (mask 97) (goal 97) s ws) :
    NatRun (mask 97) (goal 97) s (setA ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk zs) 17 0 (NN s)

def ori (zs : List Nat) : List Nat :=
  let az := setA zs
  if hk zs ≤ hk az then zs else az

theorem ori_ok {u ys} (h : NatRun (mask 97) (goal 97) u ys) :
    NatRun (mask 97) (goal 97) u (ori ys) := by
  unfold ori
  dsimp only
  split
  · exact h
  · exact runA h

def poolG : List Nat := [100250221231048801, 85641056362794085, 31545032786988181, 51864007668288661, 51811282599382117, 80011491320890514, 25915570824250466, 74329266781783139, 74329215292507283, 46234488756393115, 100224959316595819, 85593777404741778, 31603306844538978, 74329220650780819, 74329220600399971, 25915570784454754, 80011491381708946, 74376540449769569, 20280516823582817, 79958720136710243, 74334718211016851, 31597860834348194, 85588228315434098, 85588233628519521, 31597814708587617, 31597800758285411, 85588219719170195, 51836505859130514, 51889334007202914, 74329220600411235, 74329220650792083, 74329234560092257, 74329234610473057, 74329209863034979, 74329261452925075]

def Z (s : Nat) := bar 97 S NN idx ori poolG s

private theorem coveredBySix {f : ℕ → Bool} {n : ℕ}
    (check : ∀ j : Fin ((n + 5) / 6), span f (min 6 (n - j.val * 6)) (j.val * 6) = true) :
    ∀ i < n, f i = true := by
  intro i h
  have jBound : i / 6 < (n + 5) / 6 := by omega
  have base : i / 6 * 6 ≤ i := by omega
  have next : i < i / 6 * 6 + min 6 (n - i / 6 * 6) := by omega
  exact span_ok (check ⟨i / 6, jBound⟩) i base next

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checked (s : ℕ) (hs : s ≤ 11) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · simp [NN]
  · exact fun i hi => span_ok (show span (Z 6) (NN 6) 0 = true from by decide +kernel)
      i (Nat.zero_le i) hi
  · apply coveredBySix
    intro j
    fin_cases j <;> decide +kernel
  · apply coveredBySix
    intro j
    fin_cases j <;> decide +kernel
  · apply coveredBySix
    intro j
    fin_cases j <;> decide +kernel
  · apply coveredBySix
    intro j
    fin_cases j <;> decide +kernel
  · exact fun i hi => span_ok (show span (Z 11) (NN 11) 0 = true from by decide +kernel)
      i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 97 s poolG xsG || found S NN idx s (ori xsG)

theorem rootChecked : span RootG 5 7 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : NatRun (mask 97) (goal 97) s xsG) : False := by
  have hmin : 7 ≤ s := by
    have hl := run_len h
    change 8 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (Run.perm hr.2 (ori_ok h))

end CoreTable7402_aux

theorem CoreTable7402 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)) t → 12 ≤ t := by
  intro t ht
  by_contra hsmall
  obtain ⟨C, hfan, hsize, hev⟩ := ht
  apply CoreTable7402_aux.mainG CoreTable7402_aux.noRunFull
  exact ⟨C, hfan, by omega, hev⟩

end

-- From .pnp-tools/Theta9433TinyMajority.lean
section

namespace Theta9433TinyMajority

open CoreTable7402_aux

open Cactus10440Floor

def reaches (k : Nat) : Nat → List Nat → Bool
  | 0, ws => ws == [goal k]
  | s + 1, ws => next (mask k) (s + 2 - ws.length) ws (reaches k s)

theorem reaches_of {k s : Nat} {ws : List Nat}
    (valid : NatRun (mask k) (goal k) s ws) : reaches k s ws = true := by
  induction s generalizing ws with
  | zero => simp [reaches, zero_done valid rfl]
  | succ t ih =>
    exact next_complete valid t rfl ws (List.Perm.refl _) (reaches k t) (fun _ h => ih h)

private def rows : List Nat := [0, 1, 2, 4, 3, 5, 6, 7]

private theorem encodeInputs :
    (List.ofFn fun (i : Fin 3) => (fun x : Fin 3 → Bool => x i)).map (fun a => encL a rows)
      = [178, 212, 232] := by decide +kernel

private theorem encodeMajority : encL majority rows = goal 4 := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 2000000 in
private theorem noSmall : ∀ s : Fin 4, ∀ zs ∈ ([178, 212, 232] : List Nat).sublists,
    reaches 4 s.val zs = false := by decide +kernel

theorem lowerMajority : Lower 4 majority := by
  intro s fit
  by_contra tooSmall
  obtain ⟨t, can, ws, kept, run⟩ :=
    exists_run majority ⟨fun _ => false, fun _ => true, by decide⟩ s fit
  have masked : mask 4 = 2 ^ rows.length - 1 := by decide +kernel
  have sym : NatRun (mask 4) (encL majority rows) t (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn 3 => encL a rows) (inv' := fun n => n ^^^ mask 4)
    (fun a => by rw [masked]; exact encL_inv a rows)
    (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) run
  rw [encodeMajority] at sym
  have found := reaches_of sym
  have belongs := kept.map (fun a => encL a rows)
  rw [encodeInputs] at belongs
  have contradiction := noSmall ⟨t, by omega⟩ _ (List.mem_sublists.mpr belongs)
  rw [found] at contradiction
  cases contradiction

end Theta9433TinyMajority

end

-- From .pnp-tools/Theta9433Control.lean
section

namespace Theta9433Control

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) ||
    (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) ||
    (x 3 && x 8) || (x 5 && x 8)

end Theta9433Control

end

-- From .pnp-tools/Theta9433J.lean
section

namespace Theta9433J

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers.PermInputs CircuitHelpers.Readers

open Cactus10440Floor

open Theta9433Control (target)

def triangle : List Edge := [(0, 4), (0, 7), (4, 7)]

def leftStem : List Edge := (0, 6) :: triangle

def rightStem : List Edge := (1, 7) :: triangle

def rightTail : List Edge := (1, 5) :: rightStem

def stems : List Edge := (1, 7) :: leftStem

def leftStemRightTail : List Edge := (1, 5) :: stems

def J : List Edge := (2, 6) :: leftStemRightTail

theorem triangleBound : Lower 4 (graph triangle []) := by
  intro s h
  let π : Fin 9 → Fin 3 := ![0,0,0,0,1,0,0,2,0]
  have eq : (fun x : Fin 3 → Bool => graph triangle [] (x ∘ π)) = majority := by
    funext x
    simp [graph, triangle, π, majority, Bool.or_assoc]
  exact Theta9433TinyMajority.lowerMajority s (eq ▸ relabel_size π _ s h)

private def bits (n : ℕ) (i : Fin 9) := n.testBit i.val

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem leftStemBound : Lower 5 (graph leftStem []) := by
  refine lower_one (p := 6) (b := false) (by decide) ?_ ?_ ?_
  · exact ⟨bits 1, by decide +kernel⟩
  · exact ⟨bits 0, bits 17, by decide +kernel⟩
  · have eq : ∀ x : Fin 9 → Bool, cofactor (graph leftStem []) 6 false x = (graph triangle []) x := by
      decide +kernel
    rw [funext eq]
    exact triangleBound

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem rightStemBound : Lower 5 (graph rightStem []) := by
  refine lower_one (p := 1) (b := false) (by decide) ?_ ?_ ?_
  · exact ⟨bits 128, by decide +kernel⟩
  · exact ⟨bits 0, bits 17, by decide +kernel⟩
  · have eq : ∀ x : Fin 9 → Bool, cofactor (graph rightStem []) 1 false x = (graph triangle []) x := by
      decide +kernel
    rw [funext eq]
    exact triangleBound

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem triangleOr1 : Lower 5 (graph triangle [1]) := by
  refine lower_one (p := 1) (b := false) (by decide) ?_ ?_ ?_
  · exact ⟨bits 0, by decide +kernel⟩
  · exact ⟨bits 0, bits 17, by decide +kernel⟩
  · have eq : ∀ x : Fin 9 → Bool, cofactor (graph triangle [1]) 1 false x = (graph triangle []) x := by
      decide +kernel
    rw [funext eq]
    exact triangleBound

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem rightTailBound : Lower 7 (graph rightTail []) := by
  refine lower_two (p := 5) ?_ ?_ ?_
  · exact ⟨bits 2, by decide +kernel⟩
  · intro b
    cases b
    · exact ⟨bits 0, bits 17, by decide +kernel⟩
    · exact ⟨bits 0, bits 2, by decide +kernel⟩
  · intro b
    cases b
    · have eq : ∀ x : Fin 9 → Bool, cofactor (graph rightTail []) 5 false x = (graph rightStem []) x := by
        decide +kernel
      rw [funext eq]
      exact rightStemBound
    · have eq : ∀ x : Fin 9 → Bool, cofactor (graph rightTail []) 5 true x = (graph triangle [1]) x := by
        decide +kernel
      rw [funext eq]
      exact triangleOr1

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem stemsBound : Lower 6 (graph stems []) := by
  refine lower_one (p := 1) (b := false) (by decide) ?_ ?_ ?_
  · exact ⟨bits 128, by decide +kernel⟩
  · exact ⟨bits 0, bits 17, by decide +kernel⟩
  · have eq : ∀ x : Fin 9 → Bool, cofactor (graph stems []) 1 false x = (graph leftStem []) x := by
      decide +kernel
    rw [funext eq]
    exact leftStemBound

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem leftStemOr1 : Lower 6 (graph leftStem [1]) := by
  refine lower_one (p := 1) (b := false) (by decide) ?_ ?_ ?_
  · exact ⟨bits 0, by decide +kernel⟩
  · exact ⟨bits 0, bits 17, by decide +kernel⟩
  · have eq : ∀ x : Fin 9 → Bool, cofactor (graph leftStem [1]) 1 false x = (graph leftStem []) x := by
      decide +kernel
    rw [funext eq]
    exact leftStemBound

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem leftStemRightTailBound : Lower 8 (graph leftStemRightTail []) := by
  refine lower_two (p := 5) ?_ ?_ ?_
  · exact ⟨bits 2, by decide +kernel⟩
  · intro b
    cases b
    · exact ⟨bits 0, bits 17, by decide +kernel⟩
    · exact ⟨bits 0, bits 2, by decide +kernel⟩
  · intro b
    cases b
    · have eq : ∀ x : Fin 9 → Bool, cofactor (graph leftStemRightTail []) 5 false x = (graph stems []) x := by
        decide +kernel
      rw [funext eq]
      exact stemsBound
    · have eq : ∀ x : Fin 9 → Bool, cofactor (graph leftStemRightTail []) 5 true x = (graph leftStem [1]) x := by
        decide +kernel
      rw [funext eq]
      exact leftStemOr1

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem rightTailOr6 : Lower 8 (graph rightTail [6]) := by
  refine lower_one (p := 6) (b := false) (by decide) ?_ ?_ ?_
  · exact ⟨bits 0, by decide +kernel⟩
  · exact ⟨bits 0, bits 17, by decide +kernel⟩
  · have eq : ∀ x : Fin 9 → Bool, cofactor (graph rightTail [6]) 6 false x = (graph rightTail []) x := by
      decide +kernel
    rw [funext eq]
    exact rightTailBound

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem JBound : Lower 10 (graph J []) := by
  refine lower_two (p := 2) ?_ ?_ ?_
  · exact ⟨bits 64, by decide +kernel⟩
  · intro b
    cases b
    · exact ⟨bits 0, bits 17, by decide +kernel⟩
    · exact ⟨bits 0, bits 17, by decide +kernel⟩
  · intro b
    cases b
    · have eq : ∀ x : Fin 9 → Bool, cofactor (graph J []) 2 false x = (graph leftStemRightTail []) x := by
        decide +kernel
      rw [funext eq]
      exact leftStemRightTailBound
    · have eq : ∀ x : Fin 9 → Bool, cofactor (graph J []) 2 true x = (graph rightTail [6]) x := by
        decide +kernel
      rw [funext eq]
      exact rightTailOr6

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem JOr8Bound : Lower 11 (graph J [8]) := by
  refine lower_one (p := 8) (b := false) (by decide) ?_ ?_ ?_
  · exact ⟨bits 0, by decide +kernel⟩
  · exact ⟨bits 0, bits 17, by decide +kernel⟩
  · have eq : ∀ x : Fin 9 → Bool, cofactor (graph J [8]) 8 false x = (graph J []) x := by
      decide +kernel
    rw [funext eq]
    exact JBound

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem pinLeafTrue : Lower 11 (cofactor target 3 true) := by
  have eq : ∀ x : Fin 9 → Bool, cofactor target 3 true x = graph J [8] x := by
    decide +kernel
  rw [funext eq]
  exact JOr8Bound

end Theta9433J

end

-- From .pnp-tools/Theta9433Host.lean
section

namespace Theta9433Host

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers CircuitHelpers.Readers

open Cactus10440Floor

open Theta9433Control (target)

open Theta9433J (J)

abbrev main : Fn 9 := cofactor target 3 true

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem mainHostFalse : cofactor main 8 false = graph J [] := by
  funext x
  exact (show ∀ y : Fin 9 → Bool, cofactor main 8 false y = graph J [] y from by
    decide +kernel) x

theorem mainHostFalseNC : Nonconst (cofactor main 8 false) :=
  ⟨fun _ => false, fun _ => true, by decide +kernel⟩

theorem depHost : Dep main (8 : Fin 9) :=
  ⟨fun _ => false, by decide +kernel⟩

private theorem rawReader {n : ℕ} {f : Fn n} {gs : List Gate} {o : ℕ}
    (L : Least n f gs o) (i : Fin n) (dep : Dep f i)
    (nonconst : Nonconst (cofactor f i false)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := nonconst
    apply hxy
    unfold cofactor
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := dep
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjn : j < n
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjn⟩ from getD_ofFn n _ false ⟨j, hjn⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjn⟩ from getD_ofFn n _ false ⟨j, hjn⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem hostOnlyOr {gs : List Gate} {o : ℕ} (L : Least 9 main gs o)
    (size : gs.length ≤ 11) :
    ∃ p g, gs[p]? = some g ∧ (8 : ℕ) ∈ g.inputs ∧
      (∀ q, Reads gs q (8 : ℕ) → q = p) ∧ g.op = .or := by
  have noTwo (pay : Drop main 8 false 2 gs.length) : False := by
    obtain ⟨t, saved, fit⟩ := pay
    change HasCircuitSize 9 (cofactor main 8 false) t at fit
    rw [mainHostFalse] at fit
    have lb := Theta9433J.JBound t fit
    omega
  obtain ⟨p, g, hg, h8⟩ := rawReader L 8 depHost mainHostFalseNC
  have hread : Reads gs p 8 := ⟨g, hg, h8⟩
  have one (q : ℕ) (hq : Reads gs q 8) : q = p := by
    by_contra eq
    exact noTwo (L.save2 8 false mainHostFalseNC q p eq (rc_input false hq) (rc_input false hread))
  have shape : g.op = .or := by
    rcases gate_cases gs L.hcl p g hg 8 h8 with ⟨gNot, _, _⟩ | ⟨_, _, andOr⟩
    · exfalso
      have c := isC_reader L.hcl 8 p g hg h8 false (Or.inl gNot)
      obtain ⟨q, order, _, hc⟩ := L.next 8 false mainHostFalseNC p (reads_len hread) c
      exact noTwo (L.save2 8 false mainHostFalseNC p q (by omega) (rc_input false hread) hc)
    · rcases andOr with ⟨gAnd, _⟩ | ⟨gOr, _⟩
      · exfalso
        have c := isC_reader L.hcl 8 p g hg h8 false (Or.inr (by simp [fixBit, gAnd]))
        obtain ⟨q, order, _, hc⟩ := L.next 8 false mainHostFalseNC p (reads_len hread) c
        exact noTwo (L.save2 8 false mainHostFalseNC p q (by omega) (rc_input false hread) hc)
      · exact gOr
  exact ⟨p, g, hg, h8, one, shape⟩

def OrEdge (n : ℕ) (gs : List Gate) (u v : ℕ) : Prop :=
  ∃ p g, v = n + p ∧ gs[p]? = some g ∧ u ∈ g.inputs ∧ g.op = .or

theorem orPathPreservesTrue {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (x : Fin n → Bool) {u v : ℕ} (path : Relation.ReflTransGen (OrEdge n gs) u v)
    (value : vl gs x u = true) : vl gs x v = true := by
  induction path with
  | refl => exact value
  | tail _ step ih =>
    obtain ⟨p, g, rfl, atGate, inside, gOr⟩ := step
    rw [vl_gate gs clean x p g atGate, gOr]
    change ((g.inputs.map (vl gs x)).any id) = true
    exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨_, inside, ih⟩, rfl⟩

theorem leafControlAtNegative {α : Type*}
    (rest : α → Bool) (neighbors : α → Bool)
    (W : α → Bool) (U : α → Bool → Bool) (decode : α → Bool → Bool)
    (fit : ∀ y l h, decode y ((l || W y) && U y h) =
      (rest y || (h && (l || neighbors y)))) :
    ∀ y, rest y = false → W y = neighbors y := by
  intro y hrest
  by_cases hs : neighbors y = true
  · by_cases hw : W y = true
    · rw [hs, hw]
    · have hw' : W y = false := by cases h : W y <;> simp_all
      have eq0 := fit y false false
      have eq1 := fit y false true
      simp [hrest, hw', hs] at eq0 eq1
      rw [eq0] at eq1
      contradiction
  · have hs' : neighbors y = false := by cases h : neighbors y <;> simp_all
    cases hw : W y
    · exact hs'.symm
    · have eq0 := fit y false true
      have eq1 := fit y true true
      simp [hrest, hw, hs'] at eq0 eq1
      rw [eq0] at eq1
      contradiction

end Theta9433Host

end

-- From .pnp-tools/Cactus10440Chain.lean
section

namespace Cactus10440Chain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers CircuitHelpers.Readers

open Cactus10440Floor

theorem consumer {f : Fn 9} {gs : List Gate} {o p : ℕ}
    (L : Least 9 f gs o) (size : gs.length ≤ 13) (i : Fin 9)
    (nonconst : ∀ b, Nonconst (cofactor f i b))
    (bound : ∀ b, Lower 11 (cofactor f i b)) (hp : Reads gs p i) :
    ∃ q g h, gs[p]? = some g ∧ gs[q]? = some h ∧
      Reads gs q (9 + p) ∧ (∀ r, Reads gs r (9 + p) → r = q) ∧
      ((g.op = .and ∧ h.op = .or) ∨ (g.op = .or ∧ h.op = .and)) := by
  have noThree (b : Bool) (pay : Drop f i b 3 gs.length) : False := by
    obtain ⟨s, saved, hs⟩ := pay
    have lb := bound b s hs
    omega
  obtain ⟨g, hg, hgi⟩ := hp
  have hp : Reads gs p i := ⟨g, hg, hgi⟩
  have hc := isC_reader L.hcl i p g hg hgi (fixBit g) (Or.inr rfl)
  obtain ⟨q, hpq, hq, hqr⟩ := L.next i (fixBit g) (nonconst _) p (reads_len hp) hc
  have unique (r : ℕ) (hr : Reads gs r (9 + p)) : r = q := by
    by_contra different
    have hpr := reads_lt L.hcl hr
    exact noThree _ (L.save3 i _ (nonconst _) p q r
      (by omega) (by omega) (fun eq => different eq.symm)
      (rc_input _ hp) hqr (rc_of_reads hr hc))
  have noConst (b c : Bool) (first : IsC 8 gs i b (9 + p)) :
      stF 8 gs i b (9 + q) ≠ Stat.const c := by
    intro eq
    obtain ⟨r, hrq, _, hrr⟩ := L.next i b (nonconst b) q (reads_len hq) ⟨c, eq⟩
    exact noThree b (L.save3 i b (nonconst b) p q r
      (by omega) (by omega) (by omega) (rc_input b hp) (rc_of_reads hq first) hrr)
  obtain ⟨h, hh, hhp⟩ := hq
  refine ⟨q, g, h, hg, hh, ⟨h, hh, hhp⟩, unique, ?_⟩
  obtain ⟨c, hpc⟩ := hc
  have shape := st_shape 8 gs L.hcl i (fixBit g) q h hh (9 + p) hhp c hpc
    (fun c' => noConst _ c' ⟨c, hpc⟩)
  have inputVal (b : Bool) : vl gs (ins i b (fun _ : Fin 8 => false)) i.val = b := by
    rw [vl_input gs _ _ i.isLt]
    exact Fin.insertNth_apply_same (α := fun _ : Fin 9 => Bool) i b (fun _ => false)
  rcases gate_cases gs L.hcl p g hg i.val hgi with
    ⟨gNot, _, meaning⟩ | ⟨_, _, gAnd | gOr⟩
  · exfalso
    let b := !fixBit h
    obtain ⟨v, hv⟩ := isC_reader L.hcl i p g hg hgi b (Or.inl gNot)
    have eval := st_val_const 8 gs L.hcl i b (9 + p) v hv (fun _ => false)
    rw [meaning, inputVal] at eval
    have fixed : v = fixBit h := by rw [← eval]; simp [b]
    have hc' : IsC 8 gs i b (9 + q) :=
      const_read 8 gs L.hcl i b q h hh (9 + p) hhp (fixed ▸ hv)
    obtain ⟨d, hd⟩ := hc'
    exact noConst b d ⟨v, hv⟩ hd
  · left
    refine ⟨gAnd.1, ?_⟩
    have bb : fixBit g = false := by simp [fixBit, gAnd.1]
    have eval := st_val_const 8 gs L.hcl i (fixBit g) (9 + p) c hpc (fun _ => false)
    rw [gAnd.2, inputVal, bb, Bool.false_and] at eval
    rcases shape.1 with hAnd | hOr
    · exact False.elim (shape.2.1 (by simpa [fixBit, hAnd] using eval.symm))
    · exact hOr
  · right
    refine ⟨gOr.1, ?_⟩
    have bb : fixBit g = true := by simp [fixBit, gOr.1]
    have eval := st_val_const 8 gs L.hcl i (fixBit g) (9 + p) c hpc (fun _ => false)
    rw [gOr.2, inputVal, bb, Bool.true_or] at eval
    rcases shape.1 with hAnd | hOr
    · exact hAnd
    · exact False.elim (shape.2.1 (by simpa [fixBit, hOr] using eval.symm))

end Cactus10440Chain

end

-- From .pnp-tools/Theta9433Leaf.lean
section

namespace Theta9433Leaf

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers

open CircuitHelpers.PermInputs CircuitHelpers.Readers

open Cactus10440Floor

open Theta9433Control (target)

def phi : Fin 9 → Fin 8 := ![0, 4, 5, 0, 2, 6, 3, 1, 7]

def tableTarget (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
    (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
private theorem core_relabel : ∀ x : Fin 8 → Bool,
    cofactor target 3 false (x ∘ phi) = tableTarget x := by
  decide +kernel

theorem pinLeafFalse (tableBound : Lower 12 tableTarget) : Lower 12 (cofactor target 3 false) := by
  intro s h
  exact tableBound s
    (funext core_relabel ▸ relabel_size phi (cofactor target 3 false) s h)

theorem leafDepends : Dep target (3 : Fin 9) := by
  exact ⟨fun i => decide (i = 8), by decide +kernel⟩

theorem leafNonconst (b : Bool) : Nonconst (cofactor target 3 b) := by
  cases b <;> exact ⟨fun _ => false, fun _ => true, by decide +kernel⟩

theorem postedFloor (floor : Lower 12 (cofactor target 3 false)) : Lower 13 target :=
  lower_one (p := 3) (b := false) (by decide) leafDepends (leafNonconst false) floor

theorem pinEitherFloor (floor : Lower 12 (cofactor target 3 false))
    (b : Bool) : Lower 11 (cofactor target 3 b) := by
  cases b
  · exact fun s fit => le_trans (by decide) (floor s fit)
  · exact Theta9433J.pinLeafTrue

theorem leafShape (floor : Lower 12 (cofactor target 3 false))
    {gs : List Gate} {o : ℕ} (L : Least 9 target gs o)
    (size : gs.length ≤ 13) :
    ∃ p q g h, gs[p]? = some g ∧ gs[q]? = some h ∧
      Reads gs p (3 : ℕ) ∧ (∀ r, Reads gs r (3 : ℕ) → r = p) ∧
      Reads gs q (9 + p) ∧ (∀ r, Reads gs r (9 + p) → r = q) ∧
      g.op = .or ∧ h.op = .and := by
  obtain ⟨p, hp⟩ := L.dep_read 3 leafDepends leafNonconst
  have uniquely (r : ℕ) (hr : Reads gs r (3 : ℕ)) : r = p := by
    by_contra diff
    have noThree (b : Bool) (k : ℕ) (hk : 3 ≤ k) (pay : Drop target 3 b k gs.length) :
        False := by
      obtain ⟨t, count, fit⟩ := pay
      have lower := pinEitherFloor floor b t fit
      omega
    rcases L.two_readers 3 leafNonconst p r (fun e => diff e.symm) hp hr with
      ⟨pay, _⟩ | ⟨pay, _⟩ | ⟨_, pay⟩
    · exact noThree false 3 (by decide) pay
    · exact noThree false 4 (by decide) pay
    · exact noThree true 4 (by decide) pay
  obtain ⟨q, g, h, hg, hh, hq, hUnique, shape⟩ :=
    Cactus10440Chain.consumer L size 3 leafNonconst (pinEitherFloor floor) hp
  refine ⟨p, q, g, h, hg, hh, hp, uniquely, hq, hUnique, ?_⟩
  rcases shape with ⟨hAnd, _⟩ | good
  · exfalso
    obtain ⟨g', hg', hgp⟩ := hp
    have same : g' = g := Option.some.inj (hg'.symm.trans hg)
    subst g'
    have constant := isC_reader L.hcl 3 p g hg hgp false (Or.inr (by simp [fixBit, hAnd]))
    have readsLater := reads_lt L.hcl hq
    obtain ⟨t, saved, fit⟩ := L.save2 3 false (leafNonconst false) p q
      (by omega) (rc_input false ⟨g, hg, hgp⟩) (rc_of_reads hq constant)
    have lower := floor t fit
    omega
  · exact good

end Theta9433Leaf

end

-- From .pnp-tools/Theta9433UseTable.lean
section

namespace Theta9433UseTable

open Cactus10440Floor

open Theta9433Control (target)

open PEqualNP.CircuitLowerBounds CircuitHelpers.Readers

theorem pinLeafFalse : Lower 12 (cofactor target 3 false) :=
  Theta9433Leaf.pinLeafFalse CoreTable7402

theorem fullFloor : Lower 13 target :=
  Theta9433Leaf.postedFloor pinLeafFalse

theorem leafShape {gs : List Gate} {o : ℕ} (least : Least 9 target gs o)
    (budget : gs.length ≤ 13) :
    ∃ p q g h, gs[p]? = some g ∧ gs[q]? = some h ∧
      Reads gs p (3 : ℕ) ∧ (∀ r, Reads gs r (3 : ℕ) → r = p) ∧
      Reads gs q (9 + p) ∧ (∀ r, Reads gs r (9 + p) → r = q) ∧
      g.op = .or ∧ h.op = .and :=
  Theta9433Leaf.leafShape pinLeafFalse least budget

end Theta9433UseTable

end

-- From .pnp-tools/Theta9433LeafSplice.lean
section

namespace Theta9433LeafSplice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers CircuitHelpers.Readers

open BranchProof2752 (notGateCount)

open BranchProof2752.CircuitProof (isNotGate)

open Theta9433Control (target)

open Theta9433Host (main)

open Theta9433Bypass (newSlot remove wire)

def spliceSlot (p q r : Nat) : Nat := newSlot (newSlot p q) (newSlot p r)

def spliceWire (p q u j : Nat) : Nat :=
  wire 9 (newSlot p q) (wire 9 p 3 u) (wire 9 p 3 j)

def spliceGate (p q u : Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map (spliceWire p q u)⟩

def spliceGates (gs : List Gate) (p q u : Nat) : List Gate :=
  remove 9 (newSlot p q) (wire 9 p 3 u) (remove 9 p 3 gs)

private theorem redirect_twice (p q u : Nat) (g : Gate) :
    Theta9433Bypass.redirect 9 (newSlot p q) (wire 9 p 3 u)
      (Theta9433Bypass.redirect 9 p 3 g) = spliceGate p q u g := by
  simp only [spliceGate, Theta9433Bypass.redirect, List.map_map]
  rfl

private theorem newSlot_inj {p r s : Nat} (hr : r ≠ p) (hs : s ≠ p)
    (eq : newSlot p r = newSlot p s) : r = s := by
  unfold newSlot at eq
  split_ifs at eq <;> omega

theorem gate_at {gs : List Gate} {p q u r : Nat} {g : Gate} (before : p < q)
    (rp : r ≠ p) (rq : r ≠ q) (atOld : gs[r]? = some g) :
    (spliceGates gs p q u)[spliceSlot p q r]? = some (spliceGate p q u g) := by
  have first := Theta9433Bypass.gate_at (n := 9) (substitute := 3) rp atOld
  have different : newSlot p r ≠ newSlot p q := fun eq => rq (newSlot_inj rp (by omega) eq)
  have second := Theta9433Bypass.gate_at (n := 9) (substitute := wire 9 p 3 u) different first
  rw [redirect_twice] at second
  exact second

theorem old_gate {gs : List Gate} {p q u j : Nat} {g : Gate}
    (atNew : (spliceGates gs p q u)[j]? = some g) :
    ∃ r h, r ≠ p ∧ r ≠ q ∧ spliceSlot p q r = j ∧ gs[r]? = some h ∧ g = spliceGate p q u h := by
  obtain ⟨k, first, hk, slot, atFirst, rfl⟩ := Theta9433Bypass.old_gate atNew
  obtain ⟨r, h, rp, rfl, atOld, rfl⟩ := Theta9433Bypass.old_gate atFirst
  exact ⟨r, h, rp, fun eq => hk (by rw [eq]), slot, atOld, redirect_twice p q u h⟩

theorem wire_input {p q u j : Nat} (raw : j < 9) : spliceWire p q u j = j := by
  unfold spliceWire
  rw [Theta9433Bypass.wire_raw raw, Theta9433Bypass.wire_raw raw]

theorem wire_gate {p q u r : Nat} (before : p < q) (rp : r ≠ p) (rq : r ≠ q) :
    spliceWire p q u (9 + r) = 9 + spliceSlot p q r := by
  have different : newSlot p r ≠ newSlot p q := fun eq => rq (newSlot_inj rp (by omega) eq)
  unfold spliceWire spliceSlot
  rw [Theta9433Bypass.wire_at rp, Theta9433Bypass.wire_at different]

private theorem wire_eq_three {p substitute j : Nat} (eq : wire 9 p substitute j = 3) :
    j = 3 ∨ (j = 9 + p ∧ substitute = 3) := by
  unfold wire at eq
  split_ifs at eq <;> omega

structure Splice (gs : List Gate) (out : Nat) where
  p : Nat
  q : Nat
  w : Nat
  u : Nat
  first : Gate
  second : Gate
  before : p < q
  firstAt : gs[p]? = some first
  secondAt : gs[q]? = some second
  firstOr : first.op = .or
  secondAnd : second.op = .and
  firstInputs : first.inputs = [3, w] ∨ first.inputs = [w, 3]
  secondInputs : second.inputs = [9 + p, u] ∨ second.inputs = [u, 9 + p]
  wNotLeaf : w ≠ 3
  uNotLeaf : u ≠ 3
  uNotFirst : u ≠ 9 + p
  onlyLeafReader : ∀ r, Reads gs r 3 → r = p
  onlyFirstReader : ∀ r, Reads gs r (9 + p) → r = q
  residualLeast : Least 9 main (spliceGates gs p q u) (spliceWire p q u out)
  residualSize : (spliceGates gs p q u).length = 11
  residualNoLeafReader : ∀ g ∈ spliceGates gs p q u, 3 ∉ g.inputs
  residualOutNotLeaf : spliceWire p q u out ≠ 3
  agrees (x : Fin 9 → Bool) (pinned : x 3 = true) (j : Nat) (valid : j < 9 + gs.length) :
    vl (spliceGates gs p q u) x (spliceWire p q u j) = vl gs x j

theorem least_splice {gs : List Gate} {out : Nat} (least : Least 9 target gs out)
    (cap : gs.length ≤ 13) : Nonempty (Splice gs out) := by
  obtain ⟨p, q, g, h, gp, hq, ⟨g', gp', readLeaf⟩, uniqueLeaf,
    ⟨h', hq', readFirst⟩, uniqueFirst, gOr, hAnd⟩ := Theta9433UseTable.leafShape least cap
  have geq : g' = g := Option.some.inj (gp'.symm.trans gp)
  have heq : h' = h := Option.some.inj (hq'.symm.trans hq)
  subst g' h'
  have hp : p < gs.length := (List.getElem?_eq_some_iff.mp gp).1
  have hqBound : q < gs.length := (List.getElem?_eq_some_iff.mp hq).1
  have before : p < q := by
    have earlier := (least.hcl q h hq).lt (9 + p) readFirst
    omega
  have nonconstant := dep_nc Theta9433Leaf.leafDepends
  have validOut : out < 9 + gs.length := by
    by_contra! outside
    obtain ⟨x, y, diff⟩ := least.ncv nonconstant
    exact diff ((vl_beyond gs x out outside).trans (vl_beyond gs y out outside).symm)
  obtain ⟨w, gInputs, gEval⟩ : ∃ w, (g.inputs = [3, w] ∨ g.inputs = [w, 3]) ∧
      ∀ x : Fin 9 → Bool, vl gs x (9 + p) = (vl gs x 3 || vl gs x w) := by
    rcases gate_cases gs least.hcl p g gp 3 readLeaf with ⟨notOp, _⟩ | ⟨w, pins, shapes⟩
    · rw [gOr] at notOp
      contradiction
    rcases shapes with ⟨andOp, _⟩ | ⟨_, evaluates⟩
    · rw [gOr] at andOp
      contradiction
    exact ⟨w, pins, evaluates⟩
  obtain ⟨u, hInputs, hEval⟩ : ∃ u, (h.inputs = [9 + p, u] ∨ h.inputs = [u, 9 + p]) ∧
      ∀ x : Fin 9 → Bool, vl gs x (9 + q) = (vl gs x (9 + p) && vl gs x u) := by
    rcases gate_cases gs least.hcl q h hq (9 + p) readFirst with ⟨notOp, _⟩ | ⟨u, pins, shapes⟩
    · rw [hAnd] at notOp
      contradiction
    rcases shapes with ⟨_, evaluates⟩ | ⟨orOp, _⟩
    · exact ⟨u, pins, evaluates⟩
    · rw [hAnd] at orOp
      contradiction
  have uIn : u ∈ h.inputs := by
    rcases hInputs with pins | pins <;> simp [pins]
  have uEarlier := (least.hcl q h hq).lt u uIn
  have wNotLeaf : w ≠ 3 := by
    rintro rfl
    apply least.no_alias nonconstant p hp 3 (by omega)
    intro x
    simp [gEval]
  have uNotFirst : u ≠ 9 + p := by
    rintro rfl
    apply least.no_alias nonconstant q hqBound (9 + p) uEarlier
    intro x
    simp [hEval]
  have uNotLeaf : u ≠ 3 := by
    rintro rfl
    exact (ne_of_gt before) (uniqueLeaf q ⟨h, hq, uIn⟩)

  let firstPass := remove 9 p 3 gs
  let q' := newSlot p q
  let u' := wire 9 p 3 u
  have backFirst : 3 < 9 + p := by omega
  have backSecond : u' < 9 + q' := Theta9433Bypass.wire_before backFirst (ne_of_gt before) uEarlier
  have cleanFirst : CleanL 9 firstPass := Theta9433Bypass.clean least.hcl backFirst
  have cleanSplice : CleanL 9 (spliceGates gs p q u) := Theta9433Bypass.clean cleanFirst backSecond
  have lenFirst : firstPass.length + 1 = gs.length := Theta9433Bypass.size hp
  have qAtFirst := Theta9433Bypass.gate_at (n := 9) (substitute := 3) (ne_of_gt before) hq
  have q'Bound : q' < firstPass.length := (List.getElem?_eq_some_iff.mp qAtFirst).1
  have lenSplice : (spliceGates gs p q u).length + 1 = firstPass.length := Theta9433Bypass.size q'Bound
  have lower := Theta9433UseTable.fullFloor gs.length (funext least.hev ▸ has_of_clean 9 gs out least.hcl)
  have eleven : (spliceGates gs p q u).length = 11 := by omega

  have agrees (x : Fin 9 → Bool) (pinned : x 3 = true) (j : Nat) (valid : j < 9 + gs.length) :
      vl (spliceGates gs p q u) x (spliceWire p q u j) = vl gs x j := by
    have leafValue : vl gs x 3 = true := (vl_input gs x 3 (by decide)).trans pinned
    have firstValue : vl gs x (9 + p) = vl gs x 3 := by simp [gEval, leafValue]
    have firstAgrees := Theta9433Bypass.eval least.hcl backFirst x firstValue
    have secondValue : vl firstPass x (9 + q') = vl firstPass x u' := by
      change vl firstPass x (9 + newSlot p q) = vl firstPass x (wire 9 p 3 u)
      rw [← Theta9433Bypass.wire_at (n := 9) (substitute := 3) (ne_of_gt before),
        firstAgrees _ (by omega), firstAgrees _ (by omega)]
      simp [hEval, firstValue, leafValue]
    have midValid : wire 9 p 3 j < 9 + firstPass.length := by
      have mapped := Theta9433Bypass.wire_before (substitute := 3) backFirst
        (show gs.length ≠ p by omega) valid
      simp only [newSlot, ite_eq_right (show ¬ gs.length < p by omega)] at mapped
      omega
    exact (Theta9433Bypass.eval cleanFirst backSecond x secondValue _ midValid).trans
      (firstAgrees j valid)

  have preimage (j : Nat) (eq : spliceWire p q u j = 3) : j = 3 ∨ j = 9 + p := by
    rcases wire_eq_three eq with first | ⟨_, uEq⟩
    · rcases wire_eq_three first with pure | ⟨gate, _⟩
      · exact Or.inl pure
      · exact Or.inr gate
    · rcases wire_eq_three uEq with raw | ⟨wire, _⟩
      · exact (uNotLeaf raw).elim
      · exact (uNotFirst wire).elim
  have noLeafReader : ∀ g' ∈ spliceGates gs p q u, 3 ∉ g'.inputs := by
    intro g' member reads
    obtain ⟨j, atNew⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨r, old, rp, rq, _, atOld, rfl⟩ := old_gate atNew
    obtain ⟨a, aIn, eq⟩ := List.mem_map.mp reads
    rcases preimage a eq with rfl | rfl
    · exact rp (uniqueLeaf r ⟨old, atOld, aIn⟩)
    · exact rq (uniqueFirst r ⟨old, atOld, aIn⟩)
  have outNotLeaf : spliceWire p q u out ≠ 3 := by
    intro eq
    obtain ⟨x, y, diff⟩ := Theta9433Leaf.leafNonconst true
    have value (z : Fin 9 → Bool) : main z = true := by
      change target (Function.update z (3 : Fin 9) true) = true
      rw [← least.hev, ← agrees _ (by simp) out validOut, eq, vl_input _ _ _ (by decide)]
      simp
    exact diff ((value x).trans (value y).symm)
  have computes (x : Fin 9 → Bool) : vl (spliceGates gs p q u) x (spliceWire p q u out) = main x := by
    let y := Function.update x (3 : Fin 9) true
    calc
      vl (spliceGates gs p q u) x (spliceWire p q u out) =
          vl (spliceGates gs p q u) y (spliceWire p q u out) := by
        refine agree_except 3 (spliceGates gs p q u) _ _ noLeafReader (by simp) ?_ _ outNotLeaf
        intro j other
        by_cases raw : j < 9
        · rw [getD_ofFn 9 x false ⟨j, raw⟩, getD_ofFn 9 y false ⟨j, raw⟩]
          exact (Function.update_of_ne (fun eq => other (congrArg Fin.val eq)) _ _).symm
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      _ = vl gs y out := agrees y (by simp [y]) out validOut
      _ = main x := least.hev y
  have residualLeast : Least 9 main (spliceGates gs p q u) (spliceWire p q u out) := by
    refine ⟨cleanSplice, computes, fun test testOut clean fit => ?_⟩
    rw [eleven]
    have fitted : HasCircuitSize 9 main test.length := funext fit ▸ has_of_clean 9 test testOut clean
    exact Theta9433J.pinLeafTrue _ fitted
  exact ⟨⟨p, q, w, u, g, h, before, gp, hq, gOr, hAnd, gInputs, hInputs,
    wNotLeaf, uNotLeaf, uNotFirst, uniqueLeaf, uniqueFirst, residualLeast, eleven,
    noLeafReader, outNotLeaf, agrees⟩⟩

private theorem remove_notGateCount {n p substitute : Nat} {gs : List Gate} {g : Gate}
    (atGate : gs[p]? = some g) (binary : isNotGate g.op = false) :
    notGateCount (remove n p substitute gs) = notGateCount gs := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g atGate
  have erased : (pre ++ g :: post).eraseIdx pre.length = pre ++ post := by
    rw [List.eraseIdx_append_of_length_le (le_refl _)]
    simp
  unfold notGateCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  simp [remove, erased, Theta9433Bypass.redirect, Function.comp_def, binary]

theorem Splice.notGateCount_eq {gs : List Gate} {out : Nat} (s : Splice gs out) :
    notGateCount (spliceGates gs s.p s.q s.u) = notGateCount gs := by
  have first := remove_notGateCount (n := 9) (substitute := 3) s.firstAt (by simp [s.firstOr, isNotGate])
  have qAtFirst := Theta9433Bypass.gate_at (n := 9) (substitute := 3) (ne_of_gt s.before) s.secondAt
  have second := remove_notGateCount (n := 9) (substitute := wire 9 s.p 3 s.u) qAtFirst
    (by simp [Theta9433Bypass.redirect, s.secondAnd, isNotGate])
  exact second.trans first

end Theta9433LeafSplice

end

-- From .pnp-tools/Theta9433Original.lean
section

namespace Theta9433Original

open PEqualNP.CircuitLowerBounds CircuitHelpers

open CircuitHelpers.Readers

open BranchProof2752.PetersenCutTrace

open Cactus10440Floor Theta9433Control Theta9433LeafSplice

open Theta9433J (J)

open Relation

def pair (x : Fin 9 → Bool) (l h : Bool) := Function.update (Function.update x 3 l) 8 h

theorem pairLeafUnchanged (x : Fin 9 → Bool) (l l' h : Bool) {j : Fin 9} (leaf : j ≠ 3) :
    pair x l h j = pair x l' h j := by
  by_cases host : j = 8
  · subst j
    simp [pair]
  · simp [pair, Function.update_of_ne leaf, Function.update_of_ne host]

def remainder := graph J []

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem pairTarget : ∀ (x : Fin 9 → Bool) (l h : Bool),
    target (pair x l h) = (remainder x || (h && (l || x 2 || x 5))) := by
  decide +kernel

theorem rawStep {gs : List Gate} {j : Fin 9} {p : ℕ} {next : Fin (9 + gs.length)}
    (unique : ∀ r, Reads gs r j → r = p) (edge : readEdge gs (inputWire gs j) next) :
    next.val = 9 + p := by
  obtain ⟨r, g, found, dst, input⟩ := edge
  simpa only [unique r ⟨g, found, input⟩] using dst

theorem pathIndex {gs : List Gate} (clean : CleanL 9 gs)
    {a b : Fin (9 + gs.length)} (reach : ReflTransGen (readEdge gs) a b) : a.val ≤ b.val := by
  induction reach with
  | refl => exact le_rfl
  | tail _ step ih => exact ih.trans (read_order clean step).le

theorem noLeafReach {gs : List Gate} {o : ℕ} (S : Splice gs o) (L : Least 9 target gs o)
    {w : Fin (9 + gs.length)} (earlier : w.val < 9 + S.q) (notLeaf : w.val ≠ 3)
    (notFirst : w.val ≠ 9 + S.p) :
    ¬ ReflTransGen (readEdge gs) (inputWire gs (3 : Fin 9)) w := by
  intro path
  rcases path.cases_head with here | ⟨first, edge, later⟩
  · exact notLeaf (congrArg Fin.val here.symm)
  · have firstVal := rawStep S.onlyLeafReader edge
    rcases later.cases_head with here | ⟨second, step, tail⟩
    · exact notFirst ((congrArg Fin.val here).symm.trans firstVal)
    · obtain ⟨r, g, hr, htarget, hinput⟩ := step
      rw [firstVal] at hinput
      have rEq := S.onlyFirstReader r ⟨g, hr, hinput⟩
      rw [rEq] at htarget
      have le := pathIndex L.hcl tail
      omega

theorem mainBlocking {gs : List Gate} {o : Fin (9 + gs.length)}
    (S : Splice gs o.val) (outRaw : o.val ≠ 3) (outFirst : o.val ≠ 9 + S.p)
    (qBound : 9 + S.q < 9 + gs.length) :
    ¬ ReflTransGen (avoid (readEdge gs) ⟨9 + S.q, qBound⟩)
      (inputWire gs (3 : Fin 9)) o := by
  intro path
  rcases path.cases_head with here | ⟨first, edge, rest⟩
  · exact outRaw (congrArg Fin.val here.symm)
  · have firstVal := rawStep S.onlyLeafReader edge.1
    rcases rest.cases_head with here | ⟨next, step, _⟩
    · exact outFirst ((congrArg Fin.val here).symm.trans firstVal)
    · obtain ⟨r, g, hr, htarget, hinput⟩ := step.1
      rw [firstVal] at hinput
      have rEq := S.onlyFirstReader r ⟨g, hr, hinput⟩
      apply step.2.2
      exact Fin.ext (htarget.trans (by rw [rEq]))

theorem wEarlier {gs : List Gate} {o : ℕ} (S : Splice gs o) (L : Least 9 target gs o) :
    S.w < 9 + S.p := (L.hcl S.p S.first S.firstAt).lt S.w (by
      rcases S.firstInputs with pins | pins <;> simp [pins])

theorem uEarlier {gs : List Gate} {o : ℕ} (S : Splice gs o) (L : Least 9 target gs o) :
    S.u < 9 + S.q := (L.hcl S.q S.second S.secondAt).lt S.u (by
      rcases S.secondInputs with pins | pins <;> simp [pins])

theorem firstEval {gs : List Gate} {o : ℕ} (S : Splice gs o) (L : Least 9 target gs o)
    (x : Fin 9 → Bool) : vl gs x (9 + S.p) = (x 3 || vl gs x S.w) := by
  rw [vl_gate gs L.hcl x S.p S.first S.firstAt, S.firstOr]
  rcases S.firstInputs with a | a
  · simp [a, GateOp.eval, vl_input gs x 3 (by decide)]
  · simp [a, GateOp.eval, vl_input gs x 3 (by decide), Bool.or_comm]

theorem secondEval {gs : List Gate} {o : ℕ} (S : Splice gs o) (L : Least 9 target gs o)
    (x : Fin 9 → Bool) :
    vl gs x (9 + S.q) = ((x 3 || vl gs x S.w) && vl gs x S.u) := by
  rw [vl_gate gs L.hcl x S.q S.second S.secondAt, S.secondAnd]
  rcases S.secondInputs with a | a
  · simp [a, GateOp.eval, firstEval S L x]
  · simp [a, GateOp.eval, firstEval S L x, Bool.and_comm]

theorem wGateFalseAtProbe {gs : List Gate} {o : Fin (9 + gs.length)}
    (S : Splice gs o.val) (L : Least 9 target gs o.val) (outRaw : o.val ≠ 3) :
    vl gs (pair (fun _ => false) true true) S.w = false := by
  let a := pair (fun _ => false) false true
  let b := pair (fun _ => false) true true
  have h0 : vl gs a o.val = false := (L.hev _).trans (by decide +kernel)
  have h1 : vl gs b o.val = true := (L.hev _).trans (by decide +kernel)
  have pBound : 9 + S.p < 9 + gs.length := by
    have := (List.getElem?_eq_some_iff.mp S.firstAt).1
    omega
  let cut : Fin (9 + gs.length) := ⟨9 + S.p, pBound⟩
  have wBound := wEarlier S L
  let aux : Fin (9 + gs.length) := ⟨S.w, by omega⟩
  have wEq : vl gs a S.w = vl gs b S.w := by
    apply agree_on_input_ancestors L.hcl _ _ aux
    intro j path
    by_cases isLeaf : j = 3
    · subst j
      exact (noLeafReach S L (w := aux)
        (by change S.w < _; have := S.before; omega)
        S.wNotLeaf (by change S.w ≠ _; omega) path).elim
    · exact pairLeafUnchanged _ false true true isLeaf
  cases hb : vl gs b S.w
  · rfl
  · have atCut : vl gs a cut.val = vl gs b cut.val := by
      change vl gs a (9 + S.p) = vl gs b (9 + S.p)
      rw [firstEval S L a, firstEval S L b, wEq, hb, Bool.or_true, Bool.or_true]
    have final := circuit_cut_agreement L.hcl cut o a b atCut (by
      intro i diff path
      have leaf : i = 3 := by
        by_contra other
        exact diff (pairLeafUnchanged _ false true true other)
      subst i
      rcases path.cases_head with here | ⟨next, edge, _⟩
      · exact outRaw (congrArg Fin.val here.symm)
      · exact edge.2.2 (Fin.ext (rawStep S.onlyLeafReader edge.1)))
    change vl gs a o.val = vl gs b o.val at final
    rw [h0, h1] at final
    contradiction

def wIndex {gs : List Gate} {o : ℕ} (S : Splice gs o) (L : Least 9 target gs o) :
    Fin (9 + gs.length) := ⟨S.w, by
  have := wEarlier S L
  have := (List.getElem?_eq_some_iff.mp S.firstAt).1
  omega⟩

def uIndex {gs : List Gate} {o : ℕ} (S : Splice gs o) (L : Least 9 target gs o) :
    Fin (9 + gs.length) := ⟨S.u, by
  have := uEarlier S L
  have := (List.getElem?_eq_some_iff.mp S.secondAt).1
  omega⟩

def secondIndex {gs : List Gate} {o : ℕ} (S : Splice gs o) : Fin (9 + gs.length) :=
  ⟨9 + S.q, by have := (List.getElem?_eq_some_iff.mp S.secondAt).1; omega⟩

theorem wInvariant {gs : List Gate} {o : ℕ} (S : Splice gs o) (L : Least 9 target gs o)
    (noHost : ¬ ReflTransGen (readEdge gs) (inputWire gs (8 : Fin 9)) (wIndex S L))
    (x : Fin 9 → Bool) (l h : Bool) : vl gs (pair x l h) S.w = vl gs x S.w := by
  apply agree_on_input_ancestors L.hcl _ _ (wIndex S L)
  intro j path
  by_cases leaf : j = 3
  · subst j
    have early := wEarlier S L
    have before := S.before
    exact (noLeafReach S L (w := wIndex S L) (by change S.w < _; omega)
      S.wNotLeaf (by change S.w ≠ _; omega) path).elim
  by_cases host : j = 8
  · subst j
    exact (noHost path).elim
  · simp [pair, Function.update_of_ne leaf, Function.update_of_ne host]

theorem uLeafInvariant {gs : List Gate} {o : ℕ} (S : Splice gs o) (L : Least 9 target gs o)
    (x : Fin 9 → Bool) (l h : Bool) : vl gs (pair x l h) S.u = vl gs (pair x false h) S.u := by
  apply agree_on_input_ancestors L.hcl _ _ (uIndex S L)
  intro j path
  by_cases leaf : j = 3
  · subst j
    exact (noLeafReach S L (w := uIndex S L) (uEarlier S L) S.uNotLeaf S.uNotFirst path).elim
  · exact pairLeafUnchanged _ l false h leaf

theorem portBoundary {gs : List Gate} {out : Fin (9 + gs.length)}
    (S : Splice gs out.val) (L : Least 9 target gs out.val)
    (outRaw : out.val ≠ 3) (outFirst : out.val ≠ 9 + S.p)
    (noHostToW : ¬ ReflTransGen (readEdge gs) (inputWire gs (8 : Fin 9)) (wIndex S L))
    (hostCut : ¬ ReflTransGen (avoid (readEdge gs) (secondIndex S))
      (inputWire gs (8 : Fin 9)) out) :
    ∀ x, remainder x = false → vl gs x S.w = (x 2 || x 5) := by
  have leafCut : ¬ ReflTransGen (avoid (readEdge gs) (secondIndex S))
      (inputWire gs (3 : Fin 9)) out := mainBlocking S outRaw outFirst (secondIndex S).isLt
  have factor (x : Fin 9 → Bool) : ∃ decoder : Bool → Bool,
      ∀ l h, decoder (vl gs (pair x l h) (9 + S.q)) = target (pair x l h) := by
    let atCut (z : Bool × Bool) := vl gs (pair x z.1 z.2) (9 + S.q)
    let outValue (z : Bool × Bool) := target (pair x z.1 z.2)
    have agrees (a b : Bool × Bool) (eq : atCut a = atCut b) : outValue a = outValue b := by
      have endEq := circuit_cut_agreement L.hcl (secondIndex S) out _ _ eq (by
        intro j diff
        by_cases leaf : j = 3
        · subst j
          exact leafCut
        by_cases host : j = 8
        · subst j
          exact hostCut
        · exact (diff (by simp [pair, Function.update_of_ne leaf, Function.update_of_ne host])).elim)
      exact (L.hev _).symm.trans (endEq.trans (L.hev _))
    obtain ⟨decoder, semantics⟩ := unary_factor atCut outValue agrees
    exact ⟨decoder, fun l h => semantics (l, h)⟩
  choose decoder semantics using factor
  apply Theta9433Host.leafControlAtNegative remainder (fun x : Fin 9 → Bool => x 2 || x 5)
    (fun x => vl gs x S.w) (fun x b => vl gs (pair x false b) S.u) decoder
  intro x l h
  have eq := semantics x l h
  rw [pairTarget, secondEval S L _, wInvariant S L noHostToW x l h,
    uLeafInvariant S L x l h] at eq
  simpa [pair, Function.update_of_ne (show (3 : Fin 9) ≠ 8 by decide), Bool.or_assoc]
    using eq

end Theta9433Original

end

-- From .pnp-tools/Theta9433Arity.lean
section

namespace Theta9433Arity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers CircuitHelpers.Readers

open CircuitHelpers.PermInputs

open BranchProof2752 (notGateCount)

open BranchProof2752.PetersenCutTrace (readEdge inputWire)

open Cactus10440Floor (Nonconst Lower cofactor)

open Theta9433Host (main)

def dropWire (p w : ℕ) : ℕ := if w < p then w else w - 1

def restoreWire (p w : ℕ) : ℕ := if w < p then w else w + 1

def dropGate (p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (dropWire p)⟩

def dropPrimary (p : ℕ) (gs : List Gate) : List Gate := gs.map (dropGate p)

@[simp] theorem dropPrimary_length (p : ℕ) (gs : List Gate) :
    (dropPrimary p gs).length = gs.length := by simp [dropPrimary]

@[simp] theorem dropPrimary_gateOps (p : ℕ) (gs : List Gate) :
    (dropPrimary p gs).map Gate.op = gs.map Gate.op := by
  simp [dropPrimary, dropGate, List.map_map, Function.comp_def]

@[simp] theorem dropPrimary_notGateCount (p : ℕ) (gs : List Gate) :
    notGateCount (dropPrimary p gs) = notGateCount gs := by
  simp [notGateCount, dropPrimary, List.filter_map, dropGate, Function.comp_def]

theorem gate_at {p r : ℕ} {gs : List Gate} {g : Gate} (atGate : gs[r]? = some g) :
    (dropPrimary p gs)[r]? = some (dropGate p g) := by
  simp [dropPrimary, List.getElem?_map, atGate]

theorem old_gate {p r : ℕ} {gs : List Gate} {g : Gate}
    (atGate : (dropPrimary p gs)[r]? = some g) :
    ∃ h, gs[r]? = some h ∧ dropGate p h = g := by
  simpa only [dropPrimary, List.getElem?_map, Option.map_eq_some_iff] using atGate

@[simp] theorem restoreWire_ne (p w : ℕ) : restoreWire p w ≠ p := by
  unfold restoreWire
  split <;> omega

@[simp] theorem restore_dropWire {p w : ℕ} (away : w ≠ p) :
    restoreWire p (dropWire p w) = w := by
  unfold restoreWire dropWire
  split_ifs <;> omega

@[simp] theorem drop_restoreWire (p w : ℕ) : dropWire p (restoreWire p w) = w := by
  unfold dropWire restoreWire
  split_ifs <;> omega

theorem dropWire_inj {p w z : ℕ} (hw : w ≠ p) (hz : z ≠ p) :
    dropWire p w = dropWire p z ↔ w = z := by
  constructor
  · intro eq
    simpa [restore_dropWire hw, restore_dropWire hz] using congrArg (restoreWire p) eq
  · rintro rfl
    rfl

theorem dropWire_lt_iff {p w z : ℕ} (hw : w ≠ p) (hz : z ≠ p) :
    dropWire p w < dropWire p z ↔ w < z := by
  unfold dropWire
  split_ifs <;> omega

@[simp] theorem dropWire_gate {n : ℕ} (p : Fin (n + 1)) (r : ℕ) :
    dropWire p (n + 1 + r) = n + r := by
  have bound := p.isLt
  unfold dropWire
  split <;> omega

@[simp] theorem dropWire_input {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    dropWire p (p.succAbove i).val = i.val := by
  unfold Fin.succAbove
  split <;> rename_i side
  · exact ite_eq_left side
  · have after : ¬ i.succ.val < p.val := by
      change ¬ i.val < p.val at side
      change ¬ i.val + 1 < p.val
      omega
    exact (ite_eq_right after).trans (Nat.add_sub_cancel _ _)

@[simp] theorem restoreWire_input {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    restoreWire p i.val = (p.succAbove i).val := by
  rw [← dropWire_input p i, restore_dropWire (fun eq => Fin.succAbove_ne p i (Fin.ext eq))]

theorem dropWire_lt {n r w : ℕ} (p : Fin (n + 1)) (away : w ≠ p.val)
    (before : w < n + 1 + r) : dropWire p w < n + r := by
  rw [← dropWire_gate p r, dropWire_lt_iff away (by have := p.isLt; omega)]
  exact before

theorem dropPrimary_clean {n : ℕ} (p : Fin (n + 1)) {gs : List Gate}
    (clean : CleanL (n + 1) gs) (unused : ∀ g ∈ gs, p.val ∉ g.inputs) :
    CleanL n (dropPrimary p gs) := by
  intro r g atDrop
  obtain ⟨h, atGate, rfl⟩ := old_gate atDrop
  have away (w : ℕ) (member : w ∈ h.inputs) : w ≠ p.val := by
    intro eq
    exact unused h (List.mem_iff_getElem?.mpr ⟨r, atGate⟩) (eq ▸ member)
  rcases clean r h atGate with ⟨op, a, before, pins⟩ | ⟨ops, a, b, ha, hb, pins⟩
  · exact Or.inl ⟨op, dropWire p a, dropWire_lt p (away a (by simp [pins])) before,
      by simp [dropGate, pins]⟩
  · exact Or.inr ⟨ops, dropWire p a, dropWire p b, dropWire_lt p (away a (by simp [pins])) ha,
      dropWire_lt p (away b (by simp [pins])) hb, by simp [dropGate, pins]⟩

private def dropIndex {n : ℕ} [NeZero n] (p i : Fin (n + 1)) : Fin n :=
  if diff : i ≠ p then
    ⟨dropWire p i, by
      simpa using (dropWire_lt (r := 0) (w := i.val) p (fun eq => diff (Fin.ext eq))
        (by simpa using i.isLt))⟩
  else 0

@[simp] private theorem dropIndex_succAbove {n : ℕ} [NeZero n] (p : Fin (n + 1)) (i : Fin n) :
    dropIndex p (p.succAbove i) = i := by
  apply Fin.ext
  rw [dropIndex, dite_eq_left (Fin.succAbove_ne p i)]
  exact dropWire_input p i

private theorem dropWire_eq_wmap {n : ℕ} [NeZero n] (p : Fin (n + 1)) {w : ℕ}
    (away : w ≠ p.val) : dropWire p w = wmap (n + 1) n (dropIndex p) w := by
  unfold wmap
  split
  · rename_i raw
    simp [dropIndex, show (⟨w, raw⟩ : Fin (n + 1)) ≠ p from fun h => away (congrArg Fin.val h)]
  · rename_i gate
    have hp := p.isLt
    unfold dropWire
    split <;> omega

private theorem dropPrimary_eq_relabel {n : ℕ} [NeZero n] (p : Fin (n + 1)) {gs : List Gate}
    (unused : ∀ g ∈ gs, p.val ∉ g.inputs) :
    dropPrimary p gs = gs.map (relGate (n + 1) n (dropIndex p)) := by
  apply List.map_congr_left
  intro g member
  unfold dropGate relGate
  congr 1
  exact List.map_congr_left (fun w hw => dropWire_eq_wmap p (fun h => unused g member (h ▸ hw)))

theorem dropPrimary_value {n : ℕ} [NeZero n] (p : Fin (n + 1)) {gs : List Gate}
    (unused : ∀ g ∈ gs, p.val ∉ g.inputs) (x : Fin n → Bool) (bit : Bool) {w : ℕ}
    (away : w ≠ p.val) : vl (dropPrimary p gs) x (dropWire p w) = vl gs (ins p bit x) w := by
  rw [dropPrimary_eq_relabel p unused, dropWire_eq_wmap p away]
  have rel := (rel_fold (n + 1) n (dropIndex p) gs _ _ (rel_init (n + 1) n (dropIndex p) x)).2.2 w
  change vl (gs.map (relGate (n + 1) n (dropIndex p))) x _ = vl gs (x ∘ dropIndex p) w at rel
  rw [rel]
  apply agree_except p.val gs _ _ unused (by simp) ?_ w away
  intro j other
  by_cases raw : j < n + 1
  · let i : Fin (n + 1) := ⟨j, raw⟩
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (show i ≠ p from fun e => other (congrArg Fin.val e))
    rw [show j = i.val from rfl, getD_ofFn, getD_ofFn, ← hk]
    change x (dropIndex p (p.succAbove k)) = ins p bit x (p.succAbove k)
    rw [dropIndex_succAbove]
    exact (Fin.insertNth_apply_succAbove (α := fun _ : Fin (n + 1) => Bool) p bit x k).symm
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt raw),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt raw)]

theorem reads_drop_iff {p r w : ℕ} {gs : List Gate} (unused : ∀ g ∈ gs, p ∉ g.inputs)
    (away : w ≠ p) : Reads (dropPrimary p gs) r (dropWire p w) ↔ Reads gs r w := by
  constructor
  · rintro ⟨g, atDrop, read⟩
    obtain ⟨h, atGate, rfl⟩ := old_gate atDrop
    obtain ⟨u, hu, eq⟩ := List.mem_map.mp read
    have other : u ≠ p := fun h => unused _ (List.mem_iff_getElem?.mpr ⟨r, atGate⟩) (h ▸ hu)
    exact ⟨h, atGate, (dropWire_inj other away).mp eq ▸ hu⟩
  · rintro ⟨g, atGate, read⟩
    exact ⟨dropGate p g, gate_at atGate, List.mem_map.mpr ⟨w, read, rfl⟩⟩

def dropVertex {n : ℕ} {gs : List Gate} (p : Fin (n + 1))
    (w : Fin (n + 1 + gs.length)) (away : w.val ≠ p.val) : Fin (n + (dropPrimary p gs).length) :=
  ⟨dropWire p w.val, by simpa using dropWire_lt p away w.isLt⟩

def restoreVertex {n : ℕ} {gs : List Gate} (p : Fin (n + 1))
    (w : Fin (n + (dropPrimary p gs).length)) : Fin (n + 1 + gs.length) :=
  ⟨restoreWire p w.val, by
    have bound : w.val < n + gs.length := by simpa using w.isLt
    unfold restoreWire
    split <;> omega⟩

theorem restoreVertex_ne {n : ℕ} {gs : List Gate} (p : Fin (n + 1))
    (w : Fin (n + (dropPrimary p gs).length)) : (restoreVertex p w).val ≠ p.val :=
  restoreWire_ne _ _

@[simp] theorem restore_dropVertex {n : ℕ} {gs : List Gate} (p : Fin (n + 1))
    (w : Fin (n + 1 + gs.length)) (away : w.val ≠ p.val) :
    restoreVertex p (dropVertex p w away) = w := Fin.ext (restore_dropWire away)

@[simp] theorem drop_restoreVertex {n : ℕ} {gs : List Gate} (p : Fin (n + 1))
    (w : Fin (n + (dropPrimary p gs).length)) :
    dropVertex p (restoreVertex p w) (restoreVertex_ne p w) = w := Fin.ext (drop_restoreWire _ _)

@[simp] theorem dropVertex_input {n : ℕ} {gs : List Gate} (p : Fin (n + 1)) (i : Fin n)
    (away : (inputWire gs (p.succAbove i)).val ≠ p.val) :
    dropVertex p (inputWire gs (p.succAbove i)) away = inputWire (dropPrimary p gs) i :=
  Fin.ext (dropWire_input p i)

theorem readEdge_drop_iff {n : ℕ} {gs : List Gate} (p : Fin (n + 1))
    (unused : ∀ g ∈ gs, p.val ∉ g.inputs) (a b : Fin (n + 1 + gs.length))
    (aAway : a.val ≠ p.val) (bAway : b.val ≠ p.val) :
    readEdge (n := n) (dropPrimary p gs) (dropVertex p a aAway) (dropVertex p b bAway) ↔
      readEdge (n := n + 1) gs a b := by
  constructor
  · rintro ⟨r, g, atDrop, bSlot, contains⟩
    change dropWire p b.val = n + r at bSlot
    have slot : b.val = n + 1 + r :=
      (dropWire_inj bAway (by have := p.isLt; omega)).mp (bSlot.trans (dropWire_gate p r).symm)
    obtain ⟨h, atGate, reads⟩ := (reads_drop_iff unused aAway).mp ⟨g, atDrop, contains⟩
    exact ⟨r, h, atGate, slot, reads⟩
  · rintro ⟨r, g, atGate, slot, reads⟩
    refine ⟨r, dropGate p g, gate_at atGate, ?_, List.mem_map.mpr ⟨a.val, reads, rfl⟩⟩
    change dropWire p b.val = n + r
    rw [slot, dropWire_gate]

theorem readEdge_restore_iff {n : ℕ} {gs : List Gate} (p : Fin (n + 1))
    (unused : ∀ g ∈ gs, p.val ∉ g.inputs) (a b : Fin (n + (dropPrimary p gs).length)) :
    readEdge (n := n + 1) gs (restoreVertex p a) (restoreVertex p b) ↔
      readEdge (n := n) (dropPrimary p gs) a b := by
  rw [← readEdge_drop_iff p unused _ _ (restoreVertex_ne p a) (restoreVertex_ne p b)]
  simp

theorem readPath_drop_iff {n : ℕ} {gs : List Gate} (p : Fin (n + 1))
    (unused : ∀ g ∈ gs, p.val ∉ g.inputs) (a b : Fin (n + 1 + gs.length))
    (aAway : a.val ≠ p.val) (bAway : b.val ≠ p.val) :
    Relation.ReflTransGen (readEdge (n := n) (dropPrimary p gs)) (dropVertex p a aAway) (dropVertex p b bAway) ↔
      Relation.ReflTransGen (readEdge (n := n + 1) gs) a b := by
  constructor
  · intro route
    have lift {u v : Fin (n + (dropPrimary p gs).length)}
        (route : Relation.ReflTransGen (readEdge (n := n) (dropPrimary p gs)) u v) :
        Relation.ReflTransGen (readEdge (n := n + 1) gs) (restoreVertex p u) (restoreVertex p v) := by
      induction route with
      | refl => exact .refl
      | tail _ edge ih => exact ih.tail ((readEdge_restore_iff p unused _ _).mpr edge)
    simpa using lift route
  · intro route
    revert bAway
    induction route with
    | refl => exact fun _ => .refl
    | @tail mid last _ edge ih =>
      intro lastAway
      have midAway : mid.val ≠ p.val := by
        intro eq
        obtain ⟨r, g, atGate, _, reads⟩ := edge
        exact unused g (List.mem_iff_getElem?.mpr ⟨r, atGate⟩) (eq ▸ reads)
      exact (ih midAway).tail ((readEdge_drop_iff p unused _ _ midAway lastAway).mpr edge)

def main8 (x : Fin 8 → Bool) : Bool := main (ins (3 : Fin 9) true x)

theorem main8Bound : Lower 11 main8 := by
  have eq : ∀ x : Fin 9 → Bool, main8 (x ∘ (3 : Fin 9).succAbove) = main x := by
    intro x
    change main (ins (3 : Fin 9) true (Fin.removeNth 3 x)) = main x
    rw [← upd_ins]
    simp [main, cofactor]
  intro size fit
  apply Theta9433J.pinLeafTrue size
  change HasCircuitSize 9 main size
  rw [← funext eq]
  exact relabel_size ((3 : Fin 9).succAbove) main8 size fit

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
theorem main8Remainder : ∀ x : Fin 9 → Bool,
    cofactor main8 7 false (x ∘ (3 : Fin 9).succAbove) =
      Cactus10440Floor.graph Theta9433J.J [] x := by decide +kernel

theorem main8RemainderFloor : Lower 10 (cofactor main8 7 false) := by
  intro size fit
  exact Theta9433J.JBound size (funext main8Remainder ▸ relabel_size ((3 : Fin 9).succAbove) _ size fit)

theorem main8Least {gs : List Gate} {o : ℕ} (clean : CleanL 9 gs)
    (compute : ∀ x : Fin 9 → Bool, vl gs x o = main x) (size : gs.length ≤ 11)
    (unused : ∀ g ∈ gs, 3 ∉ g.inputs) (outAway : o ≠ 3) :
    Least 8 main8 (dropPrimary 3 gs) (dropWire 3 o) := by
  refine ⟨dropPrimary_clean (3 : Fin 9) clean unused, fun x => ?_, ?_⟩
  · exact (dropPrimary_value (3 : Fin 9) unused x true outAway).trans (compute _)
  · intro gs' o' clean' compute'
    rw [dropPrimary_length]
    exact size.trans (main8Bound _ (funext compute' ▸ has_of_clean 8 gs' o' clean'))

theorem main8HostOnlyOr {gs : List Gate} {o : ℕ} (L : Least 9 main gs o)
    (size : gs.length ≤ 11) (unused : ∀ g ∈ gs, 3 ∉ g.inputs) :
    ∃ p g, (dropPrimary 3 gs)[p]? = some g ∧ (7 : ℕ) ∈ g.inputs ∧
      (∀ q, Reads (dropPrimary 3 gs) q (7 : ℕ) → q = p) ∧ g.op = .or := by
  obtain ⟨p, g, atGate, member, unique, op⟩ := Theta9433Host.hostOnlyOr L size
  have host : dropWire 3 8 = 7 := by decide
  refine ⟨p, dropGate 3 g, gate_at atGate, ?_, ?_, op⟩
  · exact List.mem_map.mpr ⟨8, member, host⟩
  · intro q reader
    apply unique q
    exact (reads_drop_iff (r := q) (w := 8) unused (by decide)).mp (host.symm ▸ reader)

private def bits8 (mask : ℕ) (i : Fin 8) : Bool := mask.testBit i.val

theorem main8Nonconst : Nonconst main8 := ⟨bits8 0, bits8 128, by decide +kernel⟩

theorem main8Dep (i : Fin 8) : Dep main8 i := by
  let near : Fin 8 → ℕ := ![8, 16, 32, 1, 2, 4, 1, 0]
  have checked : ∀ (i : Fin 8),
      main8 (Function.update (bits8 (near i)) i (!(bits8 (near i) i))) ≠ main8 (bits8 (near i)) := by
    decide +kernel
  exact ⟨bits8 (near i), checked i⟩

private theorem depReads {n o : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (L : Least n f gs o) (i : Fin n) (dep : Dep f i) (away : o ≠ i.val) : ∃ r, Reads gs r i.val := by
  by_contra unused
  have absent (g : Gate) (member : g ∈ gs) : i.val ∉ g.inputs := by
    intro reads
    obtain ⟨r, atGate⟩ := List.mem_iff_getElem?.mp member
    exact unused ⟨r, g, atGate, reads⟩
  obtain ⟨x, diff⟩ := dep
  apply diff
  rw [← L.hev, ← L.hev]
  refine agree_except i.val gs _ _ absent (by simp) ?_ o away
  intro j other
  by_cases raw : j < n
  · let k : Fin n := ⟨j, raw⟩
    have distinct : k ≠ i := fun eq => other (congrArg Fin.val eq)
    rw [show j = k.val from rfl, getD_ofFn, getD_ofFn, Function.update_of_ne distinct]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt raw),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt raw)]

theorem main8OutputValid {gs : List Gate} {o : ℕ} (L : Least 8 main8 gs o) : o < 8 + gs.length := by
  by_contra! bad
  obtain ⟨x, y, diff⟩ := L.ncv main8Nonconst
  exact diff ((vl_beyond gs x o bad).trans (vl_beyond gs y o bad).symm)

theorem main8OutputGate {gs : List Gate} {o : ℕ} (L : Least 8 main8 gs o) : 8 ≤ o := by
  by_contra! raw
  let j : Fin 8 := ⟨o, raw⟩
  obtain ⟨i, distinct⟩ := exists_ne j
  obtain ⟨x, diff⟩ := main8Dep i
  apply diff
  rw [← L.hev, ← L.hev, vl_input gs _ o raw, vl_input gs _ o raw]
  exact Function.update_of_ne (Ne.symm distinct) _ _

theorem main8RawLive {gs : List Gate} {o : ℕ} (L : Least 8 main8 gs o) (i : Fin 8) : ∃ r, Reads gs r i.val := by
  exact depReads L i (main8Dep i) (by have := main8OutputGate L; have := i.isLt; omega)

theorem main8Live {gs : List Gate} {o : ℕ} (L : Least 8 main8 gs o)
    (valid : o < 8 + gs.length) : ∀ w : Fin (8 + gs.length),
      w ≠ (⟨o, valid⟩ : Fin (8 + gs.length)) → ∃ v, readEdge (n := 8) gs w v := by
  intro w notOutput
  have wValid := w.isLt
  have away : w.val ≠ o := fun eq => notOutput (Fin.ext eq)
  have reader : ∃ r, Reads gs r w.val := by
    by_cases raw : w.val < 8
    · exact main8RawLive L ⟨w.val, raw⟩
    · let slot := w.val - 8
      have index : w.val = 8 + slot := by dsimp [slot]; omega
      have slotValid : slot < gs.length := by omega
      obtain ⟨r, _, reads⟩ := L.live main8Nonconst slot slotValid (by omega)
      exact ⟨r, index.symm ▸ reads⟩
  obtain ⟨r, g, atGate, reads⟩ := reader
  have slotValid := (List.getElem?_eq_some_iff.mp atGate).1
  exact ⟨⟨8 + r, by omega⟩, r, g, atGate, rfl, reads⟩

end Theta9433Arity

end

-- From .pnp-tools/Theta9433SplicePath.lean
section

namespace Theta9433SplicePath

open PEqualNP.CircuitLowerBounds CircuitHelpers

open BranchProof2752.PetersenCutTrace

open BranchProof2752.FirstBranchRoute (Avoid)

open Theta9433LeafSplice Theta9433Bypass Relation

private theorem bypass_bounded {n p substitute j : Nat} {gs : List Gate}
    (back : substitute < n + p) (slot : p < gs.length) (valid : j < n + gs.length) :
    wire n p substitute j < n + (remove n p substitute gs).length := by
  have length := Theta9433Bypass.size (n := n) (substitute := substitute) slot
  have below := wire_before back (show gs.length ≠ p by omega) valid
  simp only [newSlot, ite_eq_right (show ¬ gs.length < p by omega)] at below
  omega

def mapWire {gs : List Gate} {out : Nat} (s : Splice gs out) (clean : CleanL 9 gs)
    (w : Fin (9 + gs.length)) : Fin (9 + (spliceGates gs s.p s.q s.u).length) := by
  refine ⟨spliceWire s.p s.q s.u w.val, ?_⟩
  have rawBack : 3 < 9 + s.p := by omega
  have pBound : s.p < gs.length := (List.getElem?_eq_some_iff.mp s.firstAt).1
  have qAtFirst := Theta9433Bypass.gate_at (n := 9) (substitute := 3) (ne_of_gt s.before) s.secondAt
  have qBound : newSlot s.p s.q < (remove 9 s.p 3 gs).length :=
    (List.getElem?_eq_some_iff.mp qAtFirst).1
  have uInput : s.u ∈ s.second.inputs := by
    rcases s.secondInputs with pins | pins <;> simp [pins]
  have uBack := (clean s.q s.second s.secondAt).lt s.u uInput
  have back := wire_before rawBack (ne_of_gt s.before) uBack
  exact bypass_bounded back qBound (bypass_bounded rawBack pBound w.isLt)

@[simp] theorem mapWire_val {gs : List Gate} {out : Nat} (s : Splice gs out) (clean : CleanL 9 gs)
    (w : Fin (9 + gs.length)) : (mapWire s clean w).val = spliceWire s.p s.q s.u w.val := rfl

@[simp] theorem map_input {gs : List Gate} {out : Nat} (s : Splice gs out) (clean : CleanL 9 gs)
    (i : Fin 9) : mapWire s clean (inputWire gs i) = inputWire (spliceGates gs s.p s.q s.u) i :=
  Fin.ext (wire_input i.isLt)

theorem map_before_first_val {gs : List Gate} {out : Nat} (s : Splice gs out)
    (clean : CleanL 9 gs) (w : Fin (9 + gs.length)) (early : w.val < 9 + s.p) :
    (mapWire s clean w).val = w.val := by
  have ordered := s.before
  have earlier : w.val < 9 + newSlot s.p s.q := by
    unfold newSlot
    split_ifs <;> omega
  simp [spliceWire, wire, ne_of_lt early, not_lt_of_ge early.le,
    ne_of_lt earlier, not_lt_of_ge earlier.le]

theorem map_gate_at {gs : List Gate} {out : Nat} (s : Splice gs out) (clean : CleanL 9 gs)
    {a b : Fin (9 + gs.length)} {r : Nat} {g : Gate}
    (atGate : gs[r]? = some g) (targetWire : b.val = 9 + r) (reads : a.val ∈ g.inputs)
    (rp : r ≠ s.p) (rq : r ≠ s.q) :
    (spliceGates gs s.p s.q s.u)[spliceSlot s.p s.q r]? = some (spliceGate s.p s.q s.u g) ∧
      (mapWire s clean b).val = 9 + spliceSlot s.p s.q r ∧
      (mapWire s clean a).val ∈ (spliceGate s.p s.q s.u g).inputs ∧
      (spliceGate s.p s.q s.u g).op = g.op := by
  refine ⟨Theta9433LeafSplice.gate_at s.before rp rq atGate, ?_, ?_, rfl⟩
  · rw [mapWire_val, targetWire, wire_gate s.before rp rq]
  · exact List.mem_map.mpr ⟨a.val, reads, rfl⟩

abbrev RetainedRead {gs : List Gate} {out : Nat} (s : Splice gs out)
    (a b : Fin (9 + gs.length)) : Prop :=
  readEdge gs a b ∧ b.val ≠ 9 + s.p ∧ b.val ≠ 9 + s.q

theorem map_edge {gs : List Gate} {out : Nat} (s : Splice gs out) (clean : CleanL 9 gs)
    {a b : Fin (9 + gs.length)} (edge : RetainedRead s a b) :
    readEdge (spliceGates gs s.p s.q s.u) (mapWire s clean a) (mapWire s clean b) := by
  rcases edge with ⟨⟨r, g, atGate, targetWire, reads⟩, notFirst, notSecond⟩
  obtain ⟨atNew, newWire, newReads, _⟩ := map_gate_at s clean atGate targetWire reads
    (fun eq => notFirst (targetWire.trans (congrArg (9 + ·) eq)))
    (fun eq => notSecond (targetWire.trans (congrArg (9 + ·) eq)))
  exact ⟨spliceSlot s.p s.q r, spliceGate s.p s.q s.u g, atNew, newWire, newReads⟩

theorem map_path {gs : List Gate} {out : Nat} (s : Splice gs out) (clean : CleanL 9 gs)
    {a b : Fin (9 + gs.length)} (path : ReflTransGen (RetainedRead s) a b) :
    ReflTransGen (readEdge (spliceGates gs s.p s.q s.u)) (mapWire s clean a) (mapWire s clean b) :=
  path.lift (mapWire s clean) (fun _ _ edge => map_edge s clean edge)

theorem map_path_before_first {gs : List Gate} {out : Nat} (s : Splice gs out) (clean : CleanL 9 gs)
    {a b : Fin (9 + gs.length)} (path : ReflTransGen (readEdge gs) a b) (before : b.val < 9 + s.p) :
    ReflTransGen (readEdge (spliceGates gs s.p s.q s.u)) (mapWire s clean a) (mapWire s clean b) := by
  apply map_path
  induction path with
  | refl => exact .refl
  | tail prior edge ih =>
    have incoming := read_order clean edge
    have ordered := s.before
    exact (ih (by omega)).tail ⟨edge, by omega, by omega⟩

end Theta9433SplicePath

end

-- From .pnp-tools/Theta9433BypassOrder.lean
section

namespace Theta9433BypassOrder

open PEqualNP.CircuitLowerBounds CircuitHelpers

open Theta9433Bypass Relation

def Reads (n : ℕ) (gs : List Gate) (u v : ℕ) : Prop :=
  ∃ j g, v = n + j ∧ gs[j]? = some g ∧ u ∈ g.inputs

abbrev Path (n : ℕ) (gs : List Gate) := ReflTransGen (Reads n gs)

theorem path_le {n : ℕ} {gs : List Gate} (original : CleanL n gs) {a b : ℕ}
    (path : Path n gs a b) : a ≤ b := by
  induction path with
  | refl => exact le_rfl
  | tail _ edge ih =>
    obtain ⟨p, g, rfl, gp, inp⟩ := edge
    exact le_trans ih (le_of_lt ((original p g gp).lt _ inp))

theorem readResult {n p substitute q : ℕ} {gs : List Gate}
    (original : CleanL n gs) (back : substitute < n + p)
    (x : Fin n → Bool) (g : Gate) (gq : gs[q]? = some g) (other : q ≠ p) :
    vl (remove n p substitute gs) x (wire n p substitute (n + q)) =
      g.op.eval (g.inputs.map (fun a => vl (remove n p substitute gs) x (wire n p substitute a))) := by
  rw [wire_at other, vl_gate _ (clean original back) x _ _
    (gate_at (n := n) (substitute := substitute) other gq)]
  simp [redirect, List.map_map, Function.comp_def]

theorem eval_offPath {n p substitute : ℕ} {gs : List Gate}
    (original : CleanL n gs) (back : substitute < n + p) (x : Fin n → Bool) :
    ∀ j < n + gs.length, ¬ Path n gs (n + p) j →
      vl (remove n p substitute gs) x (wire n p substitute j) = vl gs x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro bound offPath
    by_cases raw : j < n
    · rw [wire_raw raw, vl_input _ _ _ raw, vl_input _ _ _ raw]
    · let q := j - n
      have eq : j = n + q := by dsimp [q]; omega
      have qLt : q < gs.length := by omega
      have other : q ≠ p := by
        intro e
        apply offPath
        rw [eq, e]
      let g := gs[q]
      have gq : gs[q]? = some g := List.getElem?_eq_getElem qLt
      rw [eq, readResult original back x g gq other, vl_gate _ original x q g gq]
      congr 1
      apply List.map_congr_left
      intro a ha
      have earlier := (original q g gq).lt a ha
      refine ih a (by omega) (by omega) ?_
      intro path
      apply offPath
      rw [eq]
      exact path.tail ⟨q, g, rfl, gq, ha⟩

theorem eval_grows {n p substitute : ℕ} {gs : List Gate}
    (original : CleanL n gs) (back : substitute < n + p)
    (x : Fin n → Bool)
    (start : vl gs x (n + p) = true → vl gs x substitute = true)
    (noNot : ∀ q g, gs[q]? = some g → q ≠ p → Path n gs (n + p) (n + q) →
      g.op ≠ .not) :
    ∀ j < n + gs.length, vl gs x j = true →
      vl (remove n p substitute gs) x (wire n p substitute j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro bound before
    by_cases path : Path n gs (n + p) j
    · by_cases eq : j = n + p
      · subst j
        have same : wire n p substitute substitute = substitute := by
          simp [wire, show substitute ≠ n + p by omega, show ¬ n + p < substitute by omega]
        have offPath : ¬ Path n gs (n + p) substitute :=
          fun route => (Nat.not_le.mpr back) (path_le original route)
        calc
          vl (remove n p substitute gs) x (wire n p substitute (n + p)) =
              vl (remove n p substitute gs) x (wire n p substitute substitute) := by
                rw [show wire n p substitute (n + p) = substitute by simp [wire], same]
          _ = vl gs x substitute := eval_offPath original back x substitute (by omega) offPath
          _ = true := start before
      · have earlier := path_le original path
        let q := j - n
        have index : j = n + q := by dsimp [q]; omega
        have qLt : q < gs.length := by omega
        have other : q ≠ p := by omega
        let g := gs[q]
        have gq : gs[q]? = some g := List.getElem?_eq_getElem qLt
        have nonneg := noNot q g gq other (index ▸ path)
        have support (a : ℕ) (inGate : a ∈ g.inputs) (val : vl gs x a = true) :
            vl (remove n p substitute gs) x (wire n p substitute a) = true := by
          have validA := (original q g gq).lt a inGate
          exact ih a (by omega) (by omega) val
        rw [index, readResult original back x g gq other]
        rw [index, vl_gate _ original x q g gq] at before
        rcases original q g gq with ⟨gNot, _, _, _⟩ | ⟨gAndOr, a, b, _, _, pins⟩
        · exact (nonneg gNot).elim
        rcases gAndOr with gAnd | gOr
        · simp [gAnd, pins, GateOp.eval] at before ⊢
          exact ⟨support a (by simp [pins]) before.1, support b (by simp [pins]) before.2⟩
        · simp [gOr, pins, GateOp.eval] at before ⊢
          exact before.imp (support a (by simp [pins])) (support b (by simp [pins]))
    · rwa [eval_offPath original back x j bound path]

end Theta9433BypassOrder

end

-- From .pnp-tools/Theta9433PositiveCut.lean
section

namespace Theta9433PositiveCut

open Relation PEqualNP.CircuitLowerBounds BranchProof2752

open CircuitProof PetersenCutTrace PetersenFirstGroup

abbrev MovesTo (x y target : Bool) : Prop := x = !target ∧ y = target

def NotWire {n : ℕ} (gs : List Gate) (w : Fin (n + gs.length)) : Prop :=
  ∃ p g, gs[p]? = some g ∧ w.val = n + p ∧ g.op = .not

abbrev WireMovesTo {n : ℕ} (gs : List Gate) (x y : Fin n → Bool) (target : Bool)
    (w : Fin (n + gs.length)) : Prop := MovesTo (vl gs x w.val) (vl gs y w.val) target

abbrev SignedRead {n : ℕ} (gs : List Gate) (x y : Fin n → Bool) (target : Bool)
    (a b : Fin (n + gs.length)) : Prop :=
  readEdge gs a b ∧ WireMovesTo gs x y target a ∧ WireMovesTo gs x y target b

private theorem moves_differ {x y target : Bool} (moves : MovesTo x y target) : x ≠ y := by
  rw [moves.1, moves.2]
  cases target <;> decide

private theorem and_moves : ∀ a b c d target : Bool,
    MovesTo (a && b) (c && d) target → MovesTo a c target ∨ MovesTo b d target := by decide

private theorem or_moves : ∀ a b c d target : Bool,
    MovesTo (a || b) (c || d) target → MovesTo a c target ∨ MovesTo b d target := by decide

private theorem signed_gate_step {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (target : Bool) (w : Fin (n + gs.length))
    (internal : ¬ w.val < n) (moves : WireMovesTo gs x y target w) :
    NotWire gs w ∨ ∃ a, SignedRead gs x y target a w := by
  let p := w.val - n
  have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
  have hwire : w.val = n + p := by dsimp [p]; omega
  let g := gs[p]
  have hgate : gs[p]? = some g := List.getElem?_eq_getElem hp
  rcases clean p g hgate with ⟨hnot, _⟩ | ⟨op, a, b, ha, hb, inputs⟩
  · exact Or.inl ⟨p, g, hgate, hwire, hnot⟩
  let u : Fin (n + gs.length) := ⟨a, by omega⟩
  let v : Fin (n + gs.length) := ⟨b, by omega⟩
  have eval (z : Fin n → Bool) :
      vl gs z w.val = g.op.eval [vl gs z a, vl gs z b] := by
    rw [hwire, vl_gate gs clean z p g hgate, inputs]
    rfl
  have child : WireMovesTo gs x y target u ∨ WireMovesTo gs x y target v := by
    have evaluated : MovesTo (g.op.eval [vl gs x a, vl gs x b])
        (g.op.eval [vl gs y a, vl gs y b]) target := ⟨(eval x).symm.trans moves.1, (eval y).symm.trans moves.2⟩
    rcases op with hop | hop
    · exact and_moves _ _ _ _ _ (by simpa [hop, GateOp.eval] using evaluated)
    · exact or_moves _ _ _ _ _ (by simpa [hop, GateOp.eval] using evaluated)
  apply Or.inr
  rcases child with hmoves | hmoves
  · exact ⟨u, ⟨p, g, hgate, hwire, by simp [u, inputs]⟩, hmoves, moves⟩
  · exact ⟨v, ⟨p, g, hgate, hwire, by simp [v, inputs]⟩, hmoves, moves⟩

theorem signed_trace {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (target : Bool) (w : Fin (n + gs.length))
    (moves : WireMovesTo gs x y target w) :
    ∃ a, (a.val < n ∨ NotWire gs a) ∧ WireMovesTo gs x y target a ∧
      ReflTransGen (SignedRead gs x y target) a w := by
  induction w using (measure (fun w : Fin (n + gs.length) => w.val)).wf.induction with
  | h w ih =>
    by_cases isInput : w.val < n
    · exact ⟨w, Or.inl isInput, moves, .refl⟩
    rcases signed_gate_step clean x y target w isInput moves with isNot | ⟨a, read⟩
    · exact ⟨w, Or.inr isNot, moves, .refl⟩
    obtain ⟨source, terminal, sourceMoves, path⟩ := ih a (read_order clean read.1) read.2.1
    exact ⟨source, terminal, sourceMoves, path.tail read⟩

theorem noPathAvoidsFollow {m : ℕ} {reads : Fin m → Fin m → Prop} {out source cut goal : Fin m}
    (forward : ∀ {a b}, reads a b → a < b)
    (route : ReflTransGen (FirstBranchRoute.Follow reads out) source cut) (after : cut < goal) :
    ¬ ReflTransGen (avoid reads cut) source goal := by
  induction route using ReflTransGen.head_induction_on with
  | refl =>
    intro avoiding
    rcases avoiding.cases_head with equal | ⟨_, edge, _⟩
    · exact (ne_of_lt after) equal
    · exact edge.2.1 rfl
  | @head a b step rest ih =>
    intro avoiding
    rcases avoiding.cases_head with equal | ⟨next, edge, tail⟩
    · have bLe : b ≤ cut := FirstBranchRoute.path_forward reads forward
        (FirstBranchRoute.follows_is_read_path reads out rest)
      exact (ne_of_lt (lt_trans (lt_of_lt_of_le (forward step.1) bLe) after)) equal
    · have same : b = next := FirstBranchRoute.follow_unique reads out step ⟨edge.1, step.2⟩
      exact ih (same.symm ▸ tail)

private theorem notWire_unique {n : ℕ} {gs : List Gate} (budget : notGateCount gs ≤ 1)
    {a b : Fin (n + gs.length)} (ha : NotWire gs a) (hb : NotWire gs b) : a = b := by
  obtain ⟨p, g, hg, hw, hop⟩ := ha
  obtain ⟨q, h, hh, hv, hoq⟩ := hb
  apply Fin.ext
  rw [hw, hv]
  congr 1
  by_contra hpq
  let other : Gate := ⟨.and, []⟩
  have hq : (gs.set p other)[q]? = some h := by rwa [List.getElem?_set_ne hpq]
  have positive : 0 < (gs.set p other).countP (fun g => isNotGate g.op) :=
    List.countP_pos_iff.mpr ⟨h, List.mem_iff_getElem?.mpr ⟨q, hq⟩, by simp [hoq, isNotGate]⟩
  rw [List.countP_set (List.getElem?_eq_some_iff.mp hg).1,
    (List.getElem?_eq_some_iff.mp hg).2] at positive
  simp [hop, other, isNotGate, List.countP_eq_length_filter] at positive
  change 1 < notGateCount gs at positive
  exact (not_lt_of_ge budget) positive

theorem wire_before_boundary_pos {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length)) (live : ∀ w, w ≠ out → ∃ v, readEdge gs w v)
    (budget : notGateCount gs ≤ 1) (i : Fin n) (cut : Fin (n + gs.length))
    (reaches : ReflTransGen (readEdge gs) (inputWire gs i) cut)
    (before : cut ≤ firstInputBoundary clean out live i) (x y : Fin n → Bool)
    (same : ∀ j, j ≠ i → x j = y j) (inputUp : MovesTo (x i) (y i) true)
    (outputUp : WireMovesTo gs x y true out) : WireMovesTo gs x y true cut := by
  let source := inputWire gs i
  have cutDiff : vl gs x cut.val ≠ vl gs y cut.val := by
    intro equal
    apply moves_differ outputUp
    by_cases atOutput : cut = out
    · simpa only [atOutput] using equal
    apply circuit_cut_agreement clean cut out x y equal
    intro j different path
    have hj : j = i := by by_contra h; exact different (same j h)
    subst j
    have earlier : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) atOutput
    have cutRoute := (FirstBranchRoute.read_before (readEdge gs) out
      (read_order clean) live reaches before).1
    exact noPathAvoidsFollow (read_order clean) cutRoute earlier path
  by_contra notUp
  have cutDown : WireMovesTo gs x y false cut := by
    change vl gs x cut.val = true ∧ vl gs y cut.val = false
    cases h0 : vl gs x cut.val <;> cases h1 : vl gs y cut.val <;> simp_all [MovesTo]
  have input_flip (a : Fin (n + gs.length)) (ha : a.val < n) {target : Bool}
      (moves : WireMovesTo gs x y target a) : a = source ∧ target = true := by
    let j : Fin n := ⟨a.val, ha⟩
    have inputMoves : MovesTo (x j) (y j) target := by
      change MovesTo (vl gs x a.val) (vl gs y a.val) target at moves
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at moves
      exact moves
    have hj : j = i := by by_contra h; exact moves_differ inputMoves (same j h)
    refine ⟨Fin.ext ?_, inputMoves.2.symm.trans (by simpa only [hj] using inputUp.2)⟩
    change j.val = i.val
    exact congrArg Fin.val hj
  obtain ⟨t, negRoot, tDown, downPath⟩ := signed_trace clean x y false cut cutDown
  have tNot : NotWire gs t := negRoot.resolve_left (fun h => by cases (input_flip t h tDown).2)
  have sourceReaches : ReflTransGen (readEdge gs) source t := by
    by_contra missing
    apply moves_differ tDown
    apply agree_on_input_ancestors clean x y t
    intro j path
    by_cases h : j = i
    · subst j
      exact (missing path).elim
    · exact same j h
  have tLe : t ≤ cut := FirstBranchRoute.path_forward (readEdge gs) (read_order clean)
    (ReflTransGen.mono (fun _ _ h => h.1) _ _ downPath)
  have forced := (FirstBranchRoute.read_before (readEdge gs) out
    (read_order clean) live sourceReaches (tLe.trans before)).1
  have offNot (a : Fin (n + gs.length)) (up : WireMovesTo gs x y true a) : a ≠ t := by
    rintro rfl
    cases up.2.symm.trans tDown.2
  have tEarlier : t < out :=
    lt_of_le_of_ne (wire_le_output clean out live t) (Ne.symm (offNot out outputUp))
  obtain ⟨a, posRoot, aUp, upPath⟩ := signed_trace clean x y true out outputUp
  have aSource : a = source := by
    rcases posRoot with primary | negation
    · exact (input_flip a primary aUp).1
    · exact (offNot a aUp (notWire_unique budget negation tNot)).elim
  subst a
  exact noPathAvoidsFollow (read_order clean) forced tEarlier
    (ReflTransGen.mono (fun a b h => ⟨h.1, offNot a h.2.1, offNot b h.2.2⟩) _ _ upPath)

theorem firstInputBoundary_pos {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length)) (live : ∀ w, w ≠ out → ∃ v, readEdge gs w v)
    (budget : notGateCount gs ≤ 1) (i : Fin n) (x y : Fin n → Bool)
    (same : ∀ j, j ≠ i → x j = y j) (inputUp : MovesTo (x i) (y i) true)
    (outputUp : WireMovesTo gs x y true out) :
    WireMovesTo gs x y true (firstInputBoundary clean out live i) := by
  exact wire_before_boundary_pos clean out live budget i _
    (FirstBranchRoute.follows_is_read_path (readEdge gs) out
      (FirstBranchRoute.first_path (readEdge gs) out (read_order clean) live (inputWire gs i)))
    le_rfl x y same inputUp outputUp

theorem firstInputBoundary_or {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length)) (live : ∀ w, w ≠ out → ∃ v, readEdge gs w v)
    (budget : notGateCount gs ≤ 1) (i : Fin n) (J : (Fin n → Bool) → Bool)
    (computes : ∀ x, vl gs x out.val = (x i || J x)) (x : Fin n → Bool)
    (Jfalse : J (Function.update x i false) = false) :
    WireMovesTo gs (Function.update x i false) (Function.update x i true) true
      (firstInputBoundary clean out live i) := by
  apply firstInputBoundary_pos clean out live budget i
  · intro j hj
    simp [Function.update_of_ne hj]
  · simp [MovesTo]
  · constructor <;> simp [computes, Jfalse]

end Theta9433PositiveCut

end

-- From .pnp-tools/Theta9433OrPath.lean
section

namespace Theta9433OrPath

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers CircuitHelpers.Readers

open BranchProof2752.PetersenCutTrace

open BranchProof2752.PetersenFirstGroup

open BranchProof2752.FirstBranchRoute

open Cactus10440Floor Theta9433Bypass Relation

theorem natPathToFin {n : ℕ} {gs : List Gate}
    {a : Fin (n + gs.length)} {b : ℕ}
    (path : Theta9433BypassOrder.Path n gs a.val b) :
    ∃ target : Fin (n + gs.length), target.val = b ∧
      ReflTransGen (readEdge gs) a target := by
  induction path with
  | refl => exact ⟨a, rfl, ReflTransGen.refl⟩
  | tail _ edge ih =>
    obtain ⟨w, rfl, reach⟩ := ih
    obtain ⟨q, g, rfl, atGate, input⟩ := edge
    have qLt := (List.getElem?_eq_some_iff.1 atGate).1
    let dst : Fin (n + gs.length) := ⟨n + q, by omega⟩
    exact ⟨dst, rfl, reach.tail ⟨q, g, atGate, rfl, input⟩⟩

theorem reachable_gate {n : ℕ} {gs : List Gate} {i : Fin n}
    {q : ℕ} {g : Gate} (atGate : gs[q]? = some g)
    (reach : ReflTransGen (readEdge gs) (inputWire gs i)
      (⟨n + q, by have := (List.getElem?_eq_some_iff.1 atGate).1; omega⟩ : Fin (n + gs.length))) :
    ∃ w : Fin (n + gs.length), ReflTransGen (readEdge gs) (inputWire gs i) w ∧ w.val ∈ g.inputs := by
  rcases reach.cases_tail with eq | ⟨w, earlier, last⟩
  · have e := congrArg Fin.val eq
    have := i.isLt
    simp [inputWire] at e
    omega
  · obtain ⟨q', g', atGate', edgeEq, input⟩ := last
    change n + q = n + q' at edgeEq
    have e : q' = q := by omega
    subst q'
    have eG : g' = g := Option.some.inj (atGate'.symm.trans atGate)
    exact ⟨w, earlier, eG ▸ input⟩

def PositivePolarity {n : ℕ} (gs : List Gate) (i : Fin n) (remainder : Fn n) : Prop :=
  ∀ x, remainder x = false → ∀ w : Fin (n + gs.length),
    ReflTransGen (readEdge gs) (inputWire gs i) w →
    vl gs (Function.update x i false) w.val = false ∧
    vl gs (Function.update x i true) w.val = true

theorem noReachableNot {n : ℕ} {gs : List Gate} {i : Fin n} {remainder : Fn n}
    (clean : CleanL n gs) (polarity : PositivePolarity gs i remainder)
    (negative : ∃ x, remainder x = false)
    (q : ℕ) (g : Gate) (atGate : gs[q]? = some g)
    (reach : ReflTransGen (readEdge gs) (inputWire gs i)
      (⟨n + q, by have := (List.getElem?_eq_some_iff.1 atGate).1; omega⟩ : Fin (n + gs.length))) :
    g.op ≠ .not := by
  intro gNot
  obtain ⟨x, hx⟩ := negative
  obtain ⟨w, reaches, used⟩ := reachable_gate atGate reach
  have before := (polarity x hx w reaches).1
  have after := (polarity x hx _ reach).1
  obtain ⟨a, pins, _⟩ : ∃ a, g.inputs = [a] ∧ a < n + q := by
    rcases clean q g atGate with ⟨_, a, order, pins⟩ | ⟨ops, _⟩
    · exact ⟨a, pins, order⟩
    · rcases ops with op | op <;> simp_all
  have e : w.val = a := by simpa [pins] using used
  change vl gs (Function.update x i false) (n + q) = false at after
  rw [vl_gate _ clean _ q g atGate, gNot, pins, ← e] at after
  simp [GateOp.eval, before] at after

theorem onlyOr {n : ℕ} {gs : List Gate} {i : Fin n} {remainder : Fn n}
    (out : Fin (n + gs.length))
    (L : Least n (fun x => x i || remainder x) gs out.val)
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (one : firstInputBoundary L.hcl out live i = out)
    (polarity : PositivePolarity gs i remainder)
    (negative : ∃ x, remainder x = false) :
    ∀ q g, (atGate : gs[q]? = some g) →
      ReflTransGen (readEdge gs) (inputWire gs i)
        (⟨n + q, by have := (List.getElem?_eq_some_iff.1 atGate).1; omega⟩ :
          Fin (n + gs.length)) → g.op = .or := by
  intro q g atGate reach
  let current : Fin (n + gs.length) := ⟨n + q, by
    have := (List.getElem?_eq_some_iff.1 atGate).1
    omega⟩
  obtain ⟨w, inPath, wInput⟩ := reachable_gate atGate reach
  have noNot := noReachableNot L.hcl polarity negative q g atGate reach
  have nonconst : Nonconst (fun x => x i || remainder x) := by
    obtain ⟨x, hx⟩ := negative
    have outSigns := polarity x hx out (by
      rw [← one]
      exact follows_is_read_path _ _ (first_path (readEdge gs) out (read_order L.hcl) live _))
    refine ⟨Function.update x i false, Function.update x i true, fun eq => ?_⟩
    have eq' := (L.hev _).trans (eq.trans (L.hev _).symm)
    rw [outSigns.1, outSigns.2] at eq'
    contradiction
  rcases gate_cases gs L.hcl q g atGate w.val wInput with
    ⟨notOp, _, _⟩ | ⟨z, pins, andOr⟩
  · exact (noNot notOp).elim
  rcases andOr with ⟨andOp, gEval⟩ | ⟨orOp, _⟩
  · exfalso
    have wEarlier := (L.hcl q g atGate).lt w.val wInput
    have zInput : z ∈ g.inputs := by rcases pins with h | h <;> simp [h]
    have zEarlier := (L.hcl q g atGate).lt z zInput
    have distinct : w.val ≠ z := by
      intro equal
      apply L.no_alias nonconst q (List.getElem?_eq_some_iff.1 atGate).1 w.val wEarlier
      intro x
      rw [gEval x, ← equal, Bool.and_self]
    have currentBound : n + q < n + gs.length := current.isLt
    let other : Fin (n + gs.length) := ⟨z, by omega⟩
    have noOther : ¬ ReflTransGen (readEdge gs) (inputWire gs i) other := by
      intro reaches
      have bw : readEdge gs w current := ⟨q, g, atGate, rfl, wInput⟩
      have bz : readEdge gs other current := ⟨q, g, atGate, rfl, zInput⟩
      have leFirst : current ≤ firstInputBoundary L.hcl out live i := by
        rw [one]
        exact wire_le_output L.hcl out live current
      have eq := unique_predecessor_before (readEdge gs) out (read_order L.hcl) live
        leFirst inPath bw reaches bz
      exact distinct (congrArg Fin.val eq)
    have zFixed (x : Fin n → Bool) : vl gs (Function.update x i false) z =
        vl gs (Function.update x i true) z := by
      apply agree_on_input_ancestors L.hcl _ _ other
      intro j hj
      by_cases same : j = i
      · subst j
        exact (noOther hj).elim
      · simp [Function.update_of_ne same]
    have aliasAtNegative (x : Fin n → Bool) (hx : remainder x = false) :
        vl gs x (n + q) = vl gs x w.val := by
      have gTrue := (polarity x hx current reach).2
      change vl gs (Function.update x i true) (n + q) = true at gTrue
      rw [gEval] at gTrue
      have zTrue := (Bool.and_eq_true_iff.mp gTrue).2
      have zBoth : ∀ b, vl gs (Function.update x i b) z = true := by
        intro b
        cases b
        · exact (zFixed x).trans zTrue
        · exact zTrue
      have zx : vl gs x z = true := by
        simpa only [Function.update_eq_self] using zBoth (x i)
      rw [gEval x, zx, Bool.and_true]
    have noDownstream (r : ℕ) (h : Gate) (atR : gs[r]? = some h) (_ : r ≠ q)
        (path : Theta9433BypassOrder.Path n gs (n + q) (n + r)) :
        h.op ≠ .not := by
      obtain ⟨dest, eq, after⟩ := natPathToFin (a := current) path
      have idDest : dest = (⟨n + r, by
        have := (List.getElem?_eq_some_iff.1 atR).1
        omega⟩ : Fin (n + gs.length)) := Fin.ext eq
      rw [idDest] at after
      exact noReachableNot L.hcl polarity negative r h atR (reach.trans after)
    let new := remove n q w.val gs
    let dst := wire n q w.val out.val
    have hfit (x : Fin n → Bool) : vl new x dst = (x i || remainder x) := by
      cases hx : remainder x
      · simpa only [hx] using
          (eval L.hcl wEarlier x (aliasAtNegative x hx) out.val out.isLt).trans (L.hev x)
      · have was : vl gs x out.val = true := by rw [L.hev, hx, Bool.or_true]
        have start : vl gs x (n + q) = true → vl gs x w.val = true := by
          rw [gEval x]
          exact fun h => (Bool.and_eq_true_iff.mp h).1
        simpa [new, dst, hx] using
          Theta9433BypassOrder.eval_grows L.hcl wEarlier x start noDownstream _ out.isLt was
    have bound := L.hmin new dst (clean L.hcl wEarlier) hfit
    have small := size (n := n) (substitute := w.val) (List.getElem?_eq_some_iff.1 atGate).1
    dsimp [new] at bound
    omega
  · exact orOp

theorem polarity_of_or {n : ℕ} {gs : List Gate} {i : Fin n} {remainder : Fn n}
    (out : Fin (n + gs.length))
    (L : Least n (fun x => x i || remainder x) gs out.val)
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (one : firstInputBoundary L.hcl out live i = out)
    (budget : BranchProof2752.notGateCount gs ≤ 1)
    (ignores : ∀ x b, remainder (Function.update x i b) = remainder x) :
    PositivePolarity gs i remainder := by
  intro x hx w reaches
  let x0 := Function.update x i false
  let x1 := Function.update x i true
  have bound : w ≤ firstInputBoundary L.hcl out live i := by
    rw [one]
    exact wire_le_output L.hcl out live w
  have other : ∀ j, j ≠ i → x0 j = x1 j := by
    intro j different
    simp [x0, x1, Function.update_of_ne different]
  have rawRise : Theta9433PositiveCut.MovesTo (x0 i) (x1 i) true := by
    simp [x0, x1, Theta9433PositiveCut.MovesTo]
  have outRise : Theta9433PositiveCut.WireMovesTo gs x0 x1 true out := by
    change vl gs x0 out.val = false ∧ vl gs x1 out.val = true
    rw [L.hev, L.hev]
    simp [x0, x1, ignores, hx]
  exact Theta9433PositiveCut.wire_before_boundary_pos L.hcl out live budget i w reaches
    bound x0 x1 other rawRise outRise

theorem valueAlongOr {n : ℕ} {gs : List Gate} {i : Fin n} (clean : CleanL n gs)
    (ops : ∀ q g, (atGate : gs[q]? = some g) →
      ReflTransGen (readEdge gs) (inputWire gs i)
        (⟨n + q, by have := (List.getElem?_eq_some_iff.1 atGate).1; omega⟩ :
          Fin (n + gs.length)) → g.op = .or)
    (x : Fin n → Bool) (raw : x i = true) {w : Fin (n + gs.length)}
    (reach : ReflTransGen (readEdge gs) (inputWire gs i) w) : vl gs x w.val = true := by
  induction reach with
  | refl =>
    change vl gs x i.val = true
    rw [vl_input gs x i.val i.isLt]
    exact raw
  | tail prior step ih =>
    obtain ⟨q, g, atGate, atWire, input⟩ := step
    have eq : _ = (⟨n + q, by have := (List.getElem?_eq_some_iff.1 atGate).1; omega⟩ :
        Fin (n + gs.length)) := Fin.ext atWire
    have gOr := ops q g atGate (eq ▸ prior.tail ⟨q, g, atGate, atWire, input⟩)
    rw [atWire, vl_gate gs clean x q g atGate, gOr]
    change ((g.inputs.map (vl gs x)).any id) = true
    exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨_, input, ih⟩, rfl⟩

end Theta9433OrPath

end

-- From .pnp-tools/Theta9433DominatedWire.lean
section

namespace Theta9433DominatedWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers CircuitHelpers.Readers

private def freezeStats (m w : ℕ) : List Stat :=
  (List.range m).map fun i => if i = w then .const false else .wire i

private theorem freezeStats_getD (m w i : ℕ) :
    (freezeStats m w).getD i (.const false) =
      if i < m then (if i = w then .const false else .wire i) else .const false := by
  unfold freezeStats
  by_cases hi : i < m
  · simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [hi]

private theorem inv_freeze (n w : ℕ) (pre : List Gate) (x : Fin n → Bool) :
    Inv n (List.ofFn x) ((wiresFrom pre (List.ofFn x)).set w false)
      (freezeStats (n + pre.length) w, pre) := by
  have hlen : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
    rw [length_wiresFrom, List.length_ofFn]
  refine ⟨by simp [freezeStats, hlen], fun i => ?_⟩
  change ((freezeStats (n + pre.length) w).getD i (.const false)).Valid (n + pre.length) ∧
    ((freezeStats (n + pre.length) w).getD i (.const false)).val (wiresFrom pre (List.ofFn x)) =
      ((wiresFrom pre (List.ofFn x)).set w false).getD i false
  rw [freezeStats_getD]
  by_cases hi : i < n + pre.length
  · by_cases hw : i = w
    · subst i
      simp [hi, Stat.Valid, Stat.val, List.getD_eq_getElem?_getD, hlen]
    · simp [hi, hw, Ne.symm hw, Stat.Valid, Stat.val, List.getD_eq_getElem?_getD]
  · rw [ite_eq_right hi, List.getD_eq_default _ _ (by simp [hlen]; omega)]
    exact ⟨trivial, rfl⟩

private theorem elim_keeps_prefix (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    ∃ tail : List Gate, (elim n gs acc).2 = acc.2 ++ tail := by
  induction gs generalizing acc with
  | nil => exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    obtain ⟨tail, htail⟩ := ih (elimStep n acc g)
    rw [elim_cons, htail]
    simp only [elimStep, List.append_assoc]
    exact ⟨_, rfl⟩

private theorem vl_append {n : ℕ} (pre post : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + pre.length) : vl (pre ++ post) x w = vl pre x w := by
  unfold vl
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by simpa [length_wiresFrom] using hw)]

private theorem clean_append_gate {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : CleanL n gs) (hg : CleanGate (n + gs.length) g) : CleanL n (gs ++ [g]) := by
  intro i gi hi
  by_cases hlt : i < gs.length
  · rw [List.getElem?_append_left hlt] at hi
    exact hgs i gi hi
  · have hlen := (List.getElem?_eq_some_iff.mp hi).1
    have heq : i = gs.length := by simp at hlen; omega
    subst i
    rw [List.getElem?_concat_length] at hi
    cases hi
    exact hg

theorem clean_rewrite_or_true {n : ℕ} {f : (Fin n → Bool) → Bool}
    {gs : List Gate} {o w p q : ℕ} (hcl : CleanL n gs) (hev : ∀ x, vl gs x o = f x)
    (hdom : ∀ x, vl gs x w = true → f x = true)
    (hp : Reads gs p w) (hq : Reads gs q w) (hpq : p ≠ q) :
    (∃ gs' o', CleanL n gs' ∧ gs'.length < gs.length ∧ ∀ x, vl gs' x o' = f x) ∨
      (∀ x, f x = true) := by
  let k := w + 1 - n
  let pre := gs.take k
  let post := gs.drop k
  have hkp : k ≤ p := by have := reads_lt hcl hp; dsimp [k]; omega
  have hkq : k ≤ q := by have := reads_lt hcl hq; dsimp [k]; omega
  have hpre : pre.length = k := by
    have := reads_len hp
    simpa [pre] using Nat.min_eq_left (show k ≤ gs.length by omega)
  have hw : w < n + pre.length := by rw [hpre]; dsimp [k]; omega
  have hsplit : pre ++ post = gs := List.take_append_drop _ _
  have hclpre : CleanL n pre := by
    intro i g hi
    exact hcl i g (by rwa [← hsplit, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1])
  have hnok : ∀ g ∈ post, NOk g := fun g hg => clean_nok n gs hcl g (List.mem_of_mem_drop hg)
  have hok : ∀ g ∈ post, Ok g := fun g hg => (hnok g hg).1
  let start : List Stat × List Gate := (freezeStats (n + pre.length) w, pre)
  let acc := elim n post start
  have hstart : w < start.1.length ∧ start.1.getD w (.const false) = .const false := by
    simp [start, hw, freezeStats]
  have hsave : acc.2.length + 2 ≤ gs.length := by
    have hpq' : p - k ≠ q - k := by omega
    have hreader (i : ℕ) (hi : k ≤ i) (hr : Reads gs i w) :
        ∃ g, post[i - k]? = some g ∧ w ∈ g.inputs := by
      obtain ⟨g, hg, hread⟩ := hr
      refine ⟨g, ?_, hread⟩
      simpa [post, List.getElem?_drop, show k + (i - k) = i by omega] using hg
    have hcount := elim_count n start post hnok ({p - k, q - k} : Finset ℕ) (by
      intro i hi
      have hread : ∃ g, post[i]? = some g ∧ w ∈ g.inputs := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact hreader p hkp hp
        · exact hreader q hkq hq
      obtain ⟨g, hg, hr⟩ := hread
      exact ⟨g, hg, w, hr, by omega, false, (elim_getD n w _ post start hstart.1).trans hstart.2⟩)
    simpa [acc, start, hpq', ← List.length_append, hsplit] using hcount
  have hclacc : CleanL n acc.2 :=
    clean_elim n (List.ofFn fun _ : Fin n => false) List.length_ofFn post _ start hok
      (inv_freeze n w pre _) hclpre
  obtain ⟨tail, htail⟩ := elim_keeps_prefix n post start
  have haccpre : acc.2 = pre ++ tail := htail
  have hwacc : w < n + acc.2.length := by rw [haccpre, List.length_append]; omega
  have hwire (x : Fin n → Bool) : vl acc.2 x w = vl gs x w := by
    rw [haccpre, ← hsplit, vl_append _ _ _ _ hw, vl_append _ _ _ _ hw]
  have hinv (x : Fin n → Bool) :=
    inv_elim n (List.ofFn x) List.length_ofFn post _ start hok (inv_freeze n w pre x)
  let s := acc.1.getD o (.const false)
  have hvalid : s.Valid (n + acc.2.length) := ((hinv (fun _ => false)).2 o).1
  have hval (x : Fin n → Bool) (hx : vl gs x w = false) :
      s.val (wiresFrom acc.2 (List.ofFn x)) = f x := by
    have hex : (wiresFrom pre (List.ofFn x)).getD w false = false := by
      change vl pre x w = false
      rw [← vl_append pre post x w hw, hsplit, hx]
    have hlt : w < (wiresFrom pre (List.ofFn x)).length := by
      simpa [length_wiresFrom] using hw
    have hset : (wiresFrom pre (List.ofFn x)).set w false = wiresFrom pre (List.ofFn x) := by
      rw [List.getD_eq_getElem _ _ hlt] at hex
      rw [← hex, List.set_getElem_self]
    have hs := ((hinv x).2 o).2
    rw [hset, ← wiresFrom_append, hsplit] at hs
    exact hs.trans (hev x)
  have hrestore (x : Fin n → Bool) :
      (vl acc.2 x w || s.val (wiresFrom acc.2 (List.ofFn x))) = f x := by
    rw [hwire]
    cases hx : vl gs x w
    · simpa using hval x hx
    · simpa using (hdom x hx).symm
  cases hs : s with
  | const b =>
    cases b
    · exact Or.inl ⟨acc.2, w, hclacc, by omega, fun x => by
        simpa [hs, Stat.val] using hrestore x⟩
    · exact Or.inr fun x => by simpa [hs, Stat.val] using (hrestore x).symm
  | wire j =>
    have hj : j < n + acc.2.length := by simpa [hs, Stat.Valid] using hvalid
    let g : Gate := ⟨.or, [w, j]⟩
    have hcl' : CleanL n (acc.2 ++ [g]) := clean_append_gate hclacc
      (Or.inr ⟨Or.inr rfl, w, j, hwacc, hj, rfl⟩)
    refine Or.inl ⟨acc.2 ++ [g], n + acc.2.length, hcl', by simp; omega, fun x => ?_⟩
    rw [vl_gate _ hcl' _ _ _ List.getElem?_concat_length]
    simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id, Bool.or_false]
    rw [vl_append _ _ _ _ hwacc, vl_append _ _ _ _ hj]
    simpa [hs, Stat.val, vl] using hrestore x

theorem least_no_two_readers {n : ℕ} {f : (Fin n → Bool) → Bool}
    {gs : List Gate} {o w p q : ℕ} (L : Least n f gs o) (hfalse : ∃ x, f x = false)
    (hdom : ∀ x, vl gs x w = true → f x = true)
    (hp : Reads gs p w) (hq : Reads gs q w) (hpq : p ≠ q) : False := by
  rcases clean_rewrite_or_true L.hcl L.hev hdom hp hq hpq with ⟨gs', o', hc, hlt, hev'⟩ | hT
  · exact (Nat.not_le_of_gt hlt) (L.hmin gs' o' hc hev')
  · obtain ⟨x, hx⟩ := hfalse
    cases hx.symm.trans (hT x)

end Theta9433DominatedWire

end

-- From .pnp-tools/Theta9433NoFork.lean
section

namespace Theta9433NoFork

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers CircuitHelpers.Readers

open BranchProof2752 (notGateCount)

open BranchProof2752.PetersenCutTrace

open BranchProof2752.PetersenFirstGroup

open BranchProof2752.FirstBranchRoute

open Theta9433Bypass (newSlot remove redirect wire)

private theorem wire_eq_raw {n p t j : ℕ} {i : Fin n} (different : t ≠ i.val)
    (mapped : wire n p t j = i.val) : j = i.val := by
  have := i.isLt
  unfold wire at mapped
  split_ifs at mapped <;> omega

private theorem pin_unread {n : ℕ} {i : Fin n} {gs : List Gate}
    (noRead : ∀ g ∈ gs, i.val ∉ g.inputs) (x : Fin n → Bool) (j : ℕ) (other : j ≠ i.val) :
    vl gs x j = vl gs (Function.update x i false) j := by
  refine agree_except i.val gs _ _ noRead (by simp) ?_ j other
  intro a ha
  by_cases raw : a < n
  · rw [getD_ofFn n x false ⟨a, raw⟩, getD_ofFn n (Function.update x i false) false ⟨a, raw⟩]
    exact (Function.update_of_ne (fun eq => ha (congrArg Fin.val eq)) _ _).symm
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem erase_unique_or {n : ℕ} {gs : List Gate} {i : Fin n} {J : (Fin n → Bool) → Bool}
    (out : Fin (n + gs.length)) (L : Least n (fun x => x i || J x) gs out.val)
    (ignores : ∀ x, J (Function.update x i false) = J x) (negative : ∃ x, J x = false)
    (positive : ∃ x, J x = true) {p : ℕ} {g : Gate}
    (atGate : gs[p]? = some g) (isOr : g.op = .or) (reads : i.val ∈ g.inputs)
    (unique : ∀ q, Reads gs q i.val → q = p) :
    ∃ t < n + p, t ≠ i.val ∧
      (∀ h ∈ remove n p t gs, i.val ∉ h.inputs) ∧
      (∀ x : Fin n → Bool, x i = false → ∀ j < n + gs.length,
        vl (remove n p t gs) x (wire n p t j) = vl gs x j) ∧
      ∀ x : Fin n → Bool, vl (remove n p t gs) x (wire n p t out.val) = J x := by
  have hp : p < gs.length := (List.getElem?_eq_some_iff.mp atGate).1
  have nonconst : ∃ x y : Fin n → Bool, (x i || J x) ≠ (y i || J y) := by
    obtain ⟨x, hx⟩ := negative
    refine ⟨Function.update x i false, Function.update x i true, ?_⟩
    simp [ignores, hx]
  rcases gate_cases gs L.hcl p g atGate i.val reads with ⟨notOp, _, _⟩ | ⟨t, pins, casesOp⟩
  · cases isOr.symm.trans notOp
  rcases casesOp with ⟨andOp, _⟩ | ⟨_, gateEval⟩
  · cases isOr.symm.trans andOp
  have tIn : t ∈ g.inputs := by rcases pins with pins | pins <;> simp [pins]
  have back : t < n + p := (L.hcl p g atGate).lt t tIn
  have tOther : t ≠ i.val := by
    intro eq
    apply L.no_alias nonconst p hp i.val ((L.hcl p g atGate).lt i.val reads)
    intro x
    rw [gateEval x, eq, Bool.or_self]
  let gs' := remove n p t gs
  have noRead : ∀ h ∈ gs', i.val ∉ h.inputs := by
    intro h member input
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨q, old, notP, _, oldAt, rfl⟩ := Theta9433Bypass.old_gate hj
    obtain ⟨u, hu, image⟩ := List.mem_map.mp input
    have eq := wire_eq_raw tOther image
    exact notP (unique q ⟨old, oldAt, eq ▸ hu⟩)
  have agrees (x : Fin n → Bool) (pinned : x i = false) : ∀ j < n + gs.length,
      vl gs' x (wire n p t j) = vl gs x j := by
    apply Theta9433Bypass.eval L.hcl back x
    rw [gateEval x, vl_input gs x i.val i.isLt, pinned, Bool.false_or]
  have outOther : wire n p t out.val ≠ i.val := by
    intro eq
    have rawOut := wire_eq_raw tOther eq
    obtain ⟨x, hx⟩ := positive
    have fit := L.hev (Function.update x i false)
    change vl gs (Function.update x i false) out.val =
      ((Function.update x i false) i || J (Function.update x i false)) at fit
    rw [rawOut, vl_input _ _ _ i.isLt] at fit
    simp [ignores, hx] at fit
  refine ⟨t, back, tOther, noRead, agrees, fun x => ?_⟩
  let y := Function.update x i false
  have pinned : y i = false := by simp [y]
  calc
    vl gs' x (wire n p t out.val) = vl gs' y (wire n p t out.val) := pin_unread noRead x _ outOther
    _ = vl gs y out.val := agrees y pinned out.val out.isLt
    _ = J x := by
      have fit := L.hev y
      change vl gs y out.val = (y i || J y) at fit
      rw [fit, pinned, Bool.false_or]
      exact ignores x

theorem first_eq_out_of_unique_or {n : ℕ} {gs : List Gate} {i : Fin n}
    {J : (Fin n → Bool) → Bool} (out : Fin (n + gs.length))
    (L : Least n (fun x => x i || J x) gs out.val)
    (live : ∀ w, w ≠ out → ∃ v, readEdge gs w v) (budget : notGateCount gs ≤ 1)
    (ignores : ∀ x, J (Function.update x i false) = J x) (negative : ∃ x, J x = false)
    (positive : ∃ x, J x = true) (lower : ∀ s, HasCircuitSize n J s → gs.length ≤ s + 1)
    {p : ℕ} {g : Gate} (atGate : gs[p]? = some g) (isOr : g.op = .or)
    (reads : i.val ∈ g.inputs) (unique : ∀ q, Reads gs q i.val → q = p) :
    firstInputBoundary L.hcl out live i = out := by
  obtain ⟨t, back, tOther, noRead, agrees, computes⟩ :=
    erase_unique_or out L ignores negative positive atGate isOr reads unique
  let gs' := remove n p t gs
  have residualLeast : Least n J gs' (wire n p t out.val) := by
    refine ⟨Theta9433Bypass.clean L.hcl back, computes, fun test testOut clean fit => ?_⟩
    have sized : HasCircuitSize n J test.length := funext fit ▸ has_of_clean n test testOut clean
    have smaller : gs'.length + 1 = gs.length :=
      Theta9433Bypass.size (List.getElem?_eq_some_iff.mp atGate).1
    have bound := lower test.length sized
    omega
  let k := firstInputBoundary L.hcl out live i
  change k = out
  by_contra stoppedBefore
  have terminal : Terminal (readEdge gs) out k :=
    first_stops (readEdge gs) out (read_order L.hcl) live (inputWire gs i)
  obtain ⟨a, b, readA, readB, separate⟩ := terminal.resolve_left stoppedBefore
  have firstChild (v : Fin (n + gs.length)) (edge : readEdge gs (inputWire gs i) v) :
      v.val = n + p := by
    obtain ⟨q, old, oldAt, value, input⟩ := edge
    rw [unique q ⟨old, oldAt, input⟩] at value
    exact value
  have route := follows_is_read_path (readEdge gs) out
    (first_path (readEdge gs) out (read_order L.hcl) live (inputWire gs i))
  change Relation.ReflTransGen (readEdge gs) (inputWire gs i) k at route
  have kAfter : n + p ≤ k.val := by
    rcases route.cases_head with here | ⟨v, edge, rest⟩
    · have va := firstChild a (by rwa [here])
      have vb := firstChild b (by rwa [here])
      exact (separate (Fin.ext (va.trans vb.symm))).elim
    · rw [← firstChild v edge]
      exact path_forward (readEdge gs) (read_order L.hcl) rest
  let z := wire n p t k.val
  have zOther : z ≠ i.val := by
    intro eq
    have raw := wire_eq_raw tOther eq
    have := i.isLt
    omega
  have dominates (x : Fin n → Bool) (atWire : vl gs' x z = true) : J x = true := by
    cases jVal : J x
    · let y := Function.update x i false
      have pinned : y i = false := by simp [y]
      have cutFalse : vl gs y k.val = false :=
        (Theta9433PositiveCut.firstInputBoundary_or L.hcl out live budget i J
          L.hev x (by rw [ignores, jVal])).1
      have same := (pin_unread noRead x z zOther).trans (agrees y pinned k.val k.isLt)
      rw [atWire, cutFalse] at same
      cases same
    · rfl
  have keepRead (q : ℕ) (h : Gate) (atQ : gs[q]? = some h) (input : k.val ∈ h.inputs) :
      p < q ∧ Reads gs' (newSlot p q) z := by
    have hq := (L.hcl q h atQ).lt k.val input
    refine ⟨by omega, redirect n p t h, Theta9433Bypass.gate_at (by omega) atQ, ?_⟩
    exact List.mem_map.mpr ⟨k.val, input, rfl⟩
  obtain ⟨q, gq, atQ, va, qa⟩ := readA
  obtain ⟨r, gr, atR, vb, rb⟩ := readB
  obtain ⟨pq, hq⟩ := keepRead q gq atQ qa
  obtain ⟨pr, hr⟩ := keepRead r gr atR rb
  have indices : newSlot p q ≠ newSlot p r := by
    intro equal
    have qr : q = r := by
      simp [newSlot, show ¬ q < p by omega, show ¬ r < p by omega] at equal
      omega
    exact separate (Fin.ext (by omega))
  exact Theta9433DominatedWire.least_no_two_readers residualLeast negative dominates hq hr indices

end Theta9433NoFork

end

-- From .pnp-tools/Theta9433CoreCount.lean
section

namespace Theta9433CoreCount

open PEqualNP.CircuitLowerBounds

open BranchProof2752

open BranchProof2752.CircuitProof

open BranchProof2752.CircuitProof.Readers

open PetersenCutTrace PetersenFirstGroup

open Theta9433Leaf (tableTarget)

private def edges : List (Fin 8 × Fin 8) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6), (5, 7), (6, 7)]

private def graph : SimpleGraph (Fin 8) where
  Adj a b := (a, b) ∈ edges ∨ (b, a) ∈ edges
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by
    have noLoop : ∀ v : Fin 8, (v, v) ∉ edges := by decide +kernel
    exact fun v h => h.elim (noLoop v) (noLoop v)⟩

local instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges ∨ (b, a) ∈ edges))

private theorem alternate_neighbors : ∀ i j : Fin 8, graph.Adj i j →
    ∃ u v, graph.Adj i u ∧ graph.Adj j v ∧ u ≠ j ∧ v ≠ i ∧ ¬ graph.Adj u v := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem no_three_steps : ∀ a b c : Fin 8,
    BranchGraph.removeClass graph
      (BranchGraph.removeClass graph
        (BranchGraph.removeClass graph (BranchGraph.closeIsolates graph ∅) a) b) c ≠ Finset.univ := by
  decide +kernel

private theorem extend_finish {k : ℕ} {start : Finset (Fin 8)}
    (walk : BranchGraph.ClassSteps graph k start Finset.univ) :
    BranchGraph.ClassSteps graph (k + 1) start Finset.univ := by
  induction k generalizing start with
  | zero =>
    change Finset.univ = start at walk
    subst start
    refine ⟨0, (Finset.eq_univ_of_forall fun v => ?_).symm⟩
    exact BranchGraph.subset_removeClass graph Finset.univ 0 (Finset.mem_univ v)
  | succ k ih =>
    obtain ⟨root, rest⟩ := walk
    exact ⟨root, ih rest⟩

private theorem groups_need_four (groups : List (Finset (Fin 8)))
    (twins : BranchGraph.TwinSteps graph ∅ groups)
    (finished : BranchGraph.EdgelessAfter graph (BranchGraph.removedThrough ∅ groups)) :
    4 ≤ groups.length := by
  by_contra! fewer
  have walk := BranchGraph.covering_sequence_reaches_univ graph groups twins finished
  have triple : BranchGraph.ClassSteps graph 3 (BranchGraph.closeIsolates graph ∅) Finset.univ := by
    generalize groups.length = k at walk fewer
    interval_cases k
    · exact extend_finish (extend_finish (extend_finish walk))
    · exact extend_finish (extend_finish walk)
    · exact extend_finish walk
    · exact walk
  obtain ⟨a, b, c, complete⟩ := triple
  exact no_three_steps a b c complete.symm

private theorem tableTarget_true (x : Fin 8 → Bool) : tableTarget x = true ↔
    ∃ a b, graph.Adj a b ∧ x a = true ∧ x b = true := by
  have eq : tableTarget x = edges.any (fun e => x e.1 && x e.2) := by
    simp [tableTarget, edges, Bool.or_assoc]
  rw [eq]
  simp only [List.any_eq_true, Bool.and_eq_true, Prod.exists]
  constructor
  · rintro ⟨a, b, edge, ha, hb⟩
    exact ⟨a, b, Or.inl edge, ha, hb⟩
  · rintro ⟨a, b, edge, ha, hb⟩
    rcases edge with edge | edge
    · exact ⟨a, b, edge, ha, hb⟩
    · exact ⟨b, a, edge, hb, ha⟩

private theorem dependency_samples : ∀ v : Fin 8, ∃ w : Fin 8,
    tableTarget (Function.update (fun i => decide (i = w)) v (!(decide (v = w)))) ≠
      tableTarget (fun i => decide (i = w)) := by
  decide +kernel

private theorem depends (v : Fin 8) : Dep tableTarget v := by
  obtain ⟨w, hw⟩ := dependency_samples v
  exact ⟨fun i => decide (i = w), hw⟩

private theorem nonconstant : ∃ x y : Fin 8 → Bool, tableTarget x ≠ tableTarget y :=
  dep_nc (depends 0)

private theorem cofactor_nonconstant (v : Fin 8) (b : Bool) : ∃ x y,
    tableTarget (Function.update x v b) ≠ tableTarget (Function.update y v b) := by
  have samples : ∀ (i : Fin 8) (c : Bool),
      tableTarget (Function.update (fun _ => false) i c) ≠
        tableTarget (Function.update (fun _ => true) i c) := by
    decide +kernel
  exact ⟨fun _ => false, fun _ => true, samples v b⟩

private theorem budgetLeast {gs : List Gate} {out : Nat}
    (least : CircuitHelpers.Readers.Least 8 tableTarget gs out) :
    Least 8 tableTarget gs out :=
  least

private theorem output_valid {gs : List Gate} {out : Nat}
    (least : Least 8 tableTarget gs out) : out < 8 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

theorem least_four_branches {gs : List Gate} {out : Nat}
    (least : CircuitHelpers.Readers.Least 8 tableTarget gs out) :
    4 ≤ (circuitBranchWires (n := 8) gs).card := by
  have least := budgetLeast least
  have valid := output_valid least
  let outWire : Fin (8 + gs.length) := ⟨out, valid⟩
  have live := least_read_edge_live least nonconstant depends cofactor_nonconstant valid
  let label : Fin 8 → Fin (8 + gs.length) := firstInputBoundary least.hcl outWire live
  let branches := circuitBranchWires (n := 8) gs
  have computes (x : Fin 8 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue graph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, tableTarget_true]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset (Fin 8)) : vl gs (setInput S) outWire.val = true ↔
      BranchGraph.containsEdge graph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev, tableTarget_true]
    simp only [setInput, decide_eq_true_eq, BranchGraph.containsEdge]
    exact ⟨fun ⟨a, b, edge, ha, hb⟩ => ⟨a, ha, b, hb, edge⟩,
      fun ⟨a, ha, b, hb, edge⟩ => ⟨a, b, edge, ha, hb⟩⟩
  have independent (r) : BranchGraph.Independent graph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least nonconstant)
      graph computes alternate_neighbors r
  have labels (v : Fin 8) : label v = outWire ∨ label v ∈ branches := by
    rcases FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live
      (inputWire gs v) with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (in_circuit_branches.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup graph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live graph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp member)) (independent r)
  exact BranchGroupsLean.roots_required graph label outWire branches 4 labels before twins
    (independent outWire) groups_need_four

theorem least_size_ge_eleven_add_notGateCount {gs : List Gate} {out : Nat}
    (least : CircuitHelpers.Readers.Least 8 tableTarget gs out) :
    11 + notGateCount gs ≤ gs.length := by
  have lower := least_four_branches least
  have least := budgetLeast least
  have valid := output_valid least
  have live := least_read_edge_live least nonconstant depends cofactor_nonconstant valid
  let branches := circuitBranchWires (n := 8) gs
  have budget := branching_budget least.hcl valid (fun w hw different => by
      obtain ⟨v, p, g, hg, _, reads⟩ := live ⟨w, hw⟩ (fun eq => different (congrArg Fin.val eq))
      exact ⟨p, g, hg, reads⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at budget
  change 4 ≤ branches.card at lower
  omega

theorem least_notGateCount_le_one {gs : List Gate} {out : Nat}
    (least : CircuitHelpers.Readers.Least 8 tableTarget gs out)
    (size : gs.length ≤ 12) : notGateCount gs ≤ 1 := by
  have := least_size_ge_eleven_add_notGateCount least
  omega

end Theta9433CoreCount

end

-- From .pnp-tools/Theta9433PinOps.lean
section

namespace Theta9433PinOps

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers

open CircuitHelpers.Readers CircuitHelpers.PermInputs

open BranchProof2752 (notGateCount)

open BranchProof2752.CircuitProof (isNotGate)

open Cactus10440Floor

open Theta9433Control (target)

open Theta9433Leaf (phi tableTarget)

private theorem simplify_ops_sublist (op : GateOp) (n : Nat) (ins : List Stat) :
    ((simplify op n ins).1.toList.map Gate.op).Sublist [op] := by
  cases op <;> simp only [simplify]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;> simp [simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;> simp [simpOr]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot]
  · simp
  · simp

private theorem elim_ops_sublist (n : Nat) (gs : List Gate) (acc : List Stat × List Gate) :
    ((elim n gs acc).2.map Gate.op).Sublist (acc.2.map Gate.op ++ gs.map Gate.op) := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g tail ih =>
    rw [elim_cons]
    refine (ih (elimStep n acc g)).trans ?_
    simpa only [elimStep, List.map_append, List.map_cons, List.append_assoc,
      List.singleton_append] using
      (List.Sublist.refl (acc.2.map Gate.op)).append ((simplify_ops_sublist g.op
        (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (.const false))).append
        (List.Sublist.refl (tail.map Gate.op)))

private theorem erase_middle {α : Type} (pre post : List α) (g : α) :
    (pre ++ g :: post).eraseIdx pre.length = pre ++ post := by
  rw [List.eraseIdx_append_of_length_le (le_refl _)]; simp

private theorem pin_ops_sublist {gs : List Gate} {p : Nat} {g : Gate}
    (clean : CleanL 9 gs) (atGate : gs[p]? = some g) (readsLeaf : 3 ∈ g.inputs) :
    ((passG 8 gs 3 false).map Gate.op).Sublist ((gs.eraseIdx p).map Gate.op) := by
  have normalized := (clean p g atGate).nok
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g atGate
  let start : List Stat × List Gate := (statAt 8 3 false, [])
  let acc := elim 8 pre start
  have value : acc.1.getD 3 (.const false) = .const false := stF_self 8 pre 3 false
  have none : (simplify g.op (8 + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (.const false))).1 = none := by
    apply simplify_count
    · exact normalized.1.1
    · simpa using normalized.1.2
    · intro h; simpa using normalized.2 h
    · exact ⟨false, List.mem_map.mpr ⟨3, readsLeaf, value⟩⟩
  have skips : (elimStep 8 acc g).2 = acc.2 := by
    unfold elimStep
    dsimp only
    rw [none]
    simp
  have first := elim_ops_sublist 8 pre start
  have last := elim_ops_sublist 8 post (elimStep 8 acc g)
  rw [skips] at last
  change ((elim 8 (pre ++ g :: post) start).2.map Gate.op).Sublist _
  rw [elim_append, elim_cons, erase_middle, List.map_append]
  refine last.trans ?_
  simpa only [start, List.map_nil, List.nil_append] using
    first.append (List.Sublist.refl (post.map Gate.op))

private theorem notCount_ops (gs : List Gate) :
    notGateCount gs = (gs.map Gate.op).countP isNotGate := by
  simp only [notGateCount, ← List.countP_eq_length_filter, List.countP_map, Function.comp_def]

private theorem pin_computes {gs : List Gate} {out : Nat} (least : Least 9 target gs out) :
    ∃ w, CleanL 8 (passG 8 gs 3 false) ∧
      ∀ x : Fin 8 → Bool, vl (passG 8 gs 3 false) x w = target (ins (3 : Fin 9) false x) := by
  cases status : stF 8 gs 3 false out with
  | const c =>
    obtain ⟨x, y, diff⟩ := Theta9433Leaf.leafNonconst false
    exact (diff ((restr_const least.hcl least.hev 3 false c status x).trans
      (restr_const least.hcl least.hev 3 false c status y).symm)).elim
  | wire w =>
    refine ⟨w, ?_, fun x => ?_⟩
    · exact clean_elim 8 (List.ofFn fun _ : Fin 8 => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs least.hcl g hg).1) (inv_at 8 3 false _)
        (by simp [CleanL])
    · rw [← st_val_wire 8 gs least.hcl 3 false out w status, least.hev]

theorem pinLeafFalse_exact {gs : List Gate} {out : Nat}
    (floor : Lower 12 (cofactor target 3 false)) (least : Least 9 target gs out)
    (size : gs.length ≤ 13) :
    (passG 8 gs 3 false).length = 12 ∧ notGateCount gs = notGateCount (passG 8 gs 3 false) := by
  obtain ⟨p, _, g, _, atGate, _, ⟨reader, atReader, reads⟩, _, _, _, gateOp, _⟩ :=
    Theta9433Leaf.leafShape floor least size
  have same : reader = g := Option.some.inj (atReader.symm.trans atGate)
  subst reader
  have sublist := pin_ops_sublist least.hcl atGate reads
  have plen : p < gs.length := (List.getElem?_eq_some_iff.mp atGate).1
  have eraseSize := List.length_eraseIdx_add_one plen
  have upper := sublist.length_le
  simp only [List.length_map] at upper
  obtain ⟨w, clean, evaluates⟩ := pin_computes least
  let pass := passG 8 gs 3 false
  have actual := relabel_size (3 : Fin 9).succAbove _ _ (has_of_clean 8 pass w clean)
  have eval : (fun x : Fin 9 → Bool => vl pass (x ∘ (3 : Fin 9).succAbove) w) =
      cofactor target 3 false := by
    funext x
    rw [evaluates]
    exact congrArg target (upd_ins (3 : Fin 9) false x).symm
  rw [eval] at actual
  have lower := floor _ actual
  change 12 ≤ (passG 8 gs 3 false).length at lower
  refine ⟨by omega, ?_⟩
  have retained := sublist.eq_of_length_le (by simp only [List.length_map]; omega)
  rw [notCount_ops, notCount_ops, retained]
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g atGate
  simp [erase_middle, gateOp, isNotGate]

private def pinRelabel (i : Fin 8) : Fin 8 := phi ((3 : Fin 9).succAbove i)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
private theorem pin_relabel_evaluates : ∀ x : Fin 8 → Bool,
    target (ins (3 : Fin 9) false (x ∘ pinRelabel)) = tableTarget x := by
  decide +kernel

private theorem relabel_clean {n : Nat} (π : Fin n → Fin n) {gs : List Gate} (clean : CleanL n gs) :
    CleanL n (gs.map (relGate n n π)) := by
  intro p g atGate
  rw [List.getElem?_map] at atGate
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp atGate
  have before {w : Nat} (prior : w < n + p) : wmap n n π w < n + p := by
    unfold wmap
    split
    · rename_i h
      have := (π ⟨w, h⟩).isLt
      omega
    · omega
  rcases clean p g hg with ⟨hop, j, hj, inputs⟩ | ⟨hop, j, k, hj, hk, inputs⟩
  · exact Or.inl ⟨hop, wmap n n π j, before hj, by simp [relGate, inputs]⟩
  · exact Or.inr ⟨hop, wmap n n π j, wmap n n π k, before hj, before hk, by simp [relGate, inputs]⟩

theorem least_notGateCount_le_one {gs : List Gate} {out : Nat}
    (tableFloor : Lower 12 tableTarget) (least : Least 9 target gs out) (size : gs.length ≤ 13) :
    notGateCount gs ≤ 1 := by
  obtain ⟨len, notPreserved⟩ := pinLeafFalse_exact (Theta9433Leaf.pinLeafFalse tableFloor) least size
  obtain ⟨w, clean, evaluates⟩ := pin_computes least
  let pass := passG 8 gs 3 false
  let renamed := pass.map (relGate 8 8 pinRelabel)
  let newOut := wmap 8 8 pinRelabel w
  have computes (x : Fin 8 → Bool) : vl renamed x newOut = tableTarget x := by
    have eq : vl renamed x newOut = vl pass (x ∘ pinRelabel) w :=
      (rel_fold 8 8 pinRelabel pass _ _ (rel_init 8 8 pinRelabel x)).2.2 w
    exact eq.trans ((evaluates (x ∘ pinRelabel)).trans (pin_relabel_evaluates x))
  have renamedLen : renamed.length = 12 := by simpa [renamed, pass] using len
  have coreLeast : Least 8 tableTarget renamed newOut := by
    refine ⟨relabel_clean _ clean, computes, ?_⟩
    intro test testOut testClean testEval
    rw [renamedLen]
    exact tableFloor _ (funext testEval ▸ has_of_clean 8 test testOut testClean)
  have count := Theta9433CoreCount.least_notGateCount_le_one coreLeast renamedLen.le
  have renameNot : notGateCount renamed = notGateCount pass := by
    simp [notCount_ops, renamed, List.map_map, Function.comp_def, relGate]
  calc
    notGateCount gs = notGateCount renamed := notPreserved.trans renameNot.symm
    _ ≤ 1 := count

end Theta9433PinOps

end

-- From .pnp-tools/Theta9433JPort.lean
section

namespace Theta9433JPort

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers CircuitHelpers.Readers

open CircuitHelpers.PermInputs

open Cactus10440Floor

open Theta9433J (J)

private def mask (n : ℕ) (i : Fin 9) : Bool := n.testBit i.val

private theorem jNonconst : Nonconst (graph J []) :=
  ⟨mask 0, mask 17, by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
private theorem leftLeafBound (b : Bool) : Lower 8 (cofactor (graph J []) 2 b) := by
  cases b
  · have eq : ∀ x : Fin 9 → Bool,
        cofactor (graph J []) 2 false x = graph Theta9433J.leftStemRightTail [] x := by
      decide +kernel
    rw [funext eq]
    exact Theta9433J.leftStemRightTailBound
  · have eq : ∀ x : Fin 9 → Bool,
        cofactor (graph J []) 2 true x = graph Theta9433J.rightTail [6] x := by
      decide +kernel
    rw [funext eq]
    exact Theta9433J.rightTailOr6

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
private theorem rightLeafBound (b : Bool) : Lower 8 (cofactor (graph J []) 5 b) := by
  let π : Fin 9 → Fin 9 := ![7, 6, 5, 3, 4, 2, 1, 0, 8]
  have eq : ∀ (a : Bool) (x : Fin 9 → Bool),
      cofactor (graph J []) 5 a (x ∘ π) = cofactor (graph J []) 2 a x := by
    decide +kernel
  intro s h
  exact leftLeafBound b s (funext (eq b) ▸ relabel_size π _ s h)

private theorem noThree {gs : List Gate} {i : Fin 9} {b : Bool} {k : ℕ}
    (size : gs.length ≤ 10) (bound : Lower 8 (cofactor (graph J []) i b))
    (hk : 3 ≤ k) (pay : Drop (graph J []) i b k gs.length) : False := by
  obtain ⟨s, saved, fit⟩ := pay
  have lb := bound s fit
  omega

theorem leafShape {gs : List Gate} {o : ℕ} (L : Least 9 (graph J []) gs o)
    (size : gs.length ≤ 10) (i : Fin 9) (leaf : i = 2 ∨ i = 5) :
    ∃ p q g h, gs[p]? = some g ∧ gs[q]? = some h ∧
      Reads gs p i ∧ (∀ r, Reads gs r i → r = p) ∧
      Reads gs q (9 + p) ∧ (∀ r, Reads gs r (9 + p) → r = q) ∧
      ((g.op = .and ∧ h.op = .or) ∨ (g.op = .or ∧ h.op = .and)) := by
  have bound : ∀ b, Lower 8 (cofactor (graph J []) i b) := by
    rcases leaf with rfl | rfl
    · exact leftLeafBound
    · exact rightLeafBound
  have dep : Dep (graph J []) i := by
    rcases leaf with rfl | rfl
    · exact ⟨mask 64, by decide +kernel⟩
    · exact ⟨mask 2, by decide +kernel⟩
  have nonconst : ∀ b, Nonconst (cofactor (graph J []) i b) := by
    intro b
    rcases leaf with rfl | rfl <;> cases b <;> exact ⟨mask 0, mask 17, by decide +kernel⟩
  obtain ⟨p, g, hg, hgi⟩ := L.dep_read i dep nonconst
  have hp : Reads gs p i := ⟨g, hg, hgi⟩
  have uniqueInput (r : ℕ) (hr : Reads gs r i) : r = p := by
    by_contra different
    rcases L.two_readers i nonconst p r (Ne.symm different) hp hr with
      ⟨pay, _⟩ | ⟨pay, _⟩ | ⟨_, pay⟩
    · exact noThree size (bound false) (by decide) pay
    · exact noThree size (bound false) (by decide) pay
    · exact noThree size (bound true) (by decide) pay
  have hc := isC_reader L.hcl i p g hg hgi (fixBit g) (Or.inr rfl)
  obtain ⟨q, hpq, hq, hqr⟩ := L.next i (fixBit g) (nonconst _) p (reads_len hp) hc
  have uniqueHead (r : ℕ) (hr : Reads gs r (9 + p)) : r = q := by
    by_contra different
    have hpr := reads_lt L.hcl hr
    exact noThree size (bound _) (by decide) (L.save3 i _ (nonconst _) p q r
      (by omega) (by omega) (Ne.symm different)
      (rc_input _ hp) hqr (rc_of_reads hr hc))
  have noConst (b c : Bool) (first : IsC 8 gs i b (9 + p)) :
      stF 8 gs i b (9 + q) ≠ Stat.const c := by
    intro eq
    obtain ⟨r, hrq, _, hrr⟩ := L.next i b (nonconst b) q (reads_len hq) ⟨c, eq⟩
    exact noThree size (bound b) (by decide) (L.save3 i b (nonconst b) p q r
      (by omega) (by omega) (by omega) (rc_input b hp) (rc_of_reads hq first) hrr)
  obtain ⟨h, hh, hhp⟩ := hq
  refine ⟨p, q, g, h, hg, hh, hp, uniqueInput, ⟨h, hh, hhp⟩, uniqueHead, ?_⟩
  obtain ⟨c, hpc⟩ := hc
  have shape := st_shape 8 gs L.hcl i (fixBit g) q h hh (9 + p) hhp c hpc
    (fun c' => noConst _ c' ⟨c, hpc⟩)
  have inputVal (b : Bool) : vl gs (ins i b (fun _ : Fin 8 => false)) i.val = b := by
    rw [vl_input gs _ _ i.isLt]
    exact Fin.insertNth_apply_same (α := fun _ : Fin 9 => Bool) i b (fun _ => false)
  rcases gate_cases gs L.hcl p g hg i.val hgi with
    ⟨gNot, _, meaning⟩ | ⟨_, _, gAnd | gOr⟩
  · exfalso
    let b := !fixBit h
    obtain ⟨v, hv⟩ := isC_reader L.hcl i p g hg hgi b (Or.inl gNot)
    have eval := st_val_const 8 gs L.hcl i b (9 + p) v hv (fun _ => false)
    rw [meaning, inputVal] at eval
    have fixed : v = fixBit h := by rw [← eval]; simp [b]
    obtain ⟨d, hd⟩ := const_read 8 gs L.hcl i b q h hh (9 + p) hhp (fixed ▸ hv)
    exact noConst b d ⟨v, hv⟩ hd
  · refine Or.inl ⟨gAnd.1, ?_⟩
    have bb : fixBit g = false := by simp [fixBit, gAnd.1]
    have eval := st_val_const 8 gs L.hcl i (fixBit g) (9 + p) c hpc (fun _ => false)
    rw [gAnd.2, inputVal, bb, Bool.false_and] at eval
    rcases shape.1 with hAnd | hOr
    · exact False.elim (shape.2.1 (by simpa [fixBit, hAnd] using eval.symm))
    · exact hOr
  · refine Or.inr ⟨gOr.1, ?_⟩
    have bb : fixBit g = true := by simp [fixBit, gOr.1]
    have eval := st_val_const 8 gs L.hcl i (fixBit g) (9 + p) c hpc (fun _ => false)
    rw [gOr.2, inputVal, bb, Bool.true_or] at eval
    rcases shape.1 with hAnd | hOr
    · exact hAnd
    · exact False.elim (shape.2.1 (by simpa [fixBit, hOr] using eval.symm))

private def singleton (i j : Fin 9) : Bool := decide (j = i)

private theorem singletonSupport {gs : List Gate} {o p q : ℕ} {i : Fin 9} {g h : Gate}
    (L : Least 9 (graph J []) gs o)
    (monotone : ∀ (r : ℕ) (k : Gate), gs[r]? = some k → k.op ≠ .not)
    (hg : gs[p]? = some g) (hh : gs[q]? = some h)
    (uniqueInput : ∀ r, Reads gs r i → r = p)
    (uniqueHead : ∀ r, Reads gs r (9 + p) → r = q)
    (shape : (g.op = .and ∧ h.op = .or) ∨ (g.op = .or ∧ h.op = .and)) :
    ∀ w, vl gs (singleton i) w = true → w = i.val ∨ (w = 9 + p ∧ g.op = .or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro value
    by_cases primary : w < 9
    · rw [vl_input gs _ w primary] at value
      exact Or.inl (congrArg Fin.val (of_decide_eq_true value))
    obtain ⟨r, rfl⟩ : ∃ r, w = 9 + r := ⟨w - 9, by omega⟩
    cases hr : gs[r]? with
    | none =>
      have out : gs.length ≤ r := List.getElem?_eq_none_iff.mp hr
      rw [vl_beyond gs _ _ (by omega)] at value
      contradiction
    | some k =>
      rcases L.hcl r k hr with ⟨op, _⟩ | ⟨op, a, b, ha, hb, hargs⟩
      · exact (monotone r k hr op).elim
      have read (c : ℕ) (hc : c = a ∨ c = b) : Reads gs r c :=
        ⟨k, hr, by simpa [hargs] using hc⟩
      have headOp (eq : r = p) : k.op = g.op := by
        subst r
        exact congrArg Gate.op (Option.some.inj (hr.symm.trans hg))
      rw [vl_gate gs L.hcl _ r k hr, hargs] at value
      rcases op with op | op
      · have values : vl gs (singleton i) a = true ∧ vl gs (singleton i) b = true := by
          simpa [op, GateOp.eval] using value
        have distinct : a ≠ b := by
          intro eq
          subst b
          have hrSize := (List.getElem?_eq_some_iff.mp hr).1
          apply L.no_alias jNonconst r hrSize a ha
          intro x
          simp [vl_gate gs L.hcl x r k hr, hargs, op, GateOp.eval]
        rcases ih a ha values.1 with aInput | ⟨aHead, _⟩ <;>
          rcases ih b hb values.2 with bInput | ⟨bHead, _⟩
        · exact (distinct (aInput.trans bInput.symm)).elim
        · have eq := uniqueInput r (read i (Or.inl aInput.symm))
          omega
        · have eq := uniqueInput r (read i (Or.inr bInput.symm))
          omega
        · exact (distinct (aHead.trans bHead.symm)).elim
      · have values : vl gs (singleton i) a = true ∨ vl gs (singleton i) b = true := by
          simpa [op, GateOp.eval] using value
        obtain ⟨c, hc, bound, hcval⟩ : ∃ c, (c = a ∨ c = b) ∧ c < 9 + r ∧
            vl gs (singleton i) c = true :=
          values.elim (fun h => ⟨a, Or.inl rfl, ha, h⟩) (fun h => ⟨b, Or.inr rfl, hb, h⟩)
        rcases ih c bound hcval with atInput | ⟨atHead, hOr⟩
        · have eq := uniqueInput r (atInput ▸ read c hc)
          exact Or.inr ⟨by omega, (headOp eq).symm.trans op⟩
        · have eq := uniqueHead r (atHead ▸ read c hc)
          subst r
          have op' := congrArg Gate.op (Option.some.inj (hh.symm.trans hr))
          rcases shape with ⟨hAnd, _⟩ | ⟨_, hAnd⟩
          · rw [hAnd] at hOr
            contradiction
          · rw [op, hAnd] at op'
            contradiction

private theorem agreeThroughHead {gs : List Gate} {p : ℕ}
    (clean : CleanL 9 gs) (x y : Fin 9 → Bool)
    (input : ∀ i, i ≠ 2 → i ≠ 5 → x i = y i)
    (leafReaders : ∀ r, (Reads gs r 2 ∨ Reads gs r 5) → r = p)
    (head : vl gs x (9 + p) = vl gs y (9 + p)) :
    ∀ w, w ≠ 2 → w ≠ 5 → vl gs x w = vl gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h2 h5
    by_cases primary : w < 9
    · rw [vl_input gs x w primary, vl_input gs y w primary]
      exact input ⟨w, primary⟩ (fun h => h2 (congrArg Fin.val h)) (fun h => h5 (congrArg Fin.val h))
    obtain ⟨r, rfl⟩ : ∃ r, w = 9 + r := ⟨w - 9, by omega⟩
    by_cases cut : r = p
    · simpa [cut] using head
    cases hr : gs[r]? with
    | none =>
      have out : gs.length ≤ r := List.getElem?_eq_none_iff.mp hr
      rw [vl_beyond gs x _ (by omega), vl_beyond gs y _ (by omega)]
    | some k =>
      apply vl_congr gs clean x y r k hr
      intro a ha
      apply ih a ((clean r k hr).lt a ha)
      · intro eq
        exact cut (leafReaders r (Or.inl ⟨k, hr, eq ▸ ha⟩))
      · intro eq
        exact cut (leafReaders r (Or.inr ⟨k, hr, eq ▸ ha⟩))

theorem noLeafOrPortMonotone {gs : List Gate} {o w : ℕ} (L : Least 9 (graph J []) gs o)
    (size : gs.length ≤ 10) (monotone : ∀ (r : ℕ) (k : Gate), gs[r]? = some k → k.op ≠ .not)
    (port : ∀ x, graph J [] x = false → vl gs x w = (x 2 || x 5)) : False := by
  obtain ⟨p, q, g, h, hg, hh, hp, unique2, _, head2, shape2⟩ := leafShape L size 2 (Or.inl rfl)
  obtain ⟨p', q', g', h', hg', hh', hp', unique5, _, head5, shape5⟩ := leafShape L size 5 (Or.inr rfl)
  have lit2 : vl gs (singleton 2) w = true := (port _ (by decide +kernel)).trans (by decide +kernel)
  have lit5 : vl gs (singleton 5) w = true := (port _ (by decide +kernel)).trans (by decide +kernel)
  have not2 : w ≠ 2 := by
    intro eq
    rw [eq, vl_input gs _ _ (by decide : 2 < 9)] at lit5
    exact Bool.noConfusion lit5
  have not5 : w ≠ 5 := by
    intro eq
    rw [eq, vl_input gs _ _ (by decide : 5 < 9)] at lit2
    exact Bool.noConfusion lit2
  obtain ⟨wire2, op2⟩ := (singletonSupport L monotone hg hh unique2 head2 shape2 w lit2).resolve_left not2
  obtain ⟨wire5, _⟩ := (singletonSupport L monotone hg' hh' unique5 head5 shape5 w lit5).resolve_left not5
  have eq : p' = p := by omega
  subst p'
  obtain ⟨g₂, hg₂, reads2⟩ := hp
  obtain ⟨g₅, hg₅, reads5⟩ := hp'
  have e₂ := Option.some.inj (hg₂.symm.trans hg)
  have e₅ := Option.some.inj (hg₅.symm.trans hg)
  subst g₂
  subst g₅
  have head (x : Fin 9 → Bool) : vl gs x (9 + p) = (x 2 || x 5) := by
    rcases gate_cases gs L.hcl p g hg 2 reads2 with ⟨bad, _⟩ | ⟨a, args, andCase | orCase⟩
    · exact (monotone p g hg bad).elim
    · have bad := andCase.1
      rw [op2] at bad
      contradiction
    have other : a = 5 := by
      rcases args with args | args <;> simp [args] at reads5 <;> omega
    rw [orCase.2, other, vl_input gs x 2 (by decide), vl_input gs x 5 (by decide)]
    rfl
  have out2 : o ≠ 2 := by
    intro eq
    have h := L.hev (singleton 2)
    rw [eq, vl_input gs _ 2 (by decide)] at h
    exact Bool.noConfusion h
  have out5 : o ≠ 5 := by
    intro eq
    have h := L.hev (singleton 5)
    rw [eq, vl_input gs _ 5 (by decide)] at h
    exact Bool.noConfusion h
  have agree := agreeThroughHead L.hcl (mask 68) (mask 96) (by decide +kernel)
    (fun r hr => hr.elim (unique2 r) (unique5 r)) (by rw [head, head]; decide +kernel) o out2 out5
  rw [L.hev, L.hev] at agree
  exact Bool.noConfusion agree

open BranchProof2752
  (least_read_edge_live branch_slots_of_read_edges circuitBranchWires in_circuit_branches
    branching_budget notGateCount)

open BranchProof2752.CircuitProof (isNotGate)

open BranchProof2752.PetersenCutTrace
  (readEdge read_order inputWire avoid circuit_cut_agreement predecessors predecessors_mem
    predecessors_nodup predecessors_nil_input predecessors_val_gate)

open BranchProof2752.PetersenFirstGroup
  (firstInputBoundary firstInputBoundary_occurrences_le_one firstInputGroup_controlled
    mem_firstInputGroup wire_le_output)

open BranchProof2752.PetersenCutIndependent
  (cut_factors wireFormula_count_input_fin)

open BranchProof2752.PetersenCutFormula
  (wireFormula wireFormula_eval wireFormula_count_gate_fin)

open BranchProof2752.PetersenScratch (occurrences fixed_pair_invariant pairInput pairValue)

open BranchProof2752.FirstBranchRoute
  (Avoid Follow follow_unique read_before first_stops no_avoiding_after weight_before_le_one)

private def compress : Fin 9 → Fin 7 := ![0, 1, 2, 0, 3, 4, 5, 6, 0]

private def expand : Fin 7 → Fin 9 := ![0, 1, 2, 4, 5, 6, 7]

private def J7 (x : Fin 7 → Bool) : Bool := graph J [] (x ∘ compress)

private def mask7 (n : ℕ) (i : Fin 7) : Bool := n.testBit i.val

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
private theorem J7Bound : Lower 10 J7 := by
  have eq : ∀ x : Fin 9 → Bool, J7 (x ∘ expand) = graph J [] x := by decide +kernel
  intro s fits
  exact Theta9433J.JBound s (funext eq ▸ relabel_size expand J7 s fits)

private theorem J7Nonconst : Nonconst J7 := ⟨mask7 0, mask7 9, by decide +kernel⟩

private theorem J7Dep (i : Fin 7) : Dep J7 i := by
  let near : Fin 7 → ℕ := ![8, 16, 32, 1, 2, 4, 1]
  have h : ∀ (i : Fin 7), J7 (Function.update (mask7 (near i)) i (!(mask7 (near i) i))) ≠
      J7 (mask7 (near i)) := by decide +kernel
  exact ⟨mask7 (near i), h i⟩

private theorem J7RestrNC (i : Fin 7) (b : Bool) : Nonconst (cofactor J7 i b) := by
  have h : ∀ (i : Fin 7) (b : Bool), cofactor J7 i b (mask7 0) ≠ cofactor J7 i b (mask7 127) := by
    decide +kernel
  exact ⟨mask7 0, mask7 127, h i b⟩

private theorem wmap_lt {n m : ℕ} (π : Fin n → Fin m) {a p : ℕ} (h : a < n + p) :
    wmap n m π a < m + p := by
  unfold wmap
  split
  · rename_i ha
    have bound := (π ⟨a, ha⟩).isLt
    omega
  · omega

private theorem relabelClean {n m : ℕ} (π : Fin n → Fin m) {gs : List Gate}
    (clean : CleanL n gs) : CleanL m (gs.map (relGate n m π)) := by
  intro p g' hg'
  rw [List.getElem?_map] at hg'
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hg'
  rcases clean p g hg with ⟨op, a, ha, args⟩ | ⟨ops, a, b, ha, hb, args⟩
  · exact Or.inl ⟨op, wmap n m π a, wmap_lt π ha, by simp [relGate, args]⟩
  · exact Or.inr ⟨ops, wmap n m π a, wmap n m π b, wmap_lt π ha, wmap_lt π hb,
      by simp [relGate, args]⟩

private theorem relabelValue {n m : ℕ} (π : Fin n → Fin m) (gs : List Gate)
    (x : Fin m → Bool) (w : ℕ) :
    vl (gs.map (relGate n m π)) x (wmap n m π w) = vl gs (x ∘ π) w :=
  (rel_fold n m π gs _ _ (rel_init n m π x)).2.2 w

private theorem unateCombine {n : ℕ} (i : Fin n) (a b : DMFormula n)
    (op : Bool → Bool → Bool)
    (mono : ∀ (v w v' w' : Bool), v ≤ v' → w ≤ w' → op v w ≤ op v' w')
    (small : occurrences i a + occurrences i b ≤ 1)
    (absent : ∀ p : DMFormula n, occurrences i p = 0 → ∀ x,
      p.eval (Function.update x i false) = p.eval (Function.update x i true))
    (ha : occurrences i a ≤ 1 → ∃ s : Bool, ∀ x,
      a.eval (Function.update x i (!s)) ≤ a.eval (Function.update x i s))
    (hb : occurrences i b ≤ 1 → ∃ s : Bool, ∀ x,
      b.eval (Function.update x i (!s)) ≤ b.eval (Function.update x i s)) :
    ∃ s : Bool, ∀ x,
      op (a.eval (Function.update x i (!s))) (b.eval (Function.update x i (!s))) ≤
      op (a.eval (Function.update x i s)) (b.eval (Function.update x i s)) := by
  have fixed (p : DMFormula n) (zero : occurrences i p = 0) (s : Bool) (x : Fin n → Bool) :
      p.eval (Function.update x i (!s)) ≤ p.eval (Function.update x i s) := by
    have eq := absent p zero x
    cases s
    · exact le_of_eq eq.symm
    · exact le_of_eq eq
  by_cases az : occurrences i a = 0
  · obtain ⟨s, dir⟩ := hb (by omega)
    exact ⟨s, fun x => mono _ _ _ _ (fixed a az s x) (dir x)⟩
  · obtain ⟨s, dir⟩ := ha (by omega)
    exact ⟨s, fun x => mono _ _ _ _ (dir x) (fixed b (by omega) s x)⟩

private theorem unateReadOnce {n : ℕ} (i : Fin n) (p : DMFormula n)
    (count : occurrences i p ≤ 1) :
    ∃ s : Bool, ∀ x, p.eval (Function.update x i (!s)) ≤ p.eval (Function.update x i s) := by
  have absent (q : DMFormula n) (zero : occurrences i q = 0) (x : Fin n → Bool) :
      q.eval (Function.update x i false) = q.eval (Function.update x i true) := by
    induction q with
    | lit j s =>
      have ne : j ≠ i := by
        intro eq
        simp [occurrences, eq] at zero
      simp [DMFormula.eval, Function.update_of_ne ne]
    | and a b ihA ihB =>
      simp only [occurrences, Nat.add_eq_zero_iff] at zero
      simp only [DMFormula.eval, ihA zero.1, ihB zero.2]
    | or a b ihA ihB =>
      simp only [occurrences, Nat.add_eq_zero_iff] at zero
      simp only [DMFormula.eval, ihA zero.1, ihB zero.2]
  induction p with
  | lit j s =>
    by_cases ne : j = i
    · subst j
      refine ⟨s, fun x => ?_⟩
      cases s <;> simp [DMFormula.eval]
    · exact ⟨true, fun x => le_of_eq (absent (.lit j s) (by simp [occurrences, ne]) x)⟩
  | and a b ihA ihB =>
    exact unateCombine i a b (· && ·) (by decide) count absent ihA ihB
  | or a b ihA ihB =>
    exact unateCombine i a b (· || ·) (by decide) count absent ihA ihB

private theorem occurrencesBeforeBranch {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (i : Fin n) (q : Fin (n + gs.length)) (before : q ≤ firstInputBoundary clean out live i) :
    occurrences i (wireFormula i gs q.val) ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences i (wireFormula i gs a.val)
  have atSource : weight (inputWire gs i) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin i i _ i.isLt, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs i →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin i i w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin i i clean atSlot hw _ (predecessors_val_gate clean w atSlot hw)
  exact weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs i) otherWeight atSource distinct before

private theorem prefixBlocks {n : ℕ} {gs : List Gate} {cut out src : Fin (n + gs.length)}
    (terminal : cut ≠ out) (chain : Relation.ReflTransGen (Follow (readEdge gs) out) src cut) :
    ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) src out := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro bypass
    rcases bypass.cases_head with same | ⟨_, edge, _⟩
    · exact terminal same
    · exact edge.2.1 rfl
  | @head start next step _ ih =>
    intro bypass
    rcases bypass.cases_head with same | ⟨alt, edge, tail⟩
    · exact step.2 (Or.inl same)
    · have eq : next = alt := follow_unique (readEdge gs) out step ⟨edge.1, step.2⟩
      exact ih (eq.symm ▸ tail)

private theorem leafBeforePort {gs : List Gate} (clean : CleanL 7 gs)
    (out q : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (compute : ∀ x : Fin 7 → Bool, vl gs x out.val = J7 x)
    (port : ∀ x : Fin 7 → Bool, J7 x = false → vl gs x q.val = (x 2 || x 4))
    (i : Fin 7) (leaf : i = 2 ∨ i = 4) : firstInputBoundary clean out live i < q := by
  let x₀ := mask7 0
  let x₁ := Function.update x₀ i true
  let y₀ := mask7 (if i = 2 then 48 else 6)
  let y₁ := Function.update y₀ i true
  have samples : J7 x₀ = false ∧ J7 x₁ = false ∧ (x₀ 2 || x₀ 4) = false ∧
      (x₁ 2 || x₁ 4) = true ∧ J7 y₀ = false ∧ J7 y₁ = true ∧ (y₀ 2 || y₀ 4) = true ∧
      x₀ i = false ∧ y₀ i = false := by
    rcases leaf with rfl | rfl <;> decide +kernel
  obtain ⟨f₀, f₁, p₀, p₁, fy₀, fy₁, py₀, xoff, yoff⟩ := samples
  have q₀ := (port x₀ f₀).trans p₀
  have q₁ := (port x₁ f₁).trans p₁
  have qy₀ := (port y₀ fy₀).trans py₀
  have notOut : q ≠ out := by
    intro eq
    rw [eq, compute, f₁] at q₁
    contradiction
  have modified (x : Fin 7 → Bool) (j : Fin 7) (diff : x j ≠ Function.update x i true j) : j = i := by
    by_contra other
    exact diff (Function.update_of_ne other _ _).symm
  have route : Relation.ReflTransGen (readEdge gs) (inputWire gs i) q := by
    by_contra absent
    have sameOut : vl gs x₀ out.val = vl gs x₁ out.val := by rw [compute, compute, f₀, f₁]
    have eq := circuit_cut_agreement clean out q x₀ x₁ sameOut (by
      intro j diff path
      have ji := modified x₀ j diff
      subst j
      exact absent (Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ path))
    change vl gs x₀ q.val = vl gs x₁ q.val at eq
    rw [q₀, q₁] at eq
    contradiction
  by_contra! early
  
  have chain := (read_before (readEdge gs) out (read_order clean) live route early).1
  have count := occurrencesBeforeBranch clean out live distinct i q early
  obtain ⟨s, direction⟩ := unateReadOnce i _ count
  have positive : s = true := by
    cases s
    · have opp := direction x₀
      rw [wireFormula_eval i clean _ _ q.isLt, wireFormula_eval i clean _ _ q.isLt] at opp
      have noChange : Function.update x₀ i false = x₀ := Function.update_eq_self_iff.mpr xoff.symm
      change vl gs x₁ q.val ≤ vl gs (Function.update x₀ i false) q.val at opp
      rw [q₁, noChange, q₀] at opp
      exact (by decide : ¬ true ≤ false) opp |>.elim
    · rfl
  rw [positive] at direction
  have grows := direction y₀
  rw [wireFormula_eval i clean _ _ q.isLt, wireFormula_eval i clean _ _ q.isLt] at grows
  have noChange : Function.update y₀ i false = y₀ := Function.update_eq_self_iff.mpr yoff.symm
  change vl gs (Function.update y₀ i false) q.val ≤ vl gs y₁ q.val at grows
  rw [noChange] at grows
  have sameQ : vl gs y₀ q.val = vl gs y₁ q.val := by
    rw [qy₀] at grows ⊢
    cases h : vl gs y₁ q.val
    · rw [h] at grows
      exact (by decide : ¬ true ≤ false) grows |>.elim
    · rfl
  have sameOut := circuit_cut_agreement clean q out y₀ y₁ sameQ (by
    intro j diff
    have ji := modified y₀ j diff
    subst j
    exact prefixBlocks notOut chain)
  change vl gs y₀ out.val = vl gs y₁ out.val at sameOut
  rw [compute, compute, fy₀, fy₁] at sameOut
  contradiction

private theorem sharedBoundaryAgree {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out z : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i j : Fin n) (same : firstInputBoundary clean out live i = firstInputBoundary clean out live j)
    (after : firstInputBoundary clean out live i ≤ z) (x y : Fin n → Bool)
    (changes : ∀ k, x k ≠ y k → k = i ∨ k = j)
    (sameCut : vl gs x (firstInputBoundary clean out live i).val =
      vl gs y (firstInputBoundary clean out live i).val) : vl gs x z.val = vl gs y z.val := by
  rcases lt_or_eq_of_le after with later | eq
  · apply circuit_cut_agreement clean _ z x y sameCut
    intro k diff bypass
    have atK : firstInputBoundary clean out live k = firstInputBoundary clean out live i := by
      rcases changes k diff with rfl | rfl
      · rfl
      · exact same.symm
    have noBypass := no_avoiding_after (readEdge gs) out (read_order clean) live
      (v := inputWire gs k) (w := z) (by
        change firstInputBoundary clean out live k < z
        rwa [atK])
    change ¬ Relation.ReflTransGen (Avoid (readEdge gs) (firstInputBoundary clean out live k))
      (inputWire gs k) z at noBypass
    rw [atK] at noBypass
    exact noBypass (Relation.ReflTransGen.mono (fun _ _ h => ⟨h.1, h.2.1⟩) _ _ bypass)
  · rwa [← eq]

private def portPairs : List (Fin 7 × Fin 7) :=
  [(2, 4), (2, 0), (2, 3), (2, 6), (4, 0), (4, 3), (4, 6)]

private def portInput (e : Fin 7 × Fin 7) : Bool → Bool → (Fin 7 → Bool) :=
  pairInput e.1 e.2 (mask7 (if e = (2, 4) then 2 else if e.2 = 0 then 8 else 1))

private theorem portPairSamples : ∀ e ∈ portPairs,
    (e.1 = 2 ∨ e.1 = 4) ∧ J7 (portInput e false false) = false ∧
      J7 (portInput e true false) = false ∧ J7 (portInput e false true) = true ∧
      (portInput e false false 2 || portInput e false false 4) = false ∧
      (portInput e true false 2 || portInput e true false 4) = true := by
  decide +kernel

private theorem portPairSeparated {gs : List Gate} (clean : CleanL 7 gs)
    (out q : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (compute : ∀ x : Fin 7 → Bool, vl gs x out.val = J7 x)
    (port : ∀ x : Fin 7 → Bool, J7 x = false → vl gs x q.val = (x 2 || x 4))
    (e : Fin 7 × Fin 7) (member : e ∈ portPairs) :
    firstInputBoundary clean out live e.1 ≠ firstInputBoundary clean out live e.2 := by
  intro same
  let cut := firstInputBoundary clean out live e.1
  let x₀ := portInput e false false
  let x₁ := portInput e true false
  let x₂ := portInput e false true
  obtain ⟨leaf, f₀, f₁, f₂, p₀, p₁⟩ := portPairSamples e member
  have at₀ := (port x₀ f₀).trans p₀
  have at₁ := (port x₁ f₁).trans p₁
  have beforeQ : cut ≤ q := (leafBeforePort clean out q live distinct compute port e.1 leaf).le
  have beforeOut : cut ≤ out := wire_le_output clean out live cut
  have changes (a b c d : Bool) (k : Fin 7) (diff : portInput e a b k ≠ portInput e c d k) :
      k = e.1 ∨ k = e.2 := by
    by_contra! off
    exact diff (by simp [portInput, pairInput, off.1, off.2])
  have d₀₁ : vl gs x₀ cut.val ≠ vl gs x₁ cut.val := by
    intro eq
    have h := sharedBoundaryAgree clean out q live e.1 e.2 same beforeQ x₀ x₁ (changes _ _ _ _) eq
    rw [at₀, at₁] at h
    contradiction
  have d₀₂ : vl gs x₀ cut.val ≠ vl gs x₂ cut.val := by
    intro eq
    have h := sharedBoundaryAgree clean out out live e.1 e.2 same beforeOut x₀ x₂ (changes _ _ _ _) eq
    change vl gs (portInput e false false) out.val = vl gs (portInput e false true) out.val at h
    rw [compute, compute, f₀, f₂] at h
    contradiction
  have d₁₂ : vl gs x₁ cut.val ≠ vl gs x₂ cut.val := by
    intro eq
    have h := sharedBoundaryAgree clean out out live e.1 e.2 same beforeOut x₁ x₂ (changes _ _ _ _) eq
    change vl gs (portInput e true false) out.val = vl gs (portInput e false true) out.val at h
    rw [compute, compute, f₁, f₂] at h
    contradiction
  exact (by decide : ∀ a b c : Bool, a ≠ b → a ≠ c → b ≠ c → False) _ _ _ d₀₁ d₀₂ d₁₂

private def trianglePairs : List (Fin 7 × Fin 7) := [(0, 3), (0, 6), (3, 6)]

private def triangleBase (e : Fin 7 × Fin 7) : Fin 7 → Bool :=
  mask7 (if e = (0, 3) then 64 else if e = (0, 6) then 8 else 1)

private theorem triangleSamples : ∀ e ∈ trianglePairs, ∀ a b : Bool,
    J7 (pairInput e.1 e.2 (mask7 0) a b) = (a && b) ∧
    J7 (pairInput e.1 e.2 (triangleBase e) a b) = (a || b) := by
  decide +kernel

private theorem trianglePairSeparated {gs : List Gate} (clean : CleanL 7 gs)
    (out : Fin (7 + gs.length))
    (live : ∀ w : Fin (7 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (compute : ∀ x : Fin 7 → Bool, vl gs x out.val = J7 x)
    (e : Fin 7 × Fin 7) (member : e ∈ trianglePairs) :
    firstInputBoundary clean out live e.1 ≠ firstInputBoundary clean out live e.2 := by
  intro same
  let cut := firstInputBoundary clean out live e.1
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin 7, k = e.1 ∨ k = e.2 →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with last | blockers
    · exact Or.inl last
    · refine Or.inr (fun k hk => blockers k ((mem_firstInputGroup clean out live cut k).mpr ?_))
      rcases hk with rfl | rfl
      · rfl
      · exact same.symm
  have factor (base : Fin 7 → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue e.1 e.2 base (wireFormula e.1 gs cut.val) a b) =
      J7 (pairInput e.1 e.2 base a b) := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = e.1 ∨ k = e.2) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ _ cut.isLt]
    change outer (vl gs (pairInput e.1 e.2 base a b) cut.val) = J7 (pairInput e.1 e.2 base a b)
    rw [← compute]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ e.1 from fun h => hk (Or.inl h),
      show k ≠ e.2 from fun h => hk (Or.inr h)]
  obtain ⟨outerA, ha⟩ := factor (mask7 0)
  obtain ⟨outerO, ho⟩ := factor (triangleBase e)
  exact fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (triangleSamples e member a b).1)
    (fun a b => (ho a b).trans (triangleSamples e member a b).2)

private def markedVertices : Finset (Fin 7) := {2, 4, 0, 3, 6}

private theorem checkedPairs : ∀ i ∈ markedVertices, ∀ j ∈ markedVertices, i ≠ j →
    (i, j) ∈ portPairs ++ trianglePairs ∨ (j, i) ∈ portPairs ++ trianglePairs := by
  decide +kernel

private theorem noNotOfPort {gs : List Gate} {o q : ℕ} (L : Least 7 J7 gs o)
    (size : gs.length ≤ 10) (qValid : q < 7 + gs.length)
    (port : ∀ x : Fin 7 → Bool, J7 x = false → vl gs x q = (x 2 || x 4)) :
    ∀ (r : ℕ) (g : Gate), gs[r]? = some g → g.op ≠ .not := by
  classical
  have outValid : o < 7 + gs.length := by
    by_contra! beyond
    obtain ⟨x, y, diff⟩ := L.ncv J7Nonconst
    exact diff ((vl_beyond gs x o beyond).trans (vl_beyond gs y o beyond).symm)
  let out : Fin (7 + gs.length) := ⟨o, outValid⟩
  let qWire : Fin (7 + gs.length) := ⟨q, qValid⟩
  let least : BranchProof2752.CircuitProof.Readers.Least 7 J7 gs o :=
    L
  have live := least_read_edge_live least J7Nonconst J7Dep J7RestrNC outValid
  have distinct := predecessors_nodup least J7Nonconst
  let label : Fin 7 → Fin (7 + gs.length) := firstInputBoundary L.hcl out live
  have pairwise (e : Fin 7 × Fin 7) (member : e ∈ portPairs ++ trianglePairs) :
      label e.1 ≠ label e.2 := by
    rcases List.mem_append.mp member with hp | ht
    · exact portPairSeparated L.hcl out qWire live distinct L.hev port e hp
    · exact trianglePairSeparated L.hcl out live distinct L.hev e ht
  have inj : Set.InjOn label (↑markedVertices : Set (Fin 7)) := by
    intro i hi j hj equal
    by_contra different
    rcases checkedPairs i hi j hj different with hp | ht
    · exact pairwise (i, j) hp equal
    · exact pairwise (j, i) ht equal.symm
  let branches := circuitBranchWires (n := 7) gs
  have subset : markedVertices.image label ⊆ insert out branches := by
    intro w member
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
    rcases first_stops (readEdge gs) out (read_order L.hcl) live (inputWire gs i) with result | fork
    · exact Finset.mem_insert.mpr (Or.inl result)
    · exact Finset.mem_insert.mpr (Or.inr (in_circuit_branches.mpr fork))
  have numLabels : (markedVertices.image label).card = 5 := by
    rw [Finset.card_image_of_injOn inj]
    decide +kernel
  have lower : 4 ≤ branches.card := by
    have more := Finset.card_le_card subset
    have atMost := Finset.card_insert_le out branches
    omega
  have budget := branching_budget L.hcl outValid (fun w hw hne => by
    let wire : Fin (7 + gs.length) := ⟨w, hw⟩
    obtain ⟨_, p, g, atSlot, _, reads⟩ := live wire (fun eq => hne (congrArg Fin.val eq))
    exact ⟨p, g, atSlot, reads⟩)
    (branches.image Fin.val) (fun w member => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp member
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at budget
  have notZero : notGateCount gs = 0 := by omega
  have noNot : (gs.filter fun g => isNotGate g.op) = [] := List.length_eq_zero_iff.mp notZero
  intro r g atSlot op
  have member : g ∈ gs.filter (fun g => isNotGate g.op) :=
    List.mem_filter.mpr ⟨List.mem_iff_getElem?.mpr ⟨r, atSlot⟩, by simp [op, isNotGate]⟩
  rw [noNot] at member
  exact List.not_mem_nil member

theorem noLeafOrPort {gs : List Gate} {o q : ℕ} (clean : CleanL 9 gs)
    (computes : ∀ x : Fin 9 → Bool, vl gs x o = graph J [] x) (size : gs.length ≤ 10)
    (port : ∀ x : Fin 9 → Bool, graph J [] x = false → vl gs x q = (x 2 || x 5)) : False := by
  let gs₇ := gs.map (relGate 9 7 compress)
  let o₇ := wmap 9 7 compress o
  let q₇ := wmap 9 7 compress q
  have length : gs₇.length = gs.length := by simp [gs₇]
  have clean₇ : CleanL 7 gs₇ := relabelClean compress clean
  have eval₇ (x : Fin 7 → Bool) : vl gs₇ x o₇ = J7 x :=
    (relabelValue compress gs x o).trans (computes (x ∘ compress))
  have size₇ : gs₇.length ≤ 10 := by omega
  have least₇ : Least 7 J7 gs₇ o₇ := ⟨clean₇, eval₇, fun hs ho hc fit =>
    size₇.trans (J7Bound hs.length (funext fit ▸ has_of_clean 7 hs ho hc))⟩
  have port₇ (x : Fin 7 → Bool) (zero : J7 x = false) : vl gs₇ x q₇ = (x 2 || x 4) :=
    (relabelValue compress gs x q).trans (port (x ∘ compress) zero)
  have qValid : q₇ < 7 + gs₇.length := by
    by_contra! beyond
    have lit := port₇ (mask7 4) (by decide +kernel)
    rw [vl_beyond gs₇ _ q₇ beyond] at lit
    exact Bool.noConfusion lit
  have monotone₇ := noNotOfPort least₇ size₇ qValid port₇
  have monotone (r : ℕ) (g : Gate) (hg : gs[r]? = some g) : g.op ≠ .not :=
    monotone₇ r (relGate 9 7 compress g) (by simp [gs₇, List.getElem?_map, hg])
  have least : Least 9 (graph J []) gs o := ⟨clean, computes, fun hs ho hc fit =>
    size.trans (Theta9433J.JBound hs.length (funext fit ▸ has_of_clean 9 hs ho hc))⟩
  exact noLeafOrPortMonotone least size monotone port

end Theta9433JPort

end

-- From .pnp-tools/Theta9433Main.lean
section

namespace Theta9433Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitHelpers CircuitHelpers.Readers

open BranchProof2752 (notGateCount)

open BranchProof2752.PetersenCutTrace

open Cactus10440Floor Theta9433LeafSplice Theta9433Original

open Theta9433Control (target)

open Theta9433Arity

open Relation

private abbrev remainder8 := cofactor main8 7 false

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
private theorem main8Split : main8 = fun x => x 7 || remainder8 x := by
  funext x
  exact (show ∀ y, main8 y = (y 7 || remainder8 y) from by decide +kernel) x

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
private theorem remainder8Ignores : ∀ (x : Fin 8 → Bool) b,
    remainder8 (Function.update x 7 b) = remainder8 x := by
  decide +kernel

theorem pureAfterLeaf {gs : List Gate} {o : ℕ}
    (L9 : Least 9 Theta9433Host.main gs o) (size : gs.length ≤ 11)
    (unused : ∀ g ∈ gs, 3 ∉ g.inputs) (away : o ≠ 3)
    (budget : notGateCount gs ≤ 1) :
    ∀ r g, (atGate : gs[r]? = some g) →
      ReflTransGen (readEdge gs) (inputWire gs (8 : Fin 9))
        (⟨9 + r, by have := (List.getElem?_eq_some_iff.1 atGate).1; omega⟩ :
          Fin (9 + gs.length)) → g.op = .or := by
  let D := dropPrimary 3 gs
  let L8 := main8Least L9.hcl L9.hev size unused away
  have valid := main8OutputValid L8
  let out : Fin (8 + D.length) := ⟨dropWire 3 o, valid⟩
  let live := main8Live L8 valid
  have L : Least 8 (fun x => x 7 || remainder8 x) D out.val := by
    rw [← main8Split]
    exact L8
  have neg : ∃ x : Fin 8 → Bool, remainder8 x = false :=
    ⟨fun _ => false, by decide +kernel⟩
  have pos : ∃ x : Fin 8 → Bool, remainder8 x = true :=
    ⟨fun _ => true, by decide +kernel⟩
  have lower (s : ℕ) (h : HasCircuitSize 8 remainder8 s) : D.length ≤ s + 1 := by
    have lb := main8RemainderFloor s h
    change (dropPrimary 3 gs).length ≤ _
    rw [dropPrimary_length]
    omega
  have notCount : notGateCount D ≤ 1 := by
    simpa only [D, dropPrimary_notGateCount] using budget
  obtain ⟨p, first, atFirst, reader, unique, isOr⟩ := main8HostOnlyOr L9 size unused
  have one := Theta9433NoFork.first_eq_out_of_unique_or out L live notCount
    (fun x => remainder8Ignores x false) neg pos lower atFirst isOr reader unique
  have signs := Theta9433OrPath.polarity_of_or out L live one notCount remainder8Ignores
  have pure := Theta9433OrPath.onlyOr out L live one signs neg
  intro r g atGate reaches
  let a := inputWire gs (8 : Fin 9)
  let b : Fin (9 + gs.length) := ⟨9 + r, by
    have := (List.getElem?_eq_some_iff.1 atGate).1
    omega⟩
  have ha : a.val ≠ 3 := by change (8 : ℕ) ≠ 3; decide
  have hb : b.val ≠ 3 := by change 9 + r ≠ 3; omega
  have down := (readPath_drop_iff (3 : Fin 9) unused a b ha hb).2 reaches
  have raw : dropVertex (3 : Fin 9) a ha = inputWire D (7 : Fin 8) :=
    Fin.ext (by change dropWire 3 8 = 7; decide)
  have gAt : D[r]? = some (dropGate 3 g) := gate_at atGate
  have dst : dropVertex (3 : Fin 9) b hb = (⟨8 + r, by
      have := (List.getElem?_eq_some_iff.1 gAt).1
      omega⟩ : Fin (8 + D.length)) := Fin.ext (dropWire_gate (3 : Fin 9) r)
  rw [raw, dst] at down
  exact pure r (dropGate 3 g) gAt down

open Theta9433SplicePath

private abbrev leafGates {gs : List Gate} {o : ℕ} (S : Splice gs o) :=
  spliceGates gs S.p S.q S.u

private def PureHost (gs : List Gate) : Prop :=
  ∀ r g, (atGate : gs[r]? = some g) →
    ReflTransGen (readEdge gs) (inputWire gs (8 : Fin 9))
      (⟨9 + r, by have := (List.getElem?_eq_some_iff.1 atGate).1; omega⟩ :
        Fin (9 + gs.length)) → g.op = .or

private theorem retained_of_avoid {gs : List Gate} {o : ℕ} (S : Splice gs o)
    {a b : Fin (9 + gs.length)} (notFirst : b.val ≠ 9 + S.p)
    (path : ReflTransGen (avoid (readEdge gs) (secondIndex S)) a b) :
    ReflTransGen (RetainedRead S) a b := by
  revert notFirst
  induction path with
  | refl => exact fun _ => .refl
  | @tail m z prior edge ih =>
    intro zAway
    have hq : z.val ≠ 9 + S.q := fun eq => edge.2.2 (Fin.ext eq)
    have mp : m.val ≠ 9 + S.p := by
      intro atFirst
      obtain ⟨r, g, atGate, dst, reads⟩ := edge.1
      rw [atFirst] at reads
      have eq := S.onlyFirstReader r ⟨g, atGate, reads⟩
      exact hq (dst.trans (congrArg (9 + ·) eq))
    exact (ih mp).tail ⟨edge.1, zAway, hq⟩

private theorem retained_or_path {gs : List Gate} {o : ℕ} (S : Splice gs o)
    (L : Least 9 target gs o) (pure : PureHost (leafGates S))
    {b : Fin (9 + gs.length)}
    (path : ReflTransGen (RetainedRead S) (inputWire gs (8 : Fin 9)) b) :
    ReflTransGen (Theta9433Host.OrEdge 9 gs) 8 b.val := by
  induction path with
  | refl => exact .refl
  | @tail a z prior edge ih =>
    rcases edge with ⟨⟨r, g, atGate, dst, reads⟩, notFirst, notSecond⟩
    have rp : r ≠ S.p := fun eq => notFirst (dst.trans (congrArg (9 + ·) eq))
    have rq : r ≠ S.q := fun eq => notSecond (dst.trans (congrArg (9 + ·) eq))
    obtain ⟨mappedGate, mappedDst, _, sameOp⟩ :=
      map_gate_at S L.hcl atGate dst reads rp rq
    have moved := map_path S L.hcl (prior.tail ⟨⟨r, g, atGate, dst, reads⟩, notFirst, notSecond⟩)
    have eq : mapWire S L.hcl z = (⟨9 + spliceSlot S.p S.q r, by
        have bound := (List.getElem?_eq_some_iff.1 mappedGate).1
        change spliceSlot S.p S.q r < (leafGates S).length at bound
        omega⟩ : Fin (9 + (leafGates S).length)) := Fin.ext mappedDst
    rw [map_input, eq] at moved
    exact ih.tail ⟨r, g, dst, atGate, reads, sameOp ▸ pure _ _ mappedGate moved⟩

private theorem cut_host {gs : List Gate} {o : Fin (9 + gs.length)}
    (S : Splice gs o.val) (L : Least 9 target gs o.val) (pure : PureHost (leafGates S))
    (notFirst : o.val ≠ 9 + S.p) :
    ¬ ReflTransGen (avoid (readEdge gs) (secondIndex S)) (inputWire gs (8 : Fin 9)) o := by
  intro route
  let x := pair (fun _ => false) false true
  have raw : vl gs x 8 = true := by
    rw [vl_input gs x 8 (by decide)]
    decide +kernel
  have f := Theta9433Host.orPathPreservesTrue L.hcl x
    (retained_or_path S L pure (retained_of_avoid S notFirst route)) raw
  rw [L.hev] at f
  exact (by decide +kernel : target x ≠ true) f

private theorem host_does_not_reach_w {gs : List Gate} {o : Fin (9 + gs.length)}
    (S : Splice gs o.val) (L : Least 9 target gs o.val) (pure : PureHost (leafGates S))
    (outNotLeaf : o.val ≠ 3) :
    ¬ ReflTransGen (readEdge gs) (inputWire gs (8 : Fin 9)) (wIndex S L) := by
  intro route
  have mapped := map_path_before_first S L.hcl route (wEarlier S L)
  rw [map_input] at mapped
  let x := pair (fun _ => false) true true
  have raw : x 8 = true := by decide +kernel
  have up := Theta9433OrPath.valueAlongOr S.residualLeast.hcl pure x raw mapped
  change vl (leafGates S) x (spliceWire S.p S.q S.u S.w) = true at up
  rw [S.agrees x (by decide +kernel) S.w (wIndex S L).isLt] at up
  rw [wGateFalseAtProbe S L outNotLeaf] at up
  contradiction

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
private theorem main9Split : Theta9433Host.main = fun x => x 8 || remainder x := by
  funext x
  exact (show ∀ y, Theta9433Host.main y = (y 8 || remainder y) from by decide +kernel) x

set_option maxRecDepth 30000 in
set_option maxHeartbeats 7000000 in
private theorem remainderIgnores : ∀ x : Fin 9 → Bool,
    remainder (Function.update x (8 : Fin 9) false) = remainder x := by
  decide +kernel

private theorem ignoreInput {gs : List Gate} {i : Fin 9}
    (unused : ∀ g ∈ gs, i.val ∉ g.inputs) (x y : Fin 9 → Bool)
    (same : ∀ j, j ≠ i → x j = y j) (w : ℕ) (notRaw : w ≠ i.val) :
    vl gs x w = vl gs y w := by
  refine agree_except i.val gs _ _ unused (by simp) ?_ w notRaw
  intro j different
  by_cases raw : j < 9
  · let v : Fin 9 := ⟨j, raw⟩
    rw [getD_ofFn 9 x false v, getD_ofFn 9 y false v]
    exact same v (fun eq => different (congrArg Fin.val eq))
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private theorem no_port {gs : List Gate} {o : Fin (9 + gs.length)}
    (S : Splice gs o.val) (L : Least 9 target gs o.val)
    (noHost : ¬ ReflTransGen (readEdge gs) (inputWire gs (8 : Fin 9)) (wIndex S L))
    (port : ∀ x, remainder x = false → vl gs x S.w = (x 2 || x 5)) : False := by
  let out9 := mapWire S L.hcl o
  have split : Least 9 (fun x => x 8 || remainder x) (leafGates S) out9.val := by
    rw [← main9Split]
    exact S.residualLeast
  have cap : (leafGates S).length ≤ 11 := S.residualSize.le
  have neg : ∃ x : Fin 9 → Bool, remainder x = false := ⟨fun _ => false, by decide +kernel⟩
  have pos : ∃ x : Fin 9 → Bool, remainder x = true := ⟨fun _ => true, by decide +kernel⟩
  obtain ⟨p, g, atGate, reads, uniq, gOr⟩ := Theta9433Host.hostOnlyOr S.residualLeast cap
  obtain ⟨other, back, avoidHost, unused, disagrees, computes⟩ :=
    Theta9433NoFork.erase_unique_or out9 split remainderIgnores neg pos atGate gOr reads uniq
  let Jgates := Theta9433Bypass.remove 9 p other (leafGates S)
  let outJ := Theta9433Bypass.wire 9 p other out9.val
  let w9 := mapWire S L.hcl (wIndex S L)
  let wJ := Theta9433Bypass.wire 9 p other w9.val
  have wUnchanged : w9.val = S.w := map_before_first_val S L.hcl (wIndex S L) (wEarlier S L)
  have wNot8 : w9.val ≠ 8 := by
    intro eq
    have ends : wIndex S L = inputWire gs (8 : Fin 9) := Fin.ext (wUnchanged.symm.trans eq)
    exact noHost (ends.symm ▸ ReflTransGen.refl)
  have wNot3 : w9.val ≠ 3 := fun eq => S.wNotLeaf (wUnchanged.symm.trans eq)
  have wJNot8 : wJ ≠ 8 := by
    intro eq
    simp only [wJ, Theta9433Bypass.wire] at eq
    split_ifs at eq <;> omega
  have Jsmall : Jgates.length ≤ 10 := by
    have exactOne := Theta9433Bypass.size (n := 9) (substitute := other)
      (List.getElem?_eq_some_iff.1 atGate).1
    change Jgates.length + 1 = (leafGates S).length at exactOne
    omega
  have matchPort (x : Fin 9 → Bool) (hx : remainder x = false) :
      vl Jgates x wJ = (x 2 || x 5) := by
    let y := Function.update x (8 : Fin 9) false
    let z := pair x true false
    have hostFalse : y 8 = false := by simp [y]
    have leafTrue : z 3 = true := by simp [z, pair]
    have sameHost (i : Fin 9) (notHost : i ≠ 8) : x i = y i := by
      simp [y, Function.update_of_ne notHost]
    have sameLeaf (i : Fin 9) (notLeaf : i ≠ 3) : y i = z i := by
      simpa only [y, z, pair, Function.update_eq_self] using
        pairLeafUnchanged x (x 3) true false notLeaf
    calc
      vl Jgates x wJ = vl Jgates y wJ := ignoreInput (i := 8) unused x y sameHost wJ wJNot8
      _ = vl (leafGates S) y w9.val := disagrees y hostFalse _ w9.isLt
      _ = vl (leafGates S) z w9.val := ignoreInput (i := 3) S.residualNoLeafReader y z sameLeaf _ wNot3
      _ = vl gs z S.w := S.agrees z leafTrue S.w (wIndex S L).isLt
      _ = vl gs x S.w := wInvariant S L noHost x true false
      _ = (x 2 || x 5) := port x hx
  exact Theta9433JPort.noLeafOrPort (Theta9433Bypass.clean split.hcl back) computes Jsmall matchPort

theorem lower : ∀ t, HasCircuitSize 9 target t → 14 ≤ t := by
  intro t fit
  by_contra small
  have nonconst := dep_nc Theta9433Leaf.leafDepends
  obtain ⟨gs, o, L, size⟩ := exists_least 9 target t nonconst fit
  have cap : gs.length ≤ 13 := by omega
  have valid : o < 9 + gs.length := by
    by_contra! outside
    obtain ⟨x, y, different⟩ := L.ncv nonconst
    exact different ((vl_beyond gs x o outside).trans (vl_beyond gs y o outside).symm)
  let out : Fin (9 + gs.length) := ⟨o, valid⟩
  obtain ⟨S⟩ := least_splice L cap
  let sample := pair (fun _ => false) true false
  have leafOn : sample 3 = true := by decide +kernel
  have reject : vl gs sample o = false := (L.hev _).trans (by decide +kernel)
  have notLeaf : out.val ≠ 3 := by
    intro eq
    change o = 3 at eq
    rw [eq, vl_input gs sample 3 (by decide)] at reject
    change sample (3 : Fin 9) = false at reject
    rw [leafOn] at reject
    contradiction
  have notFirst : out.val ≠ 9 + S.p := by
    intro eq
    change o = 9 + S.p at eq
    rw [eq, firstEval S L sample, leafOn, Bool.true_or] at reject
    contradiction
  have budget := Theta9433PinOps.least_notGateCount_le_one CoreTable7402 L cap
  have pure : PureHost (leafGates S) :=
    pureAfterLeaf S.residualLeast S.residualSize.le S.residualNoLeafReader S.residualOutNotLeaf
      (S.notGateCount_eq.trans_le budget)
  have noHost := host_does_not_reach_w (o := out) S L pure notLeaf
  have through := cut_host (o := out) S L pure notFirst
  exact no_port (o := out) S L noHost (portBoundary (out := out) S L notLeaf notFirst noHost through)

end Theta9433Main

end

end PEqualNP.Outside.L_meta_9433_aux

open PEqualNP.Outside.L_meta_9433_aux

theorem PEqualNP.Outside.L_meta_9433 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → 14 ≤ t :=
  Theta9433Main.lower
