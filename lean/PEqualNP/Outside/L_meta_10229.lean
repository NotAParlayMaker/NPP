import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs
import PEqualNP.Defs.Represents

-- Fix two left and two right inputs to obtain the six-cycle.
-- The finite catalogue checks enumerate tables for the remaining normal forms.

namespace PEqualNP.Outside.L_meta_10229_aux

namespace Helpers

open PEqualNP.CircuitLowerBounds

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

end Helpers

namespace Helpers

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

end Helpers

namespace Helpers

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

end Helpers

namespace Helpers.PermInputs

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

end Helpers.PermInputs

namespace Link

structure Model where
  op : ℕ → ℕ
  s1 : ℕ → ℕ
  s2 : ℕ → ℕ
  so : ℕ
  w : ℕ → ℕ → Bool

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

structure Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop where
  op_lt : ∀ j < s, M.op j < 3
  s1_le : ∀ j < s, M.s1 j ≤ n + j
  s2_le : ∀ j < s, M.s2 j ≤ n + j
  so_le : M.so ≤ n + s
  w_eq : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)
  out_eq : ∀ r, R r → M.sv n s M.so r = g r

def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

def padDecidable (n : ℕ) (M : Model) (j : ℕ) : Decidable (M.pad n j) := by
  unfold Model.pad; infer_instance

local instance (n : Nat) (M : Model) (j : Nat) : Decidable (M.pad n j) := padDecidable n M j

structure NF (n s : ℕ) (M : Model) : Prop where
  pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j
  padOp : ∀ j < s, M.op j = 2 → M.pad n j
  noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j
  noPadRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i
  ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j
  used : ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)
  out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1)

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Helpers

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model where
  op j := (code n (gateAt C j) j).1
  s1 j := (code n (gateAt C j) j).2.1
  s2 j := (code n (gateAt C j) j).2.2
  so := if C.output < n + C.gates.length then C.output else n + s
  w j r := if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) where
  op_lt j _ := (code_le n _ j).1
  s1_le j _ := (code_le n _ j).2.1
  s2_le j _ := (code_le n _ j).2.2
  so_le := by simp only [ofCirc]; split_ifs <;> omega
  w_eq j hj r _ := by
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, hjl, hga, code, gfun]
  out_eq r hr := by
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model where
  op j := if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j
  s1 j := if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j)
  s2 j := if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j)
  so := rd n d t s M.so
  w j r := if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) where
  op_lt j hj := by
    simp only [mv]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  s1_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  s2_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  so_le := by
    have := hv.so_le
    simp only [mv]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  w_eq j hj r hr := by
    by_cases h0 : j = 0
    · subst h0; simp [mv, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, if_neg h0, if_pos h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  out_eq r hr := by
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, M.s1 j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

theorem ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.s1_le j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  { M with s1 := fun i => if i = j then M.s2 j else M.s1 i,
           s2 := fun i => if i = j then M.s1 j else M.s2 i }

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) where
  op_lt := hv.op_lt
  s1_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  so_le := hv.so_le
  w_eq i hi r hr := by
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  out_eq r hr := hv.out_eq r hr

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

theorem meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, hlt]⟩
  omega

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem same_src (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

end Link

local instance (n : Nat) (M : Link.Model) (j : Nat) : Decidable (M.pad n j) := Link.padDecidable n M j

namespace Promise

open PEqualNP.Represents

def repRow (n u v : ℕ) : ℕ := 2 ^ u + 2 ^ (n + v)

theorem repRow_testBit {n u : ℕ} (hu : u < n) (v i : ℕ) :
    (repRow n u v).testBit i = (decide (i = u) || decide (i = n + v)) := by
  have h : repRow n u v = 2 ^ (n + v) ||| 2 ^ u := by
    have := Nat.two_pow_add_eq_or_of_lt (i := n + v) (b := 2 ^ u)
      (Nat.pow_lt_pow_right (by norm_num) (by omega)) 1
    rw [mul_one] at this
    rw [← this, repRow, add_comm]
  rw [h, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow, Bool.or_comm]
  congr 1 <;> exact decide_eq_decide.mpr eq_comm

theorem repRow_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    (List.ofFn fun i : Fin (n + m) => (repRow n u v).testBit i) = oneEach u v := by
  have hu := u.2
  apply List.ext_getElem
  · simp [oneEach]
  · intro i h1 h2
    rw [List.getElem_ofFn, repRow_testBit hu]
    simp only [oneEach, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
    split_ifs with h
    · have hne : ¬ i = n + (v : ℕ) := by omega
      simp [Fin.ext_iff, hne]
    · have hne : ¬ i = (u : ℕ) := by omega
      have hiff : i = n + (v : ℕ) ↔ i - n = (v : ℕ) := by omega
      simp [Fin.ext_iff, hne, hiff]

def repRows (n m : ℕ) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange m).map fun v => repRow n u v

def gMask (n m M r : ℕ) : Bool := M.testBit (m * Nat.log2 (r % 2 ^ n) + Nat.log2 (r / 2 ^ n))

theorem gMask_row {n m : ℕ} (M : ℕ) (u : Fin n) (v : Fin m) :
    gMask n m M (repRow n u v) = M.testBit (m * u + v) := by
  have hlt : 2 ^ (u : ℕ) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) u.2
  have h1 : repRow n u v % 2 ^ n = 2 ^ (u : ℕ) := by
    rw [repRow, pow_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have h2 : repRow n u v / 2 ^ n = 2 ^ (v : ℕ) := by
    rw [repRow, pow_add, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  rw [gMask, h1, h2, Nat.log2_two_pow, Nat.log2_two_pow]

end Promise

namespace LastSource

open Link

theorem earlier_padding {n s : Nat} {M : Model} (hn : NF n s M) {i j : Nat}
    (hij : i ≤ j) (hjs : j < s) (hp : M.pad n j) : M.pad n i := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact hp
  | succ j ih =>
    by_cases eq : i = j + 1
    · rwa [eq]
    · exact ih (by omega) (by omega) (hn.pre j hjs hp)

end LastSource

namespace Elimination

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Helpers
open Helpers.PermInputs

def IsAO (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

theorem elim_preserves_ao (n : Nat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, IsAO g) → (∀ g ∈ acc.2, IsAO g) → ∀ g ∈ (elim n gs acc).2, IsAO g := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h1
    · exact h g' h1
    · have op := simplify_op _ _ _ g' (by simpa using h1)
      unfold IsAO at *
      rw [op]
      exact hgs g List.mem_cons_self

theorem mono_relabel {n m : Nat} (π : Fin n → Fin m) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (relabel n m π C) ∧ (relabel n m π C).size = C.size ∧
    ∀ x : Fin m → Bool, (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) := by
  refine ⟨?_, by simp [relabel, Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨g₀, h₀, rfl⟩ := List.mem_map.mp hg
    exact ⟨(h g₀ h₀).1, by simpa [relGate] using (h g₀ h₀).2⟩
  · intro x
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem reader_of_dependency (n : Nat) (C : Circuit)
    (hout : C.output ≠ n)
    (hdep : ∃ x : Fin (n + 1) → Bool,
      C.eval (List.ofFn (Function.update x (Fin.last n) (!x (Fin.last n)))) ≠
        C.eval (List.ofFn x)) : ∃ g ∈ C.gates, n ∈ g.inputs := by
  by_contra hNo
  push Not at hNo
  obtain ⟨x, hx⟩ := hdep
  apply hx
  have hns := supp_noread n C.gates (inputSupps (n + 1)) hNo (inputSupps_noread n) C.output hout
  exact (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
    intro k hk
    have hne : k ≠ Fin.last n := fun e => hns (e ▸ hk)
    simp [Function.update_of_ne hne])

theorem drop_last (n : Nat) (C : Circuit) (hC : Monotone2 C)
    (hRead : ∃ gate ∈ C.gates, n ∈ gate.inputs)
    (hNonconstant : ∃ x y : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc x false)) ≠ C.eval (List.ofFn (Fin.snoc y false))) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Fin.snoc x false)) := by
  have hnok : ∀ g ∈ C.gates, NOk g := by
    intro g hg
    have hv := hC g hg
    have hao : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hv.1
    rcases hao with ha | ho
    · exact ⟨⟨Or.inl ha, hv.2⟩, by simp [ha]⟩
    · exact ⟨⟨Or.inr (Or.inl ho), hv.2⟩, by simp [ho]⟩
  let acc := elim n C.gates (initStats n false, [])
  have hinv (x : Fin n → Bool) :
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn (Fin.snoc x false))) acc := by
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) C.gates _ _ (fun g hg => (hnok g hg).1) (inv_init n false x)
  have heval (x : Fin n → Bool) :
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn x)) =
        C.eval (List.ofFn (Fin.snoc x false)) :=
    ((hinv x).2 C.output).2
  cases hs : acc.1.getD C.output (Stat.const false) with
  | const c =>
    obtain ⟨x, y, hxy⟩ := hNonconstant
    exfalso
    apply hxy
    rw [← heval x, ← heval y, hs]
    rfl
  | wire j =>
    refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
    · intro gate hg
      have hOp := elim_preserves_ao n C.gates (initStats n false, [])
        (fun g hh => by simpa [IsAO] using (hC g hh).1) (by simp) gate hg
      have hOk := elim_ok n C.gates (initStats n false, []) (by simp) gate hg
      exact ⟨by simpa [IsAO] using hOp, hOk.2⟩
    · have hlen := elim_len_lt n n C.gates (initStats n false, []) hnok (by simp [initStats])
          ⟨false, getD_snoc_len _ _ _ _ (by simp)⟩ hRead
      simpa [acc, Circuit.size] using hlen
    · intro x
      have e := heval x
      rw [hs] at e
      exact e

end Elimination

namespace Restriction
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem fold_mono (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or)) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := hleg g (by simp)
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

open PEqualNP.MetaComplexity PEqualNP.Represents Elimination
open Helpers.PermInputs

theorem circuit_mono {n : Nat} (C : Circuit) (hC : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have hGate : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g h => by simpa using (hC g h).1
  have hlist : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i
    by_cases hi : i < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]
      exact hxy ⟨i, hi⟩
    · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]
  exact fold_mono C.gates hGate (List.ofFn x) (List.ofFn y) (by simp) hlist C.output

theorem drop_essential (n : Nat) (C : Circuit) (hC : Monotone2 C)
    (x y : Fin (n + 1) → Bool) (hx : x (Fin.last n) = true)
    (hPos : C.eval (List.ofFn x) = true) (hNeg : C.eval (List.ofFn y) = false)
    (inc : ∀ i, i ≠ Fin.last n → x i = true → y i = true)
    (p q : Fin n → Bool)
    (hp : C.eval (List.ofFn (Fin.snoc p false)) = true)
    (hq : C.eval (List.ofFn (Fin.snoc q false)) = false) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧
      ∀ z : Fin n → Bool, D.eval (List.ofFn z) = C.eval (List.ofFn (Fin.snoc z false)) := by
  have dep : ∃ z : Fin (n + 1) → Bool,
      C.eval (List.ofFn (Function.update z (Fin.last n) (!z (Fin.last n)))) ≠
        C.eval (List.ofFn z) := by
    refine ⟨x, ?_⟩
    intro he
    rw [hx] at he
    have hxy : ∀ i, Function.update x (Fin.last n) false i = true → y i = true := by
      intro i hi
      by_cases eq : i = Fin.last n
      · subst i; simp at hi
      · rw [Function.update_of_ne eq] at hi
        exact inc i eq hi
    have impossible := circuit_mono C hC (Function.update x (Fin.last n) false) y hxy
      (he.trans hPos)
    rw [hNeg] at impossible
    contradiction
  have hout : C.output ≠ n := by
    intro ho
    have hRead : (wf C.gates (List.ofFn (Fin.snoc p false))).getD n false =
        (List.ofFn (Fin.snoc p false)).getD n false := wf_keep _ _ _ (by simp)
    change (wf C.gates (List.ofFn (Fin.snoc p false))).getD C.output false = true at hp
    rw [ho, hRead] at hp
    rw [Helpers.ofFn_snoc,
      Helpers.getD_snoc_len _ _ _ _ (by simp)] at hp
    contradiction
  exact drop_last n C hC (reader_of_dependency n C hout dep) ⟨p, q, by rw [hp, hq]; decide⟩

def pair (n a b : Nat) : Fin n → Bool := fun i => decide (i.val = a ∨ i.val = b)

end Restriction

namespace Transfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Helpers.PermInputs
open Elimination (mono_relabel)
open Restriction (drop_essential pair)

def graph (u v : Fin 5) : Bool := (12075574 : Nat).testBit (5 * u.val + v.val)
def compressed (u v : Fin 4) : Bool := (30874 : Nat).testBit (4 * u.val + v.val)
def permute : Fin 10 → Fin 10 := ![0, 1, 2, 9, 3, 4, 5, 8, 6, 7]
def lWire : Fin 5 → Nat := ![0, 1, 2, 9, 3]
def rWire : Fin 5 → Nat := ![4, 5, 8, 6, 7]
def lKeep : Fin 4 → Fin 5 := ![0, 1, 2, 4]
def rKeep : Fin 4 → Fin 5 := ![0, 1, 3, 4]

private theorem pullback : ∀ u v : Fin 5,
    List.ofFn (pair 10 (lWire u) (rWire v) ∘ permute) = oneEach u v := by decide +kernel

theorem compress_circuit (h : RepSizeAtMost graph 10) : RepSizeAtMost compressed 8 := by
  obtain ⟨C, hC, hSize, hRep⟩ := h
  let C1 := relabel 10 10 permute C
  obtain ⟨hC1, hSz1, hEval1⟩ := mono_relabel permute C hC
  have ev (u v : Fin 5) : C1.eval (List.ofFn (pair 10 (lWire u) (rWire v))) = graph u v := by
    rw [hEval1, pullback, hRep]
  have e1 : C1.eval (List.ofFn (pair 10 9 7)) = true := ev 3 4
  have e2 : C1.eval (List.ofFn (pair 10 3 7)) = false := ev 4 4
  have e3 : C1.eval (List.ofFn (Fin.snoc (pair 9 2 7) false)) = true := by
    have same : List.ofFn (Fin.snoc (pair 9 2 7) false) = List.ofFn (pair 10 2 7) := by decide
    rw [same]; exact ev 2 4
  have e4 : C1.eval (List.ofFn (Fin.snoc (pair 9 3 7) false)) = false := by
    have same : List.ofFn (Fin.snoc (pair 9 3 7) false) = List.ofFn (pair 10 3 7) := by decide
    rwa [same]
  obtain ⟨C2, hC2, hSz2, hEval2⟩ := drop_essential 9 C1 hC1 (pair 10 9 7) (pair 10 3 7)
    rfl e1 e2 (by decide) (pair 9 2 7) (pair 9 3 7) e3 e4
  have ev2hi : C2.eval (List.ofFn (pair 9 0 8)) = true := by
    rw [hEval2]
    have same : List.ofFn (Fin.snoc (pair 9 0 8) false) = List.ofFn (pair 10 0 8) := by decide
    rw [same]; exact ev 0 2
  have ev2lo : C2.eval (List.ofFn (pair 9 0 4)) = false := by
    rw [hEval2]
    have same : List.ofFn (Fin.snoc (pair 9 0 4) false) = List.ofFn (pair 10 0 4) := by decide
    rw [same]; exact ev 0 0
  have ev2p : C2.eval (List.ofFn (Fin.snoc (pair 8 0 5) false)) = true := by
    rw [hEval2]
    have same : List.ofFn (Fin.snoc (Fin.snoc (pair 8 0 5) false) false) =
      List.ofFn (pair 10 0 5) := by decide
    rw [same]; exact ev 0 1
  have ev2q : C2.eval (List.ofFn (Fin.snoc (pair 8 0 4) false)) = false := by
    have same : List.ofFn (Fin.snoc (pair 8 0 4) false) = List.ofFn (pair 9 0 4) := by decide
    rwa [same]
  obtain ⟨D, hD, hSzD, hEvalD⟩ := drop_essential 8 C2 hC2 (pair 9 0 8) (pair 9 0 4)
    rfl ev2hi ev2lo (by decide) (pair 8 0 5) (pair 8 0 4) ev2p ev2q
  change C1.size = C.size at hSz1
  refine ⟨D, hD, by omega, ?_⟩
  intro u v
  have same : ∀ u v : Fin 4, List.ofFn (pair 8 u.val (4 + v.val)) = oneEach u v := by decide +kernel
  have lift : ∀ u v : Fin 4,
      List.ofFn (Fin.snoc (Fin.snoc (pair 8 u.val (4 + v.val)) false) false) =
      List.ofFn (pair 10 (lWire (lKeep u)) (rWire (rKeep v))) := by decide +kernel
  have reduced : ∀ u v : Fin 4, graph (lKeep u) (rKeep v) = compressed u v := by decide +kernel
  rw [← same u v, hEvalD, hEval2, lift]
  exact (ev (lKeep u) (rKeep v)).trans (reduced u v)

end Transfer

namespace CycleTransfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Helpers.PermInputs
open Elimination (mono_relabel)
open Restriction (drop_essential pair)

def graph (u v : Fin 4) : Bool := (30874 : Nat).testBit (4 * u.val + v.val)
def compressed (u v : Fin 3) : Bool := (238 : Nat).testBit (3 * u.val + v.val)
def permute : Fin 8 → Fin 8 := ![0, 1, 7, 2, 3, 4, 6, 5]
def lWire : Fin 4 → Nat := ![0, 1, 7, 2]
def rWire : Fin 4 → Nat := ![3, 4, 6, 5]
def lKeep : Fin 3 → Fin 4 := ![0, 1, 3]
def rKeep : Fin 3 → Fin 4 := ![0, 1, 3]

private theorem pullback : ∀ u v : Fin 4,
    List.ofFn (pair 8 (lWire u) (rWire v) ∘ permute) = oneEach u v := by decide +kernel

theorem compress_circuit (h : RepSizeAtMost graph 8) : RepSizeAtMost compressed 6 := by
  obtain ⟨C, hC, hSize, hRep⟩ := h
  let C1 := relabel 8 8 permute C
  obtain ⟨hC1, hSz1, hEval1⟩ := mono_relabel permute C hC
  have ev (u v : Fin 4) : C1.eval (List.ofFn (pair 8 (lWire u) (rWire v))) = graph u v := by
    rw [hEval1, pullback, hRep]
  have e1 : C1.eval (List.ofFn (pair 8 7 5)) = true := ev 2 3
  have e2 : C1.eval (List.ofFn (pair 8 2 5)) = false := ev 3 3
  have e3 : C1.eval (List.ofFn (Fin.snoc (pair 7 0 4) false)) = true := by
    have same : List.ofFn (Fin.snoc (pair 7 0 4) false) = List.ofFn (pair 8 0 4) := by decide
    rw [same]; exact ev 0 1
  have e4 : C1.eval (List.ofFn (Fin.snoc (pair 7 0 3) false)) = false := by
    have same : List.ofFn (Fin.snoc (pair 7 0 3) false) = List.ofFn (pair 8 0 3) := by decide
    rw [same]; exact ev 0 0
  obtain ⟨C2, hC2, hSz2, hEval2⟩ := drop_essential 7 C1 hC1 (pair 8 7 5) (pair 8 2 5)
    rfl e1 e2 (by decide) (pair 7 0 4) (pair 7 0 3) e3 e4
  have ev2hi : C2.eval (List.ofFn (pair 7 2 6)) = true := by
    rw [hEval2]
    have same : List.ofFn (Fin.snoc (pair 7 2 6) false) = List.ofFn (pair 8 2 6) := by decide
    rw [same]; exact ev 3 2
  have ev2lo : C2.eval (List.ofFn (pair 7 2 5)) = false := by
    rw [hEval2]
    have same : List.ofFn (Fin.snoc (pair 7 2 5) false) = List.ofFn (pair 8 2 5) := by decide
    rw [same]; exact ev 3 3
  have ev2p : C2.eval (List.ofFn (Fin.snoc (pair 6 0 4) false)) = true := by
    rw [hEval2]
    have same : List.ofFn (Fin.snoc (Fin.snoc (pair 6 0 4) false) false) =
      List.ofFn (pair 8 0 4) := by decide
    rw [same]; exact ev 0 1
  have ev2q : C2.eval (List.ofFn (Fin.snoc (pair 6 0 3) false)) = false := by
    have same : List.ofFn (Fin.snoc (pair 6 0 3) false) = List.ofFn (pair 7 0 3) := by decide
    rw [same, hEval2]
    exact e4
  obtain ⟨D, hD, hSzD, hEvalD⟩ := drop_essential 6 C2 hC2 (pair 7 2 6) (pair 7 2 5)
    rfl ev2hi ev2lo (by decide) (pair 6 0 4) (pair 6 0 3) ev2p ev2q
  change C1.size = C.size at hSz1
  refine ⟨D, hD, by omega, ?_⟩
  intro u v
  have same : ∀ u v : Fin 3, List.ofFn (pair 6 u.val (3 + v.val)) = oneEach u v := by decide +kernel
  have lift : ∀ u v : Fin 3,
      List.ofFn (Fin.snoc (Fin.snoc (pair 6 u.val (3 + v.val)) false) false) =
      List.ofFn (pair 8 (lWire (lKeep u)) (rWire (rKeep v))) := by decide +kernel
  have reduced : ∀ u v : Fin 3, graph (lKeep u) (rKeep v) = compressed u v := by decide +kernel
  rw [← same u v, hEvalD, hEval2, lift]
  exact (ev (lKeep u) (rKeep v)).trans (reduced u v)

end CycleTransfer

namespace Reduction

open PEqualNP.Represents

theorem to_cycle (h : RepSizeAtMost Transfer.graph 10) :
    RepSizeAtMost CycleTransfer.compressed 6 :=
  CycleTransfer.compress_circuit (Transfer.compress_circuit h)

end Reduction

namespace Normalized

open Link
open Promise (gMask repRow repRows repRow_eq gMask_row)
open LastSource

abbrev table := gMask 3 3 238
abbrev rows := repRows 3 3
abbrev Graph : Fin 3 → Fin 3 → Bool := fun u v => (238 : Nat).testBit (3 * u.val + v.val)

private theorem row_mem_normalized (u v : Fin 3) : repRow 3 u v ∈ rows := by
  exact List.mem_flatMap.mpr ⟨u, by simp, List.mem_map.mpr ⟨v, by simp, rfl⟩⟩

private theorem noWire : ∀ i : Fin 6, ∃ u v : Fin 3,
    table (repRow 3 u v) ≠ (repRow 3 u v).testBit i := by
  decide +kernel

private theorem noGate : ∀ t : Fin 3, ∀ a b : Fin 6, ∃ u v : Fin 3,
    table (repRow 3 u v) ≠ gfun t ((repRow 3 u v).testBit a) ((repRow 3 u v).testBit b) := by
  decide +kernel

theorem penultimate_active {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) : ¬ M.pad 6 5 := by
  intro padPrev
  have padded (i : Nat) (hi : i ≤ 5) : M.pad 6 i :=
    earlier_padding hn hi (by decide) padPrev
  by_cases padLast : M.pad 6 6
  · have out := hv.so_le
    by_cases raw : M.so < 6
    · obtain ⟨u, v, disagree⟩ := noWire ⟨M.so, raw⟩
      apply disagree
      have eq := hv.out_eq (repRow 3 u v) (row_mem_normalized u v)
      simpa only [Model.sv, if_pos raw] using eq.symm
    · by_cases wire : M.so < 13
      · have pad : M.pad 6 (M.so - 6) :=
          earlier_padding hn (by omega) (by decide) padLast
        have value := pad_w hv (show M.so - 6 < 7 by omega) pad (r := 9) (by decide)
        have eq := hv.out_eq 9 (by decide)
        rw [Model.sv, if_neg raw, if_pos wire, value] at eq
        exact (show table 9 ≠ true by decide) eq.symm
      · have eq := hv.out_eq 17 (by decide)
        rw [Model.sv, if_neg raw, if_neg wire] at eq
        exact (show table 17 ≠ false by decide) eq.symm
  · have hout : M.so = 12 := (hn.out (by decide)).resolve_right padLast
    have hnf := hn.noF 6 (by decide) padLast
    have first : M.s1 6 < 6 := by
      by_contra h
      have le := hv.s1_le 6 (by decide)
      have idx : M.s1 6 - 6 < 6 := by omega
      have no := (hn.noPadRd 6 (by decide) (M.s1 6 - 6) idx (padded _ (by omega))).1
      exact no (by omega)
    have second : M.s2 6 < 6 := by
      by_contra h
      have le := hv.s2_le 6 (by decide)
      have idx : M.s2 6 - 6 < 6 := by omega
      have no := (hn.noPadRd 6 (by decide) (M.s2 6 - 6) idx (padded _ (by omega))).2
      exact no (by omega)
    obtain ⟨u, v, disagree⟩ := noGate ⟨M.op 6, hv.op_lt 6 (by decide)⟩
      ⟨M.s1 6, first⟩ ⟨M.s2 6, second⟩
    apply disagree
    have h := hv.out_eq (repRow 3 u v) (row_mem_normalized u v)
    have gate := hv.w_eq 6 (by decide) (repRow 3 u v) (row_mem_normalized u v)
    rw [hout] at h
    change M.w 6 (repRow 3 u v) = table (repRow 3 u v) at h
    rw [← h, gate, Model.sv, if_pos first, Model.sv, if_pos second]

end Normalized

namespace ThreeLive

open Link
open Promise (repRow repRows)
open Normalized
open LastSource

theorem row_mem (u v : Fin 3) : repRow 3 u v ∈ rows := by
  exact List.mem_flatMap.mpr ⟨u, by simp, List.mem_map.mpr ⟨v, by simp, rfl⟩⟩

theorem distinguish : ∀ i : Fin 6, ∃ u v u' v' : Fin 3,
    table (repRow 3 u v) = true ∧ table (repRow 3 u' v') = false ∧
    ∀ j : Fin 6, j ≠ i → (repRow 3 u v).testBit j = true →
      (repRow 3 u' v').testBit j = true := by
  decide +kernel

theorem gate_mono {t : Nat} {a b a' b' : Bool}
    (ha : a = true → a' = true) (hb : b = true → b' = true) :
    gfun t a b = true → gfun t a' b' = true := by
  by_cases h0 : t = 0 <;> by_cases h1 : t = 1 <;>
    cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all [gfun]

end ThreeLive

namespace ThreeLive

open Link
open Promise (repRow repRows)
open Normalized
open LastSource

open scoped BigOperators

theorem reads_each_input {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) (i : Fin 6) :
    ∃ j < 7, ¬ M.pad 6 j ∧ (M.s1 j = i.val ∨ M.s2 j = i.val) := by
  by_contra absent
  have notRead (j : Nat) (hj : j < 7) : M.s1 j ≠ i.val ∧ M.s2 j ≠ i.val := by
    by_cases pad : M.pad 6 j
    · have first := pad.2.1
      have second := pad.2.2
      have hi := i.isLt
      exact ⟨by omega, by omega⟩
    · exact ⟨fun eq => absent ⟨j, hj, pad, Or.inl eq⟩,
        fun eq => absent ⟨j, hj, pad, Or.inr eq⟩⟩
  obtain ⟨u, v, u', v', positive, negative, compare⟩ := distinguish i
  let r := repRow 3 u v
  let q := repRow 3 u' v'
  have hr : r ∈ rows := row_mem u v
  have hq : q ∈ rows := row_mem u' v'
  have monotone : ∀ j < 7, M.w j r = true → M.w j q = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j prev =>
      intro hj
      have source (w : Nat) (hw : w ≠ i.val) :
          M.sv 6 j w r = true → M.sv 6 j w q = true := by
        unfold Model.sv
        split
        next raw =>
          exact compare ⟨w, raw⟩ (fun eq => hw (congrArg Fin.val eq))
        next notraw =>
          split
          next within =>
            exact prev (w - 6) (by omega) (by omega)
          next outside =>
            exact id
      rw [hv.w_eq j hj r hr, hv.w_eq j hj q hq]
      exact gate_mono (source _ (notRead j hj).1) (source _ (notRead j hj).2)
  have hpPrev := penultimate_active hv hn
  have hpLast : ¬ M.pad 6 6 := fun pad => hpPrev (hn.pre 5 (by decide) pad)
  have hout : M.so = 12 := (hn.out (by decide)).resolve_right hpLast
  have eval (z : Nat) (hz : z ∈ rows) : M.w 6 z = table z := by
    have e := hv.out_eq z hz
    rw [hout] at e
    exact e
  have h := monotone 6 (by decide) ((eval r hr).trans positive)
  rw [eval q hq, negative] at h
  contradiction

def activeGates (M : Model) : Finset Nat := (Finset.range 7).filter fun j => ¬ M.pad 6 j

def sourceWires (M : Model) : Finset Nat :=
  (activeGates M).biUnion fun j => {M.s1 j, M.s2 j}

theorem wire_bounds {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) :
    5 ≤ (activeGates M).card ∧ 6 + (activeGates M).card ≤ (sourceWires M).card + 1 ∧
      2 * (activeGates M).card - (sourceWires M).card ≤ 2 := by
  let active := activeGates M
  let pair (j : Nat) : Finset Nat := {M.s1 j, M.s2 j}
  let sources := active.biUnion pair
  let internal := active.image fun j => 6 + j
  have hpPrev := penultimate_active hv hn
  have hpLast : ¬ M.pad 6 6 := fun pad => hpPrev (hn.pre 5 (by decide) pad)
  have out : M.so = 12 := (hn.out (by decide)).resolve_right hpLast
  have distinct : Disjoint (Finset.range 6) internal := by
    apply Finset.disjoint_left.mpr
    intro w hw hi
    have bound := Finset.mem_range.mp hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    omega
  have internalCard : internal.card = active.card :=
    Finset.card_image_of_injective active (fun a b e => by omega)
  have included : Finset.range 6 ∪ internal ⊆ insert M.so sources := by
    intro w hw
    rcases Finset.mem_union.mp hw with raw | gate
    · have wlt := Finset.mem_range.mp raw
      obtain ⟨j, hj, hp, found⟩ := reads_each_input hv hn ⟨w, wlt⟩
      apply Finset.mem_insert_of_mem
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hp⟩, ?_⟩
      simpa [pair, eq_comm] using found
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp gate
      obtain ⟨hjlt, hjlive⟩ := Finset.mem_filter.mp hj
      have jlt := Finset.mem_range.mp hjlt
      by_cases last : j = 6
      · simp [last, out]
      · obtain ⟨k, jltK, klt, found⟩ := hn.used j (by omega) hjlive
        have live : ¬ M.pad 6 k := by
          intro padded
          have max := padded.2
          rcases found with s1 | s2 <;> omega
        apply Finset.mem_insert_of_mem
        refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr klt, live⟩, ?_⟩
        simpa [pair, eq_comm] using found
  have slots : sources.card ≤ 2 * active.card := by
    calc
      sources.card ≤ ∑ j ∈ active, (pair j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ active, 2 := Finset.sum_le_sum (fun _ _ => Finset.card_le_two)
      _ = 2 * active.card := by simp [Nat.mul_comm]
  have lower := Finset.card_le_card included
  rw [Finset.card_union_of_disjoint distinct, Finset.card_range, internalCard] at lower
  have upper := Finset.card_insert_le M.so sources
  have activeBound : active.card ≤ 7 := by
    have h : active ⊆ Finset.range 7 := Finset.filter_subset _ _
    simpa only [Finset.card_range] using Finset.card_le_card h
  change 5 ≤ active.card ∧ 6 + active.card ≤ sources.card + 1 ∧
    2 * active.card - sources.card ≤ 2
  omega

theorem wire_budget {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) :
    5 ≤ (activeGates M).card ∧ 2 * (activeGates M).card - (sourceWires M).card ≤ 2 :=
  ⟨(wire_bounds hv hn).1, (wire_bounds hv hn).2.2⟩

theorem at_least_five {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) : 5 ≤ (activeGates M).card :=
  (wire_budget hv hn).1

theorem active_after_initial_two {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {j : Nat} (hj : 2 ≤ j) (hjlt : j < 7) : ¬ M.pad 6 j := by
  intro pad
  have subset : activeGates M ⊆ ({3, 4, 5, 6} : Finset Nat) := by
    intro i hi
    obtain ⟨bound, live⟩ := Finset.mem_filter.mp hi
    have ilt := Finset.mem_range.mp bound
    have lo : 3 ≤ i := by
      by_contra h
      exact live (earlier_padding hn (by omega) hjlt pad)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have upper := Finset.card_le_card subset
  have lower := at_least_five hv hn
  rw [show ({3, 4, 5, 6} : Finset Nat).card = 4 by decide] at upper
  omega

end ThreeLive

namespace SourceTree

open Link
open Normalized
open ThreeLive

def slots (M : Model) : Finset (Nat × Bool) :=
  (activeGates M).product Finset.univ

def source (M : Model) (slot : Nat × Bool) : Nat :=
  if slot.2 then M.s2 slot.1 else M.s1 slot.1

theorem source_image (M : Model) : (slots M).image (source M) = sourceWires M := by
  ext w
  simp only [slots, Finset.mem_image,
    Prod.exists, sourceWires, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨j, b, hj, eq⟩
    cases b
    · exact ⟨j, (Finset.mem_product.mp hj).1, Or.inl eq.symm⟩
    · exact ⟨j, (Finset.mem_product.mp hj).1, Or.inr eq.symm⟩
  · rintro ⟨j, hj, first | second⟩
    · exact ⟨j, false, Finset.mem_product.mpr ⟨hj, Finset.mem_univ _⟩, first.symm⟩
    · exact ⟨j, true, Finset.mem_product.mpr ⟨hj, Finset.mem_univ _⟩, second.symm⟩

theorem unique_source_slots {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) (seven : (activeGates M).card = 5) :
    Set.InjOn (source M) (slots M) := by
  apply Finset.card_image_iff.mp
  rw [source_image]
  have count : (slots M).card = 10 := by simp [slots, seven]
  rw [count]
  have lower := (wire_bounds hv hn).2.1
  have upper := Finset.card_image_le (s := slots M) (f := source M)
  rw [source_image, count] at upper
  omega

def Reads (M : Model) (w out : Nat) : Prop :=
  ∃ slot ∈ slots M, out = 6 + slot.1 ∧ source M slot = w

theorem reads_strict {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {w out : Nat} (edge : Reads M w out) : w < out := by
  obtain ⟨⟨j, b⟩, hm, rfl, rfl⟩ := edge
  have active : j ∈ activeGates M := (Finset.mem_product.mp hm).1
  obtain ⟨hi, hp⟩ := Finset.mem_filter.mp active
  have hj := Finset.mem_range.mp hi
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  rcases hn.noF j hj hp with ⟨h3, h4⟩
  cases b <;> simp only [source, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem reads_unique {M : Model} (single : Set.InjOn (source M) (slots M))
    {w a b : Nat} (left : Reads M w a) (right : Reads M w b) : a = b := by
  obtain ⟨l, hl, rfl, le⟩ := left
  obtain ⟨r, hr, rfl, re⟩ := right
  have eq := single hl hr (le.trans re.symm)
  rw [eq]

inductive Up (M : Model) : Nat → Nat → Prop
  | refl (w : Nat) : Up M w w
  | step {w next out : Nat} : Reads M w next → Up M next out → Up M w out

theorem up_append {M : Model} {a b c : Nat} (path : Up M a b) (edge : Reads M b c) :
    Up M a c := by
  induction path with
  | refl => exact Up.step edge (Up.refl _)
  | step first _ ih => exact Up.step first (ih edge)

theorem up_le {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {w out : Nat} (path : Up M w out) : w ≤ out := by
  induction path with
  | refl => exact Nat.le_refl _
  | step edge _ ih => exact Nat.le_trans (Nat.le_of_lt (reads_strict hv hn edge)) ih

theorem up_comparable {M : Model} (single : Set.InjOn (source M) (slots M))
    {w a b : Nat} (ha : Up M w a) (hb : Up M w b) : Up M a b ∨ Up M b a := by
  induction ha generalizing b with
  | refl => exact Or.inl hb
  | step e rest ih =>
    cases hb with
    | refl => exact Or.inr (Up.step e rest)
    | step f other =>
      have eq := reads_unique single e f
      exact ih (eq.symm ▸ other)

theorem sibling_has_no_common_ancestor {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) (single : Set.InjOn (source M) (slots M)) {a b parent w : Nat}
    (distinct : a ≠ b) (left : Reads M a parent) (right : Reads M b parent)
    (ha : Up M w a) (hb : Up M w b) : False := by
  rcases up_comparable single ha hb with ab | ba
  · cases ab with
    | refl => exact distinct rfl
    | step first rest =>
      have eq := reads_unique single first left
      have lo := up_le hv hn (eq ▸ rest)
      have hi := reads_strict hv hn right
      omega
  · cases ba with
    | refl => exact distinct rfl
    | step first rest =>
      have eq := reads_unique single first right
      have lo := up_le hv hn (eq ▸ rest)
      have hi := reads_strict hv hn left
      omega

end SourceTree

namespace SourceInventory

open Link
open Normalized
open ThreeLive
open SourceTree

theorem distinct_sources_card {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) :
    (sourceWires M).card = (activeGates M).card + 5 := by
  let earlier := (activeGates M).erase 6
  let allowed := Finset.range 6 ∪ earlier.image (fun i => 6 + i)
  have le : sourceWires M ⊆ allowed := by
    intro w mem
    rw [← source_image] at mem
    obtain ⟨⟨j, side⟩, slot, wire⟩ := Finset.mem_image.mp mem
    have edge : Reads M w (6+j) := ⟨(j, side), slot, rfl, wire⟩
    have before := reads_strict hv hn edge
    have active : j ∈ activeGates M := (Finset.mem_product.mp slot).1
    obtain ⟨hj, live⟩ := Finset.mem_filter.mp active
    have hj' := Finset.mem_range.mp hj
    apply Finset.mem_union.mpr
    by_cases raw : w < 6
    · exact Or.inl (Finset.mem_range.mpr raw)
    · right
      let i := w - 6
      have ilt : i < j := by dsimp [i]; omega
      have wi : w = 6 + i := by dsimp [i]; omega
      have hi : ¬ M.pad 6 i := by
        intro pad
        have no := hn.noPadRd j hj' i ilt pad
        rw [wi] at wire
        cases side
        · exact no.1 wire
        · exact no.2 wire
      refine Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨by omega, ?_⟩, wi.symm⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hi⟩
  have apart : Disjoint (Finset.range 6) (earlier.image fun i => 6+i) := by
    apply Finset.disjoint_left.mpr
    intro w raw other
    have bound := Finset.mem_range.mp raw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp other
    omega
  have last : 6 ∈ activeGates M :=
    Finset.mem_filter.mpr ⟨by decide, active_after_initial_two hv hn (by decide) (by decide)⟩
  have eraseCard : earlier.card + 1 = (activeGates M).card := Finset.card_erase_add_one last
  have cap := Finset.card_le_card le
  unfold allowed at cap
  rw [Finset.card_union_of_disjoint apart, Finset.card_range,
    Finset.card_image_of_injective _ (fun a b eq => by omega)] at cap
  have lower := (wire_bounds hv hn).2.1
  omega

end SourceInventory

namespace ReadOnce

open Link
open Promise (repRow gMask_row)
open Normalized
open ThreeLive
open SourceTree

def inputBits (i : Nat) : Nat := [7, 56, 448, 73, 146, 292][i]?.getD 0

def combine (andGate : Bool) (a b : Nat) : Nat :=
  if andGate then a &&& b else a ||| b

inductive ReadOnce : Nat → Nat → Prop
  | input (i : Fin 6) : ReadOnce (2 ^ i.val) (inputBits i.val)
  | gate {a b x y : Nat} (choice : Bool) (separate : a &&& b = 0) :
      ReadOnce a x → ReadOnce b y → ReadOnce (a ||| b) (combine choice x y)

theorem range_of_read_once {s t : Nat} (h : ReadOnce s t) :
    0 < s ∧ s < 64 ∧ t < 512 := by
  induction h with
  | input i =>
    exact (show ∀ i : Fin 6, 0 < 2 ^ i.val ∧ 2 ^ i.val < 64 ∧ inputBits i.val < 512 by
      decide +kernel) i
  | @gate a b x y choice _ _ _ ha hb =>
    have nz : a ||| b ≠ 0 := fun eq => (Nat.ne_of_gt ha.1) (Nat.or_eq_zero_iff.mp eq).1
    refine ⟨Nat.pos_of_ne_zero nz, Nat.or_lt_two_pow (n := 6) ha.2.1 hb.2.1, ?_⟩
    cases choice
    · exact Nat.or_lt_two_pow (n := 9) ha.2.2 hb.2.2
    · exact Nat.and_lt_two_pow (n := 9) _ hb.2.2

private theorem input_value : ∀ (i : Fin 6) (u v : Fin 3),
    (inputBits i.val).testBit (3 * u.val + v.val) = (repRow 3 u v).testBit i.val := by
  decide +kernel

private theorem src_uses {M : Model} {j : Nat} (hj : j < 7) (hp : ¬ M.pad 6 j) :
    Reads M (M.s1 j) (6+j) ∧ Reads M (M.s2 j) (6+j) := by
  have adm : j ∈ activeGates M := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hp⟩
  exact ⟨⟨(j, false), Finset.mem_product.mpr ⟨adm, Finset.mem_univ _⟩, rfl, rfl⟩,
    ⟨(j, true), Finset.mem_product.mpr ⟨adm, Finset.mem_univ _⟩, rfl, rfl⟩⟩

private theorem agree_sources {M : Model} {j w r : Nat} (hj : j < 7)
    (wlt : w < 6 + j) : M.sv 6 j w r = M.sv 6 7 w r := by
  by_cases raw : w < 6
  · simp [Model.sv, raw]
  · simp [Model.sv, raw, wlt, show w < 13 by omega]

theorem wire_repr {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) (single : Set.InjOn (source M) (slots M)) :
    ∀ w < 13, (6 ≤ w → ¬ M.pad 6 (w - 6)) →
      ∃ s t, ReadOnce s t ∧
        (∀ i, s.testBit i = true → Up M i w) ∧
        ∀ u v : Fin 3, t.testBit (3 * u.val + v.val) = M.sv 6 7 w (repRow 3 u v) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w prev =>
    intro wlt live
    by_cases raw : w < 6
    · refine ⟨2 ^ w, inputBits w, ReadOnce.input ⟨w, raw⟩, ?_, ?_⟩
      · intro i hi
        rw [Nat.testBit_two_pow] at hi
        obtain rfl := of_decide_eq_true hi
        exact Up.refl _
      · intro u v
        simpa only [Model.sv, ite_eq_left raw] using input_value ⟨w, raw⟩ u v
    · obtain ⟨j, rfl⟩ : ∃ j, w = 6 + j := ⟨w - 6, by omega⟩
      have hj : j < 7 := by omega
      have hp : ¬ M.pad 6 j := by simpa using live (by omega)
      obtain ⟨el, er⟩ := src_uses hj hp
      have ll := reads_strict hv hn el
      have rr := reads_strict hv hn er
      have child (w : Nat) (h : w = M.s1 j ∨ w = M.s2 j)
          (bound : w < 6 + j) (above : 6 ≤ w) : ¬ M.pad 6 (w - 6) := by
        intro pad
        have no := hn.noPadRd j hj (w - 6) (by omega) pad
        rcases h with eq | eq
        · exact no.1 (by omega)
        · exact no.2 (by omega)
      obtain ⟨a, x, hx, pa, ea⟩ :=
        prev _ ll (by omega) (child _ (Or.inl rfl) ll)
      obtain ⟨b, y, hy, pb, eb⟩ :=
        prev _ rr (by omega) (child _ (Or.inr rfl) rr)
      have distinct := Nat.ne_of_lt (hn.ord j hj hp)
      have disjoint : a &&& b = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_land, Nat.zero_testBit]
        cases ha : a.testBit i <;> cases hb : b.testBit i <;> try rfl
        exact (sibling_has_no_common_ancestor hv hn single distinct el er
          (pa i ha) (pb i hb)).elim
      let choice := decide (M.op j = 0)
      refine ⟨a ||| b, combine choice x y, ReadOnce.gate choice disjoint hx hy, ?_, ?_⟩
      · intro i hi
        rw [Nat.testBit_lor] at hi
        rcases Bool.or_eq_true_iff.mp hi with left | right
        · exact up_append (pa i left) el
        · exact up_append (pb i right) er
      · intro u v
        have hgate := hv.w_eq j hj (repRow 3 u v) (row_mem u v)
        rw [agree_sources hj ll, agree_sources hj rr, ← ea u v, ← eb u v] at hgate
        have outval : M.sv 6 7 (6+j) (repRow 3 u v) = M.w j (repRow 3 u v) := by
          simp [Model.sv, show ¬ 6+j < 6 by omega, show 6+j < 13 by omega]
        rw [outval, hgate]
        have other : M.op j ≠ 2 := fun eq => hp (hn.padOp j hj eq)
        have op := hv.op_lt j hj
        by_cases zero : M.op j = 0
        · simp [combine, choice, gfun, zero, Nat.testBit_land]
        · have one : M.op j = 1 := by omega
          simp [combine, choice, gfun, zero, one, Nat.testBit_lor]

theorem five_gates_read_once {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) (seven : (activeGates M).card = 5) :
    ∃ s, ReadOnce s 238 := by
  have active : ¬ M.pad 6 6 := active_after_initial_two hv hn (by decide) (by decide)
  have out : M.so = 12 := (hn.out (by decide)).resolve_right active
  obtain ⟨s, t, repr, _, eval⟩ := wire_repr hv hn (unique_source_slots hv hn seven) 12
    (by decide) (fun _ => active)
  have eq : t = 238 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases inside : i < 9
    · let u : Fin 3 := ⟨i / 3, by omega⟩
      let v : Fin 3 := ⟨i % 3, by omega⟩
      have index : 3 * u.val + v.val = i := by dsimp [u, v]; omega
      have value := hv.out_eq (repRow 3 u v) (row_mem u v)
      rw [out] at value
      rw [← index, eval u v, value]
      exact gMask_row 238 u v
    · have bound : 2 ^ 9 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow ((range_of_read_once repr).2.2.trans_le bound),
        Nat.testBit_lt_two_pow ((show 238 < 2^9 by decide).trans_le bound)]
  exact ⟨s, eq ▸ repr⟩

end ReadOnce

namespace SharedCut

open Link
open Normalized
open ThreeLive
open SourceTree
open SourceInventory

abbrev Slot := Nat × Bool

structure Shared (M : Model) (removed : Slot) : Prop where
  used : removed ∈ slots M
  remaining_injective : Set.InjOn (source M) ((slots M).erase removed)

theorem shared_slot {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) (eight : (activeGates M).card = 6) :
    ∃ removed, Shared M removed := by
  classical
  have cardSlots : (slots M).card = 12 := by simp [slots, eight]
  have cardWires : ((slots M).image (source M)).card = 11 := by
    rw [source_image, distinct_sources_card hv hn, eight]
  have notInj : ¬ Set.InjOn (source M) (slots M) := by
    intro inj
    have e := Finset.card_image_of_injOn inj
    omega
  unfold Set.InjOn at notInj
  push_neg at notInj
  obtain ⟨p, hp, q, hq, eq, ne⟩ := notInj
  have image : ((slots M).erase p).image (source M) = (slots M).image (source M) := by
    ext w
    constructor
    · intro h
      obtain ⟨s, hs, e⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨s, (Finset.mem_erase.mp hs).2, e⟩
    · intro h
      obtain ⟨s, hs, e⟩ := Finset.mem_image.mp h
      by_cases same : s = p
      · subst s
        exact Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨Ne.symm ne, hq⟩, eq.symm.trans e⟩
      · exact Finset.mem_image.mpr ⟨s, Finset.mem_erase.mpr ⟨same, hs⟩, e⟩
  refine ⟨p, hp, Finset.card_image_iff.mp ?_⟩
  rw [image, cardWires, Finset.card_erase_of_mem hp, cardSlots]

abbrev sharedWire (M : Model) (removed : Slot) : Nat := source M removed

def cutSource (M : Model) (removed : Slot) (s : Slot) : Nat :=
  if s = removed then 13
  else if source M s = sharedWire M removed then 14 else source M s

private theorem slot_lt {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {s : Slot} (mem : s ∈ slots M) :
    source M s < 6+s.1 :=
  reads_strict hv hn ⟨s, mem, rfl, rfl⟩

private theorem slot_gate_bound {M : Model} {s : Slot} (mem : s ∈ slots M) :
    s.1 < 7 :=
  Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_product.mp mem).1).1

theorem cutSource_injective {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {removed : Slot} (shared : Shared M removed) :
    Set.InjOn (cutSource M removed) (slots M) := by
  intro a ha b hb eq
  have rawA := slot_lt hv hn ha
  have rawB := slot_lt hv hn hb
  have gateA := slot_gate_bound ha
  have gateB := slot_gate_bound hb
  by_cases ea : a = removed
  · by_cases eb : b = removed
    · exact ea.trans eb.symm
    · by_cases sb : source M b = sharedWire M removed
      · simp [cutSource, ea, eb, sb] at eq
      · simp only [cutSource, if_pos ea, if_neg eb, if_neg sb] at eq
        omega
  · by_cases eb : b = removed
    · by_cases sa : source M a = sharedWire M removed
      · simp [cutSource, ea, eb, sa] at eq
      · simp only [cutSource, if_neg ea, if_pos eb, if_neg sa] at eq
        omega
    · apply shared.remaining_injective (Finset.mem_erase.mpr ⟨ea, ha⟩)
        (Finset.mem_erase.mpr ⟨eb, hb⟩)
      by_cases sa : source M a = sharedWire M removed <;>
        by_cases sb : source M b = sharedWire M removed
      · exact sa.trans sb.symm
      · simp only [cutSource, if_neg ea, if_neg eb, if_pos sa, if_neg sb] at eq
        omega
      · simp only [cutSource, if_neg ea, if_neg eb, if_neg sa, if_pos sb] at eq
        omega
      · simpa only [cutSource, if_neg ea, if_neg eb, if_neg sa, if_neg sb] using eq

def CutReads (M : Model) (removed : Slot) (w out : Nat) : Prop :=
  ∃ slot ∈ slots M, out = 6+slot.1 ∧ cutSource M removed slot = w

def rankWire (w : Nat) : Nat := if w < 13 then w+1 else 0

theorem cut_reads_increasing {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {removed : Slot} {w out : Nat} (edge : CutReads M removed w out) :
    rankWire w < rankWire out := by
  obtain ⟨s, mem, rfl, rfl⟩ := edge
  have old := slot_lt hv hn mem
  have gate := slot_gate_bound mem
  have dst : 6+s.1 < 13 := by omega
  have src : source M s < 13 := by omega
  by_cases eq : s = removed
  · rw [cutSource, if_pos eq]
    simp only [rankWire, if_pos dst, if_neg (show ¬ 13 < 13 by decide)]
    omega
  · by_cases compare : source M s = sharedWire M removed
    · rw [cutSource, if_neg eq, if_pos compare]
      simp only [rankWire, if_pos dst, if_neg (show ¬ 14 < 13 by decide)]
      omega
    · rw [cutSource, if_neg eq, if_neg compare]
      simp only [rankWire, if_pos dst, if_pos src]
      omega

theorem cut_reads_unique {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {removed : Slot} (shared : Shared M removed) {w a b : Nat}
    (first : CutReads M removed w a) (second : CutReads M removed w b) : a = b := by
  obtain ⟨l, hl, rfl, le⟩ := first
  obtain ⟨r, hr, rfl, re⟩ := second
  rw [cutSource_injective hv hn shared hl hr (le.trans re.symm)]

theorem shared_wire_terminal {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {removed : Slot} (used : removed ∈ slots M) {w : Nat} :
    ¬ CutReads M removed (sharedWire M removed) w := by
  rintro ⟨s, _, _, eq⟩
  have bound := slot_lt hv hn used
  have gate := slot_gate_bound used
  have lo : sharedWire M removed < 13 := by
    change source M removed < 13
    omega
  by_cases same : s = removed
  · rw [cutSource, if_pos same] at eq
    exact (Nat.ne_of_lt lo) eq.symm
  · by_cases other : source M s = sharedWire M removed
    · rw [cutSource, if_neg same, if_pos other] at eq
      exact (Nat.ne_of_lt (lo.trans (by decide : 13 < 14))) eq.symm
    · exact other (by simpa only [cutSource, if_neg same, if_neg other] using eq)

end SharedCut

namespace CutPaths

open Link
open Normalized
open SourceTree
open SharedCut

inductive Path (M : Model) (d : Slot) : Nat → Nat → Prop
  | refl (w : Nat) : Path M d w w
  | step {x y z : Nat} : CutReads M d x y → Path M d y z → Path M d x z

theorem append {M : Model} {d : Slot} {x y z : Nat}
    (path : Path M d x y) (edge : CutReads M d y z) : Path M d x z := by
  induction path with
  | refl => exact Path.step edge (Path.refl _)
  | step first _ ih => exact Path.step first (ih edge)

theorem rank_le {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {d : Slot} {x z : Nat} (p : Path M d x z) :
    rankWire x ≤ rankWire z := by
  induction p with
  | refl => exact Nat.le_refl _
  | step edge _ ih => exact (Nat.le_of_lt (cut_reads_increasing hv hn edge)).trans ih

theorem comparable {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {d : Slot} (shared : Shared M d) {w a b : Nat}
    (pa : Path M d w a) (pb : Path M d w b) : Path M d a b ∨ Path M d b a := by
  induction pa generalizing b with
  | refl => exact Or.inl pb
  | step first rest ih =>
    cases pb with
    | refl => exact Or.inr (Path.step first rest)
    | step other suffix =>
      have eq := cut_reads_unique hv hn shared first other
      exact ih (eq.symm ▸ suffix)

theorem siblings_disjoint {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {d : Slot} (shared : Shared M d) {w a b out : Nat}
    (ne : a ≠ b) (ea : CutReads M d a out) (eb : CutReads M d b out)
    (pa : Path M d w a) (pb : Path M d w b) : False := by
  rcases comparable hv hn shared pa pb with ab | ba
  · cases ab with
    | refl => exact ne rfl
    | step edge suffix =>
      have eq := cut_reads_unique hv hn shared edge ea
      exact (Nat.not_lt_of_ge (rank_le hv hn (eq ▸ suffix))) (cut_reads_increasing hv hn eb)
  · cases ba with
    | refl => exact ne rfl
    | step edge suffix =>
      have eq := cut_reads_unique hv hn shared edge eb
      exact (Nat.not_lt_of_ge (rank_le hv hn (eq ▸ suffix))) (cut_reads_increasing hv hn ea)

theorem shared_lt {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {d : Slot} (hd : d ∈ slots M) : sharedWire M d < 12 := by
  have used : Reads M (sharedWire M d) (6+d.1) := ⟨d, hd, rfl, rfl⟩
  have bound := reads_strict hv hn used
  have gate := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_product.mp hd).1).1
  omega

theorem marker_path_below {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {d : Slot} (hd : d ∈ slots M) {w : Nat}
    (hw : 13 ≤ w) (p : Path M d w (sharedWire M d)) : False := by
  have below := shared_lt hv hn hd
  cases p with
  | refl => omega
  | step edge rest =>
    obtain ⟨s, hs, rfl, eq⟩ := edge
    have old : source M s < 6+s.1 := reads_strict hv hn ⟨s, hs, rfl, rfl⟩
    have gate := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_product.mp hs).1).1
    have same : source M s = sharedWire M d := by
      by_cases e : s = d
      · subst s
        rfl
      · by_contra ne
        rw [cutSource, if_neg e, if_neg ne] at eq
        omega
    have rank := rank_le hv hn rest
    simp only [rankWire, if_pos (show 6+s.1 < 13 by omega),
      if_pos (show sharedWire M d < 13 by omega)] at rank
    omega

private theorem terminal_path {M : Model} {d : Slot} {x y : Nat}
    (stop : ∀ w, ¬ CutReads M d x w) (p : Path M d x y) : x = y := by
  cases p with
  | refl => rfl
  | step edge _ => exact (stop _ edge).elim

theorem no_shared_input {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {d : Slot} (shared : Shared M d) {w : Nat}
    (cone : Path M d w (sharedWire M d)) (out : Path M d w 12) : False := by
  have below := shared_lt hv hn shared.used
  rcases comparable hv hn shared cone out with forward | backward
  · have eq := terminal_path (fun _ => shared_wire_terminal hv hn shared.used) forward
    omega
  · have e := rank_le hv hn backward
    simp only [rankWire, if_pos (show 12 < 13 by decide),
      if_pos (show sharedWire M d < 13 by omega)] at e
    omega

end CutPaths

namespace CutExpression

open Link
open Promise (repRow)
open Normalized
open ThreeLive
open SourceTree (slots source Reads reads_strict)
open SharedCut
open CutPaths
open ReadOnce (ReadOnce inputBits combine)

def markerIndex (b : Bool) : Nat := if b then 7 else 6

def origin (i : Nat) : Nat := if i < 6 then i else i+7

inductive Expr : Nat → Type
  | input (i : Fin 6) : Expr (2 ^ i.val)
  | marker (b : Bool) : Expr (2 ^ markerIndex b)
  | gate {a b : Nat} (andGate : Bool) (separate : a &&& b = 0)
      (left : Expr a) (right : Expr b) : Expr (a ||| b)

def Expr.evaluate (row : Nat) (shared : Bool) : {s : Nat} → Expr s → Bool
  | _, .input i => row.testBit i.val
  | _, .marker _ => shared
  | _, .gate choose _ l r =>
    if choose then l.evaluate row shared && r.evaluate row shared
    else l.evaluate row shared || r.evaluate row shared

def Expr.tableWith (shared : Nat) : {s : Nat} → Expr s → Nat
  | _, .input i => inputBits i.val
  | _, .marker _ => shared
  | _, .gate choose _ l r => combine choose (l.tableWith shared) (r.tableWith shared)

theorem Expr.plain {s : Nat} (e : Expr s) (bound : s < 64) :
    ReadOnce s (e.tableWith 0) := by
  induction e with
  | input i => exact ReadOnce.input i
  | marker b => cases b <;> simp [markerIndex] at bound
  | gate c sep l r lh rh =>
    exact ReadOnce.gate c sep (lh (Nat.left_le_or.trans_lt bound))
      (rh (Nat.right_le_or.trans_lt bound))

theorem Expr.plain_value {s : Nat} (e : Expr s) (bound : s < 64)
    (r : Nat) (a b : Bool) : e.evaluate r a = e.evaluate r b := by
  induction e with
  | input i => rfl
  | marker t => cases t <;> simp [markerIndex] at bound
  | gate c sep l p lh ph =>
    simp only [Expr.evaluate, lh (Nat.left_le_or.trans_lt bound),
      ph (Nat.right_le_or.trans_lt bound)]

private theorem input_value : ∀ (i : Fin 6) (u v : Fin 3),
    (inputBits i.val).testBit (3 * u.val+v.val) = (repRow 3 u v).testBit i.val := by
  decide +kernel

theorem Expr.table_eval {s : Nat} (e : Expr s) (shared : Nat) (u v : Fin 3) :
    (e.tableWith shared).testBit (3 * u.val+v.val) =
      e.evaluate (repRow 3 u v) (shared.testBit (3 * u.val+v.val)) := by
  induction e with
  | input i => exact input_value i u v
  | marker _ => rfl
  | gate c _ _ _ lh rh =>
    cases c <;> simp [Expr.tableWith, Expr.evaluate, combine, Nat.testBit_land,
      Nat.testBit_lor, lh, rh]

def legal (M : Model) (w : Nat) : Prop :=
  w < 15 ∧ (6 ≤ w → w < 13 → ¬ M.pad 6 (w-6))

def cutValue (M : Model) (d : Slot) (wire r : Nat) : Bool :=
  M.sv 6 7 (if wire < 13 then wire else sharedWire M d) r

private theorem gate_mem {M : Model} {s : Slot} (hs : s ∈ slots M) :
    s.1 < 7 ∧ ¬ M.pad 6 s.1 := by
  have fs := Finset.mem_filter.mp (Finset.mem_product.mp hs).1
  exact ⟨Finset.mem_range.mp fs.1, fs.2⟩

theorem cutSource_legal {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) (d : Slot) {s : Slot} (mem : s ∈ slots M) :
    legal M (cutSource M d s) := by
  have st := gate_mem mem
  have before : source M s < 6+s.1 := reads_strict hv hn ⟨s, mem, rfl, rfl⟩
  by_cases eq : s = d
  · rw [cutSource, if_pos eq]
    exact ⟨by decide, fun _ impossible => False.elim (by omega)⟩
  · by_cases same : source M s = sharedWire M d
    · rw [cutSource, if_neg eq, if_pos same]
      exact ⟨by decide, fun _ impossible => False.elim (by omega)⟩
    · rw [cutSource, if_neg eq, if_neg same]
      refine ⟨by omega, fun raw _ pad => ?_⟩
      have prior : source M s - 6 < s.1 := by omega
      have eqwire : source M s = 6 + (source M s - 6) := by omega
      have no := hn.noPadRd s.1 st.1 _ prior pad
      obtain ⟨j,b⟩ := s
      cases b
      · exact no.1 eqwire
      · exact no.2 eqwire

theorem cutSource_value {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) (d : Slot) {s : Slot} (mem : s ∈ slots M) (r : Nat) :
    cutValue M d (cutSource M d s) r = M.sv 6 s.1 (source M s) r := by
  have st := gate_mem mem
  have before : source M s < 6+s.1 := reads_strict hv hn ⟨s, mem, rfl, rfl⟩
  have lo : source M s < 13 := by omega
  have restore : (if cutSource M d s < 13 then cutSource M d s else sharedWire M d) =
      source M s := by
    by_cases eq : s = d
    · subst s
      simp [cutSource]
    · by_cases same : source M s = sharedWire M d
      · simp [cutSource, eq, same]
      · simp [cutSource, eq, same, lo]
  unfold cutValue
  rw [restore]
  by_cases low : source M s < 6 <;> simp [Model.sv, low, lo, before]

theorem expression_for_wire {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {d : Slot} (shared : Shared M d) (w : Nat) (law : legal M w) :
    ∃ (s : Nat) (expr : Expr s),
      (∀ i, s.testBit i = true → Path M d (origin i) w) ∧
      ∀ r ∈ rows, expr.evaluate r (M.sv 6 7 (sharedWire M d) r) = cutValue M d w r := by
  have build : ∀ n w, rankWire w = n → legal M w →
    ∃ (s : Nat) (expr : Expr s),
      (∀ i, s.testBit i = true → Path M d (origin i) w) ∧
      ∀ r ∈ rows, expr.evaluate r (M.sv 6 7 (sharedWire M d) r) = cutValue M d w r := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n smaller =>
      intro w rank good
      by_cases marker : 13 ≤ w
      · have poss : w = 13 ∨ w = 14 := by have h := good.1; omega
        have leaf (b : Bool) (eq : w = origin (markerIndex b)) :
            ∃ (s : Nat) (expr : Expr s),
              (∀ i, s.testBit i = true → Path M d (origin i) w) ∧
              ∀ r ∈ rows, expr.evaluate r (M.sv 6 7 (sharedWire M d) r) = cutValue M d w r := by
          refine ⟨_, Expr.marker b, ?_, ?_⟩
          · intro i bit
            rw [Nat.testBit_two_pow] at bit
            obtain rfl := of_decide_eq_true bit
            rw [eq]
            exact Path.refl _
          · intro r _
            simp [Expr.evaluate, cutValue, show ¬ w < 13 by omega]
        rcases poss with e | e
        · exact leaf false e
        · exact leaf true e
      · have small : w < 13 := by omega
        by_cases input : w < 6
        · refine ⟨_, Expr.input ⟨w,input⟩, ?_, ?_⟩
          · intro i bit
            rw [Nat.testBit_two_pow] at bit
            obtain rfl := of_decide_eq_true bit
            simpa [origin, input] using Path.refl (M := M) (d := d) w
          · intro r _
            simp [Expr.evaluate, cutValue, Model.sv, small, input]
        · obtain ⟨j, rfl⟩ : ∃ j, w = 6+j := ⟨w-6, by omega⟩
          have hj : j < 7 := by omega
          have live : ¬ M.pad 6 j := by simpa using good.2 (by omega) small
          have mem : j ∈ ThreeLive.activeGates M :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, live⟩
          have leftMem : (j,false) ∈ slots M :=
            Finset.mem_product.mpr ⟨mem, Finset.mem_univ _⟩
          have rightMem : (j,true) ∈ slots M :=
            Finset.mem_product.mpr ⟨mem, Finset.mem_univ _⟩
          let x := cutSource M d (j,false)
          let y := cutSource M d (j,true)
          have e₁ : CutReads M d x (6+j) := ⟨(j,false),leftMem,rfl,rfl⟩
          have e₂ : CutReads M d y (6+j) := ⟨(j,true),rightMem,rfl,rfl⟩
          have xlt := cut_reads_increasing hv hn e₁
          have ylt := cut_reads_increasing hv hn e₂
          obtain ⟨a, l, lp, lv⟩ := smaller _ (xlt.trans_eq rank) x rfl (cutSource_legal hv hn d leftMem)
          obtain ⟨b, r, rp, rv⟩ := smaller _ (ylt.trans_eq rank) y rfl (cutSource_legal hv hn d rightMem)
          have ne : x ≠ y := by
            intro eq
            have pair := cutSource_injective hv hn shared leftMem rightMem eq
            exact Bool.noConfusion (congrArg Prod.snd pair)
          have sep : a &&& b = 0 := by
            apply Nat.eq_of_testBit_eq
            intro i
            rw [Nat.testBit_land, Nat.zero_testBit]
            cases ha : a.testBit i <;> cases hb : b.testBit i <;> try rfl
            exact (siblings_disjoint hv hn shared ne e₁ e₂ (lp i ha) (rp i hb)).elim
          let choose := decide (M.op j = 0)
          refine ⟨_, Expr.gate choose sep l r, ?_, ?_⟩
          · intro i bit
            rw [Nat.testBit_lor] at bit
            rcases Bool.or_eq_true_iff.mp bit with h | h
            · exact append (lp i h) e₁
            · exact append (rp i h) e₂
          · intro row hr
            have out : cutValue M d (6+j) row = M.w j row := by
              simp [cutValue, Model.sv, small, show ¬ 6+j < 6 by omega]
            have al := (lv row hr).trans (cutSource_value hv hn d leftMem row)
            have ar := (rv row hr).trans (cutSource_value hv hn d rightMem row)
            rw [out, hv.w_eq j hj row hr]
            simp only [Expr.evaluate, al, ar]
            have nonConst : M.op j ≠ 2 := fun two => live (hn.padOp j hj two)
            have opt := hv.op_lt j hj
            by_cases zero : M.op j = 0
            · simp [choose, gfun, zero, source]
            · have one : M.op j = 1 := by omega
              simp [choose, gfun, one, source]
  exact build (rankWire w) w rfl law

end CutExpression

namespace Contraction

open Link
open Promise (repRow gMask_row)
open Normalized
open ThreeLive
open SourceTree (slots source Reads reads_strict)
open SharedCut
open CutPaths
open CutExpression
open CutExpression (Expr origin)
open ReadOnce (ReadOnce inputBits combine range_of_read_once)

private theorem source_legal {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) {s : Slot} (mem : s ∈ slots M) : legal M (source M s) := by
  have before : source M s < 6 + s.1 := reads_strict hv hn ⟨s, mem, rfl, rfl⟩
  have g := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_product.mp mem).1).1
  refine ⟨by omega, fun above _ pad => ?_⟩
  have no := hn.noPadRd s.1 g (source M s - 6) (by omega) pad
  have eq : source M s = 6 + (source M s - 6) := by omega
  obtain ⟨j, b⟩ := s
  cases b
  · exact no.1 eq
  · exact no.2 eq

private theorem bounded_table {s shared : Nat} (e : Expr s) (bound : shared < 512) :
    e.tableWith shared < 512 := by
  induction e with
  | input i => exact (range_of_read_once (ReadOnce.input i)).2.2
  | marker b => exact bound
  | gate c _ _ _ ha hb =>
    cases c
    · exact Nat.or_lt_two_pow (n := 9) ha hb
    · exact Nat.and_lt_two_pow (n := 9) _ hb

theorem six_gates_contract {M : Model} (hv : Valid 6 7 table (· ∈ rows) M)
    (hn : NF 6 7 M) (eight : (activeGates M).card = 6) :
    ∃ (a b x : Nat) (outer : Expr b),
      ReadOnce a x ∧ a &&& b = 0 ∧ outer.tableWith x = 238 := by
  obtain ⟨d, shared⟩ := shared_slot hv hn eight
  have qlt := shared_lt hv hn shared.used
  have live := active_after_initial_two hv hn (j := 6) (by decide) (by decide)
  have out : M.so = 12 := (hn.out (by decide)).resolve_right live
  obtain ⟨a, cone, qa, qv⟩ :=
    expression_for_wire hv hn shared (sharedWire M d) (source_legal hv hn shared.used)
  obtain ⟨b, outer, ba, bv⟩ := expression_for_wire hv hn shared 12
    ⟨by decide, fun _ _ => live⟩
  have small : a < 64 := by
    change a < 2 ^ 6
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases bit : a.testBit i = true
    · exact (marker_path_below hv hn shared.used (w := origin i)
        (by unfold origin; rw [if_neg (by omega : ¬ i < 6)]; omega) (qa i bit)).elim
    · exact Bool.eq_false_iff.mpr bit
  have sep : a &&& b = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land, Nat.zero_testBit]
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> try rfl
    exact (no_shared_input hv hn shared (qa i ha) (ba i hb)).elim
  let x := cone.tableWith 0
  have plain : ReadOnce a x := cone.plain small
  have shared_value (u v : Fin 3) :
      x.testBit (3 * u.val+v.val) = M.sv 6 7 (sharedWire M d) (repRow 3 u v) := by
    change (cone.tableWith 0).testBit (3 * u.val+v.val) = _
    rw [Expr.table_eval]
    calc
      _ = cone.evaluate _ (M.sv 6 7 (sharedWire M d) (repRow 3 u v)) :=
        cone.plain_value small _ _ _
      _ = cutValue M d (sharedWire M d) (repRow 3 u v) := qv _ (row_mem u v)
      _ = _ := by simp [cutValue, show sharedWire M d < 13 by omega]
  refine ⟨a,b,x,outer,plain,sep,?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < 9
  · let u : Fin 3 := ⟨i / 3, by omega⟩
    let v : Fin 3 := ⟨i % 3, by omega⟩
    have index : 3 * u.val+v.val = i := by dsimp [u,v]; omega
    have value := hv.out_eq (repRow 3 u v) (row_mem u v)
    rw [out] at value
    rw [← index, outer.table_eval, shared_value, bv _ (row_mem u v)]
    change M.sv 6 7 12 (repRow 3 u v) = (238 : Nat).testBit (3 * u.val+v.val)
    rw [value]
    exact gMask_row 238 u v
  · have cap : 2^9 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    have bound := bounded_table outer (range_of_read_once plain).2.2
    rw [Nat.testBit_lt_two_pow (bound.trans_le cap),
      Nat.testBit_lt_two_pow ((show 238 < 2^9 by decide).trans_le cap)]

end Contraction

namespace ContractionGuard

open Promise (repRow)
open Normalized (Graph)
open CutExpression
open CutExpression

theorem evaluate_mono {s r q : Nat} (e : Expr s) {x y : Bool} (shared : x = true → y = true)
    (raw : ∀ i < 6, s.testBit i = true → r.testBit i = true → q.testBit i = true) :
    e.evaluate r x = true → e.evaluate q y = true := by
  induction e with
  | input i =>
    exact raw i.val i.isLt Nat.testBit_two_pow_self
  | marker _ => exact shared
  | @gate a b choose disjoint l rr lh rh =>
    have monoL : l.evaluate r x = true → l.evaluate q y = true := lh (fun i lt bit =>
      raw i lt (by rw [Nat.testBit_lor, bit]; rfl))
    have monoR : rr.evaluate r x = true → rr.evaluate q y = true := rh (fun i lt bit =>
      raw i lt (by rw [Nat.testBit_lor, bit]; cases a.testBit i <;> rfl))
    cases choose
    · intro hv
      rcases Bool.or_eq_true_iff.mp hv with pos | pos
      · exact Bool.or_eq_true_iff.mpr (Or.inl (monoL pos))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (monoR pos))
    · intro hv
      obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp hv
      exact Bool.and_eq_true_iff.mpr ⟨monoL left, monoR right⟩

theorem forced_shared_bits {a b x : Nat} (e : Expr b) (separate : a &&& b = 0)
    (out : e.tableWith x = 238) (u v u' v' : Fin 3)
    (pos : Graph u v = true) (neg : Graph u' v' = false)
    (raw : ∀ i < 6, a.testBit i = false → (repRow 3 u v).testBit i = true →
      (repRow 3 u' v').testBit i = true) :
    x.testBit (3 * u.val+v.val) = true ∧ x.testBit (3 * u'.val+v'.val) = false := by
  have agree (i j : Fin 3) : e.evaluate (repRow 3 i j) (x.testBit (3 * i.val+j.val)) = Graph i j := by
    rw [← Expr.table_eval, out]
  have need : ¬ (x.testBit (3 * u.val+v.val) = true → x.testBit (3 * u'.val+v'.val) = true) := by
    intro relation
    have edge := evaluate_mono e relation (fun i bound present =>
      raw i bound (by
        have zero := congrArg (fun t : Nat => t.testBit i) separate
        rw [Nat.testBit_land, Nat.zero_testBit, present] at zero
        simpa using zero))
    have impossible := edge ((agree u v).trans pos)
    rw [agree u' v', neg] at impossible
    contradiction
  cases hp : x.testBit (3 * u.val+v.val) <;>
    cases hq : x.testBit (3 * u'.val+v'.val) <;> simp_all

theorem support_bounds {s : Nat} (e : Expr s) : 0 < s ∧ s < 256 := by
  induction e with
  | input i =>
    exact (show ∀ i : Fin 6, 0 < 2 ^ i.val ∧ 2 ^ i.val < 256 by decide +kernel) i
  | marker b => cases b <;> decide
  | @gate a b _ _ _ _ ha hb =>
    refine ⟨?_, Nat.or_lt_two_pow (n := 8) ha.2 hb.2⟩
    exact lt_of_lt_of_le ha.1 (Nat.left_le_or (m := b))

end ContractionGuard

namespace Catalogue

abbrev Catalogue := Array (Nat × List Nat)

def row (rows : Catalogue) (s : Nat) : Nat × List Nat := rows[s]?.getD (0, [])

def bit (rows : Catalogue) (s v : Nat) : Bool := (row rows s).1.testBit v

def entries (rows : Catalogue) (s : Nat) : List Nat := (row rows s).2

def pack : List Nat → Nat
  | [] => 0
  | v :: vs => 2 ^ v ||| pack vs

def agrees (rows : Catalogue) (s : Nat) : Prop := pack (entries rows s) = (row rows s).1

instance (rows : Catalogue) (s : Nat) : Decidable (agrees rows s) := by
  unfold agrees
  infer_instance

private theorem pack_bit (vs : List Nat) (v : Nat) :
    (pack vs).testBit v = true ↔ v ∈ vs := by
  induction vs with
  | nil => simp [pack]
  | cons x xs ih =>
    simp only [pack, Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true_iff,
      decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

theorem bit_iff {rows : Catalogue} {s v : Nat} (h : agrees rows s) :
    bit rows s v = true ↔ v ∈ entries rows s := by
  unfold agrees at h
  rw [bit, ← h]
  exact pack_bit _ _

def checkPair (rows : Catalogue) (a b : Nat) : Bool :=
  if a ≤ b ∧ a &&& b = 0 then
    (entries rows a).all fun x =>
      (entries rows b).all fun y =>
        bit rows (a ||| b) (x &&& y) && bit rows (a ||| b) (x ||| y)
  else true

def checkRow (rows : Catalogue) (a : Nat) : Bool :=
  (List.range rows.size).all (checkPair rows a)

private theorem close_ordered {rows : Catalogue}
    (checked : ∀ a : Fin rows.size, checkRow rows a = true)
    {a b x y : Nat} (ar : a < rows.size) (br : b < rows.size)
    (compatible : agrees rows (a ||| b))
    (order : a ≤ b) (sep : a &&& b = 0)
    (hx : x ∈ entries rows a) (hy : y ∈ entries rows b) :
    x &&& y ∈ entries rows (a ||| b) ∧ x ||| y ∈ entries rows (a ||| b) := by
  have r := checked ⟨a, ar⟩
  unfold checkRow at r
  have pair := List.all_eq_true.mp r b (List.mem_range.mpr br)
  change checkPair rows a b = true at pair
  rw [checkPair, ite_eq_left ⟨order,sep⟩] at pair
  have acts := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp pair x hx) y hy)
  exact ⟨(bit_iff compatible).mp acts.1, (bit_iff compatible).mp acts.2⟩

theorem close {rows : Catalogue}
    (checked : ∀ a : Fin rows.size, checkRow rows a = true)
    {a b x y : Nat} (ar : a < rows.size) (br : b < rows.size)
    (compatible : agrees rows (a ||| b))
    (sep : a &&& b = 0) (hx : x ∈ entries rows a) (hy : y ∈ entries rows b) :
    x &&& y ∈ entries rows (a ||| b) ∧ x ||| y ∈ entries rows (a ||| b) := by
  rcases Nat.le_total a b with hab | hba
  · exact close_ordered checked ar br compatible hab sep hx hy
  · have agreed : agrees rows (b ||| a) := by rwa [Nat.lor_comm]
    have h := close_ordered checked br ar agreed hba (by rwa [Nat.land_comm]) hy hx
    simpa only [Nat.land_comm y x, Nat.lor_comm y x, Nat.lor_comm b a] using h

theorem excluded {rows : Catalogue} {s t : Nat} (compatible : agrees rows s)
    (absent : bit rows s t = false) (mem : t ∈ entries rows s) : False := by
  have hit : bit rows s t = true := (bit_iff compatible).mpr mem
  exact Bool.noConfusion (hit.symm.trans absent)

end Catalogue

namespace Catalogues
def candidates : List (Nat × Nat) := [(1, 7), (2, 56), (4, 448), (8, 73), (9, 79), (16, 146), (18, 186), (32, 292), (36, 484)]

def plain : Catalogue.Catalogue := #[
  (0x0, []),
  (0x80, [7]),
  (0x100000000000000, [56]),
  (0x8000000000000001, [0, 63]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x2000000000000000000, [73]),
  (0x80000000000000000002, [1, 79]),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x4000000000000000000000000000000000000, [146]),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511])
]

def case_1_7 : Catalogue.Catalogue := #[
  (0x0, []),
  (0x0, []),
  (0x100000000000000, [56]),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x0, []),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x0, []),
  (0x2000000000000000000, [73]),
  (0x0, []),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x0, []),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x0, []),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x0, []),
  (0x4000000000000000000000000000000000000, [146]),
  (0x0, []),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x0, []),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x0, []),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x0, []),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x0, []),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x0, []),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x0, []),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x0, []),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x0, []),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x0, []),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x0, []),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x0, []),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x0, []),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x0, []),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x0, []),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x0, []),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x0, []),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x0, []),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x80, [7]),
  (0x0, []),
  (0x8000000000000001, [0, 63]),
  (0x0, []),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x0, []),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x0, []),
  (0x80000000000000000002, [1, 79]),
  (0x0, []),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x0, []),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x0, []),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x0, []),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x0, []),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x0, []),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x0, []),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x0, []),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x0, []),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x0, []),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x0, []),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x0, []),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x0, []),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x0, []),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x0, []),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x0, []),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x0, []),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x0, []),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x0, []),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x0, []),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x0, []),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x0, []),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0x0, []),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x80, [7]),
  (0x0, []),
  (0x8000000000000001, [0, 63]),
  (0x0, []),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x0, []),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x0, []),
  (0x80000000000000000002, [1, 79]),
  (0x0, []),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x0, []),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x0, []),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x0, []),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x0, []),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x0, []),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x0, []),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x0, []),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x0, []),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x0, []),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x0, []),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x0, []),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x0, []),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x0, []),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x0, []),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x0, []),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x0, []),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x0, []),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x0, []),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x0, []),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x0, []),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x0, []),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0x0, []),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x80, [7]),
  (0x0, []),
  (0x8000000000000081, [0, 7, 63]),
  (0x0, []),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000081, [0, 7, 455]),
  (0x0, []),
  (0x80000000000000810000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008100000000000081, [0, 7, 56, 63, 448, 455, 511]),
  (0x0, []),
  (0x80000000000000000082, [1, 7, 79]),
  (0x0, []),
  (0x80000000000082008200000000008383, [0, 1, 7, 8, 9, 15, 57, 63, 73, 79, 127]),
  (0x0, []),
  (0x80820000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000082830000000000000083, [0, 1, 7, 64, 65, 71, 73, 79, 449, 455, 463]),
  (0x0, []),
  (0x82000000000083830000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083838300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 63, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 455, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x80000000000000000000000000000000000084, [2, 7, 151]),
  (0x0, []),
  (0x800000000084000000000000000000008400000000850085, [0, 2, 7, 16, 18, 23, 58, 63, 146, 151, 191]),
  (0x0, []),
  (0x8000840000000000000000000000000000000000000000000000000000000000000000000000000084008500000000000000000000000000000085, [0, 2, 7, 128, 130, 135, 146, 151, 450, 455, 471]),
  (0x0, []),
  (0x84000000008500850000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000008500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 63, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 455, 464, 466, 471, 506, 511]),
  (0x0, []),
  (0x8000000000000000008800000000000000008800000000000000008f, [0, 1, 2, 3, 7, 75, 79, 147, 151, 223]),
  (0x0, []),
  (0x8000000088000000880000008c8c0000880000008a008a008f000000898f8f8f, [0, 1, 2, 3, 7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 79, 89, 91, 95, 123, 127, 146, 147, 151, 154, 155, 159, 187, 191, 219, 223, 255]),
  (0x0, []),
  (0x8088888f00000000000000000000000000000000000000000000000000000000888c8a8900000000008c008f0000000000008a8f000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 67, 71, 73, 75, 79, 128, 129, 130, 131, 135, 146, 147, 151, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 223, 448, 449, 450, 451, 455, 459, 463, 467, 471, 479]),
  (0x0, []),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f8f8f8f0000008a8f8f8f8f000000898f8f8f, [0, 1, 2, 3, 7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 67, 71, 72, 73, 74, 75, 79, 80, 81, 82, 83, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 131, 135, 136, 137, 138, 139, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000090, [4, 7, 295]),
  (0x0, []),
  (0x80000090000000000000000000000000000000000000000000000000000000009000009100000091, [0, 4, 7, 32, 36, 39, 60, 63, 292, 295, 319]),
  (0x0, []),
  (0x80000000900000000000000000000000000000000000000090000000910000000000000000000000000000000000000000000000000000000000000091, [0, 4, 7, 256, 260, 263, 292, 295, 452, 455, 487]),
  (0x0, []),
  (0x90000091000000910000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000009100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 63, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 455, 480, 484, 487, 508, 511]),
  (0x0, []),
  (0x800000000000000000a00000000000000000000000000000000000000000000000000000a00000000000000000b3, [0, 1, 4, 5, 7, 77, 79, 293, 295, 367]),
  (0x0, []),
  (0x8000a00000000000a000b0b00000000000000000000000000000000000000000a000a2000000a200b300a1b30000b3b3, [0, 1, 4, 5, 7, 8, 9, 12, 13, 15, 32, 33, 36, 37, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 79, 105, 109, 111, 125, 127, 292, 293, 295, 300, 301, 303, 317, 319, 365, 367, 383]),
  (0x0, []),
  (0x80a00000a0b300000000000000000000a0b00000a2a1000000b0000000b300000000000000000000000000000000000000000000a2b300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 69, 71, 73, 77, 79, 256, 257, 260, 261, 263, 292, 293, 295, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 367, 448, 449, 452, 453, 455, 461, 463, 485, 487, 495]),
  (0x0, []),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000b3b300000000000000000000000000000000b300a2b30000b3b3b300a1b30000b3b3, [0, 1, 4, 5, 7, 8, 9, 12, 13, 15, 32, 33, 36, 37, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 69, 71, 72, 73, 76, 77, 79, 96, 97, 100, 101, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 261, 263, 264, 265, 268, 269, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x800000000000000000000000000000000000c00000000000000000000000000000000000c00000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 151, 294, 295, 439]),
  (0x0, []),
  (0x80c00000000000000000000000000000c0d000d0000000000000000000000000c0c4000000c400000000000000000000d5c100d500d500d5, [0, 2, 4, 6, 7, 16, 18, 20, 22, 23, 32, 34, 36, 38, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 151, 178, 182, 183, 190, 191, 292, 294, 295, 308, 310, 311, 318, 319, 438, 439, 447]),
  (0x0, []),
  (0x8000c000c000d500c000d000c400c10000000000000000000000d0000000d500000000000000000000000000c400d5000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 134, 135, 146, 150, 151, 256, 258, 260, 262, 263, 292, 294, 295, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 439, 448, 450, 452, 454, 455, 470, 471, 486, 487, 503]),
  (0x0, []),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d500d500d50000000000000000d5c400d500d500d50000000000000000d5c100d500d500d5, [0, 2, 4, 6, 7, 16, 18, 20, 22, 23, 32, 34, 36, 38, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 134, 135, 144, 146, 148, 150, 151, 160, 162, 164, 166, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 262, 263, 272, 274, 276, 278, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x0, []),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a5ff99ffffff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x0, []),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f0000000ff0000000088ccaa990000000000cc00ff000000000000aaff00000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 77, 79, 128, 129, 130, 131, 132, 133, 134, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 261, 262, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0x0, []),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff99ffffffffccaa99ffccaa99ffcca5ffccffffffffc3aaffaaffffffffc3a5ff99ffffff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 89, 91, 93, 95, 96, 97, 98, 99, 100, 101, 102, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, [])
]

def case_2_56 : Catalogue.Catalogue := #[
  (0x0, []),
  (0x80, [7]),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000, [73]),
  (0x80000000000000000002, [1, 79]),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000, [146]),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x0, []),
  (0x0, []),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x0, []),
  (0x0, []),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x0, []),
  (0x0, []),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x0, []),
  (0x0, []),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x0, []),
  (0x0, []),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x0, []),
  (0x0, []),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x0, []),
  (0x0, []),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0x0, []),
  (0x0, []),
  (0x100000000000000, [56]),
  (0x8000000000000001, [0, 63]),
  (0x0, []),
  (0x0, []),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x0, []),
  (0x0, []),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x0, []),
  (0x0, []),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x0, []),
  (0x0, []),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x0, []),
  (0x0, []),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x0, []),
  (0x0, []),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x0, []),
  (0x0, []),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x0, []),
  (0x0, []),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x100000000000000, [56]),
  (0x8000000000000001, [0, 63]),
  (0x0, []),
  (0x0, []),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x0, []),
  (0x0, []),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x0, []),
  (0x0, []),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x0, []),
  (0x0, []),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x0, []),
  (0x0, []),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x0, []),
  (0x0, []),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x0, []),
  (0x0, []),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x0, []),
  (0x0, []),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x100000000000000, [56]),
  (0x8100000000000001, [0, 56, 63]),
  (0x0, []),
  (0x0, []),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000001, [0, 56, 504]),
  (0x81000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008100000000000081, [0, 7, 56, 63, 448, 504, 511]),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000100000000000100, [8, 56, 121]),
  (0x82000000000002008300000000008303, [0, 1, 8, 9, 15, 56, 57, 63, 73, 121, 127]),
  (0x0, []),
  (0x0, []),
  (0x3000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000003010100000000000101, [0, 8, 56, 64, 72, 73, 120, 121, 456, 504, 505]),
  (0x83000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083838300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 63, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 504, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000100000000010000, [16, 56, 186]),
  (0x840000000004000000000000000000008500000000850005, [0, 2, 16, 18, 23, 56, 58, 63, 146, 186, 191]),
  (0x0, []),
  (0x0, []),
  (0x5000000000100000000000000000000000000000000000000000000000000000000000000000000050000000005000100000000000000000100000000010001, [0, 16, 56, 128, 144, 146, 184, 186, 464, 504, 506]),
  (0x85000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000008500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 63, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 504, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x800000000000000040000000400000002000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 121, 154, 186, 251]),
  (0x88000000080000008c0000008c0c00008a0000008a000a008f0000008f87878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 25, 26, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 121, 123, 127, 146, 147, 154, 155, 159, 186, 187, 191, 219, 251, 255]),
  (0x0, []),
  (0x0, []),
  (0xf000000070101010000000000000000000000000000000000000000000000000f0000000f040201050000000505010103000000030103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 88, 89, 120, 121, 128, 136, 144, 146, 152, 154, 184, 186, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 251, 448, 456, 464, 472, 473, 474, 504, 505, 506, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008f8f87878f0000008f878f878f0000008f87878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 25, 26, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 88, 89, 90, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 152, 153, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000100000100000000, [32, 56, 316]),
  (0x90000010000000000000000000000000000000000000000000000000000000009100009100000011, [0, 4, 32, 36, 39, 56, 60, 63, 292, 316, 319]),
  (0x0, []),
  (0x0, []),
  (0x11000001000000000000000000000000000000000000000011000011000000010000000000000000000000000000000000000000000000000100000100000001, [0, 32, 56, 256, 288, 292, 312, 316, 480, 504, 508]),
  (0x91000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000009100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 63, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 504, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x200000000000000010001000000000000000000000000000000000000000000002000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 121, 300, 316, 381]),
  (0xa000200000000000b000b0300000000000000000000000000000000000000000a200a20000002200b300b393000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 41, 44, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 121, 125, 127, 292, 293, 300, 301, 303, 316, 317, 319, 365, 381, 383]),
  (0x0, []),
  (0x0, []),
  (0x33001301000001010000000000000000330033100000020111001111000001010000000000000000000000000000000003000301000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 104, 105, 120, 121, 256, 264, 288, 292, 296, 300, 312, 316, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 381, 448, 456, 480, 488, 489, 492, 504, 505, 508, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b3b30000939300000000000000000000000000000000b300b3930000b393b300b393000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 41, 44, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 104, 105, 108, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 296, 297, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000010100000000000000000000000000000040400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 186, 308, 316, 446]),
  (0xc0400000000000000000000000000000d0d00050000000000000000000000000c4c40000004400000000000000000000d5d50095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 50, 52, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 186, 190, 191, 292, 294, 308, 310, 311, 316, 318, 319, 438, 446, 447]),
  (0x0, []),
  (0x0, []),
  (0x55150001000100015555001000040001000000000000000011110011000100010000000000000000050500010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 176, 178, 184, 186, 256, 272, 288, 292, 304, 308, 312, 316, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 446, 448, 464, 480, 496, 498, 500, 504, 506, 508, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d500d5009500950000000000000000d5d5009500d500950000000000000000d5d50095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 50, 52, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 176, 178, 180, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 304, 306, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffd7b79f9fb7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 25, 26, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 41, 42, 44, 45, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x0, []),
  (0x0, []),
  (0xff5533110f0503015555101004040101331033100201020111111111010101010f0402010f040201050501010505010103010301030103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 88, 89, 96, 104, 105, 112, 120, 121, 128, 136, 144, 146, 152, 154, 160, 168, 176, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 296, 300, 304, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff7f7ff9f97979fffccaa99ffccaa99ffdfb797dfff97b7ffd7bf97bf97ffd7ffd7b79f9fb7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 25, 26, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 41, 42, 44, 45, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 88, 89, 90, 91, 92, 93, 95, 96, 97, 98, 100, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113, 114, 116, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 158, 159, 160, 161, 162, 164, 167, 168, 169, 170, 172, 173, 175, 176, 177, 178, 179, 180, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 281, 282, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 300, 301, 302, 303, 304, 305, 306, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, [])
]

def case_4_448 : Catalogue.Catalogue := #[
  (0x0, []),
  (0x80, [7]),
  (0x100000000000000, [56]),
  (0x8000000000000001, [0, 63]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000, [73]),
  (0x80000000000000000002, [1, 79]),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000, [146]),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x810000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 448, 455]),
  (0x1000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 448, 504]),
  (0x81000000000000810000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 455, 504, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 448, 457]),
  (0x82830000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 448, 449, 455, 457, 463]),
  (0x3000000000003010000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 448, 456, 457, 504, 505]),
  (0x83000000000083830000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 455, 456, 457, 463, 504, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x400010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 448, 466]),
  (0x8400850000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 448, 450, 455, 466, 471]),
  (0x5000000000500010000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 448, 464, 466, 504, 506]),
  (0x85000000008500850000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 455, 464, 466, 471, 504, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80402010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 457, 466, 475]),
  (0x888c8a8f00000000000000000000000000000000000000000000000000000000088c8a8f00000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 193, 194, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 457, 459, 463, 466, 467, 471, 475, 479]),
  (0xf0000000f050301000000000000000000000000000000000000000000000000070000000f050301010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 200, 201, 208, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 457, 464, 466, 472, 473, 474, 475, 504, 505, 506, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8f8f8f8f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 193, 194, 195, 199, 200, 201, 202, 203, 207, 208, 209, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000010000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 448, 484]),
  (0x90000000910000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 448, 452, 455, 484, 487]),
  (0x11000011000000010000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 448, 480, 484, 504, 508]),
  (0x91000091000000910000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 455, 480, 484, 487, 504, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2010000002010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 457, 484, 493]),
  (0xa0b00000a2b30000000000000000000020b00000a2b3000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 321, 324, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 457, 461, 463, 484, 485, 487, 493, 495]),
  (0x33003311000003010000000000000000130033110000030101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 328, 329, 352, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 457, 480, 484, 488, 489, 492, 493, 504, 505, 508, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b30000b3b3b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 321, 324, 325, 327, 328, 329, 332, 333, 335, 352, 353, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x400010000400010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 466, 484, 502]),
  (0xc000d000c400d5004000d000c400d50000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 386, 388, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 466, 470, 471, 484, 486, 487, 502, 503]),
  (0x55550011000500011555001100050001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 400, 402, 416, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 466, 480, 484, 496, 498, 500, 502, 504, 506, 508, 510]),
  (0xd5d500d500d500d5d5d500d500d500d50000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 386, 388, 390, 391, 400, 402, 404, 406, 407, 416, 418, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00d70000a0f00000aab7000000f00000009f0000000088ccaa9f0000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 193, 194, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 321, 322, 324, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 386, 388, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101104050101331033110201030111101011010101010f0402010f050301050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 200, 201, 208, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 328, 329, 336, 345, 352, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 400, 402, 410, 416, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f7ccdfd7d7fff0fff7aab7bfb7fff0f0ff9997979fffccaa9fffdfbf9fffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 199, 200, 201, 202, 203, 204, 205, 207, 208, 209, 210, 211, 212, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 324, 325, 327, 328, 329, 330, 331, 332, 333, 335, 336, 337, 338, 340, 341, 343, 345, 347, 349, 351, 352, 353, 354, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 388, 390, 391, 392, 393, 394, 396, 398, 399, 400, 401, 402, 403, 404, 406, 407, 410, 411, 414, 415, 416, 417, 418, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, [])
]

def case_8_73 : Catalogue.Catalogue := #[
  (0x0, []),
  (0x80, [7]),
  (0x100000000000000, [56]),
  (0x8000000000000001, [0, 63]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000, [146]),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000, [73]),
  (0x80000000000000000002, [1, 79]),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000, [73]),
  (0x80000000000000000002, [1, 79]),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000, [73]),
  (0x82000000000000000002, [1, 73, 79]),
  (0x2000000000002000000000000000100, [8, 73, 121]),
  (0x82000000000082000200000000008303, [0, 1, 8, 9, 15, 57, 73, 79, 121, 127]),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002010000000000000000, [64, 73, 457]),
  (0x82020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000082830000000000000003, [0, 1, 64, 65, 71, 73, 79, 449, 457, 463]),
  (0x2000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 121, 456, 457, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x8000000000000000000000000000000000002000000000000000001, [0, 73, 219]),
  (0x8800000000000000000800000000000000008a00000000000000008f, [0, 1, 2, 3, 7, 73, 75, 79, 147, 219, 223]),
  (0x800000008000000000000000400000002000000020002000100000001010101, [0, 8, 16, 24, 56, 73, 89, 121, 154, 219, 251]),
  (0x8800000088000000080000008c0c00008a0000008a008a008f0000008b878f8f, [0, 1, 2, 3, 7, 8, 9, 10, 11, 15, 16, 17, 18, 23, 24, 25, 27, 31, 56, 57, 58, 59, 63, 73, 75, 79, 89, 91, 95, 121, 123, 127, 146, 147, 154, 155, 159, 187, 219, 223, 251, 255]),
  (0x80002010000000000000000000000000000000000000000000000000000000008040201000000000000000100000000000002010000000000000001, [0, 64, 73, 128, 192, 201, 210, 219, 448, 457, 475]),
  (0x88088a8f00000000000000000000000000000000000000000000000000000000888c8a8b00000000000c00870000000000008a8f000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 67, 71, 73, 75, 79, 128, 129, 130, 135, 146, 147, 192, 193, 195, 199, 201, 203, 207, 210, 211, 215, 219, 223, 448, 449, 450, 451, 455, 457, 459, 463, 467, 475, 479]),
  (0xb0000000f0103010000000000000000000000000000000000000000000000000f0000000f040301010000000405010103000000030103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 88, 89, 120, 121, 128, 136, 144, 146, 154, 184, 192, 200, 201, 210, 216, 217, 218, 219, 248, 249, 250, 251, 448, 456, 457, 464, 472, 473, 474, 475, 504, 505, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8b8b8f0000008c8f87878f0000008b878f8f8f0000008b878f8f, [0, 1, 2, 3, 7, 8, 9, 10, 11, 15, 16, 17, 18, 23, 24, 25, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 67, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 88, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 193, 195, 199, 200, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000002000000000000000001, [0, 73, 365]),
  (0xa00000000000000000200000000000000000000000000000000000000000000000000000a20000000000000000b3, [0, 1, 4, 5, 7, 73, 77, 79, 293, 365, 367]),
  (0x200020000000000000001000000000000000000000000000000000000000000002000200000002000100010100000101, [0, 8, 32, 40, 56, 73, 105, 121, 300, 365, 381]),
  (0xa000a000000000002000b0300000000000000000000000000000000000000000a200a2000000a200b300a3930000b3b3, [0, 1, 4, 5, 7, 8, 9, 12, 13, 15, 32, 33, 36, 39, 40, 41, 45, 47, 56, 57, 60, 61, 63, 73, 77, 79, 105, 109, 111, 121, 125, 127, 292, 293, 300, 301, 303, 317, 365, 367, 381, 383]),
  (0x2000000002010000000000000000000020100000020100000000000000010000000000000000000000000000000000000000000002010000000000000001, [0, 64, 73, 256, 320, 329, 356, 365, 448, 457, 493]),
  (0xa0200000a2b300000000000000000000a0b00000a2a3000000300000009300000000000000000000000000000000000000000000a2b300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 69, 71, 73, 77, 79, 256, 257, 260, 263, 292, 293, 320, 321, 325, 327, 329, 333, 335, 356, 357, 359, 365, 367, 448, 449, 452, 453, 455, 457, 461, 463, 485, 493, 495]),
  (0x23003301000003010000000000000000330033100000030101001011000001010000000000000000000000000000000003000301000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 104, 105, 120, 121, 256, 264, 288, 292, 300, 312, 320, 328, 329, 356, 360, 361, 364, 365, 376, 377, 380, 381, 448, 456, 457, 480, 488, 489, 492, 493, 504, 505, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a3a3b300b0b30000939300000000000000000000000000000000b300a3930000b3b3b300a3930000b3b3, [0, 1, 4, 5, 7, 8, 9, 12, 13, 15, 32, 33, 36, 39, 40, 41, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 69, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 104, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 321, 325, 327, 328, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000020000000000000000010000000000000000008000000000000000004000000000000000002000000000000000001, [0, 73, 146, 219, 292, 365, 511]),
  (0x800000000000000000800000000000000000a00000000000000000f00000000000000000880000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 219, 223, 292, 293, 294, 295, 365, 367, 439, 511]),
  (0x80000000000000004000000000000000200020000000000010101010000000000800000008000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 219, 251, 292, 300, 308, 316, 365, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3af9fbbb7ffff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 23, 24, 25, 27, 28, 29, 31, 32, 33, 34, 35, 36, 39, 40, 41, 42, 43, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010000001000040001000020100000020100000010000000010000000008040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 219, 256, 292, 320, 329, 356, 365, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaaf000000f00000009f0000000088ccaabb0000000000cc00b7000000000000aaff00000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 193, 195, 196, 197, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 321, 322, 323, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100301030111101011010101010f0403010f040301050401010405010103010301030103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 88, 89, 96, 104, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 200, 201, 210, 216, 217, 218, 219, 224, 232, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 328, 329, 336, 344, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aba7afaffff0f0ff9b979f9fffccab9bffccbbbbffcca797ccffb7b7ffc3af9fbbb7ffffffc3af9fbbb7ffff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 23, 24, 25, 27, 28, 29, 31, 32, 33, 34, 35, 36, 39, 40, 41, 42, 43, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 87, 88, 89, 91, 92, 93, 95, 96, 97, 98, 99, 100, 103, 104, 105, 106, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 141, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 169, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 195, 196, 197, 199, 200, 201, 203, 204, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 227, 228, 231, 232, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 267, 268, 271, 272, 273, 274, 276, 279, 280, 281, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 325, 327, 328, 329, 330, 331, 333, 335, 336, 337, 338, 341, 343, 344, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, [])
]

def case_9_79 : Catalogue.Catalogue := #[
  (0x0, []),
  (0x0, []),
  (0x100000000000000, [56]),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x0, []),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000, [146]),
  (0x0, []),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x0, []),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x0, []),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x0, []),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x0, []),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x0, []),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x0, []),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000, [79]),
  (0x0, []),
  (0x80000000000000000000000000000100, [8, 127]),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 463]),
  (0x0, []),
  (0x80000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000081010000000000000101, [0, 8, 64, 72, 79, 120, 456, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000004, [2, 223]),
  (0x0, []),
  (0x8000000000000000000000000400000000000000800000000400000001040401, [0, 10, 18, 24, 58, 95, 154, 255]),
  (0x0, []),
  (0x800000040000000000000000000000000000000000000000000000000000000000048001000000000000000400000000000000040000000000000001, [0, 66, 130, 192, 207, 210, 450, 479]),
  (0x0, []),
  (0x84000000850404010000000000000000000000000000000000000000000000008500000085048001040000000404050104000000800584010100000001010105, [0, 2, 8, 16, 24, 56, 64, 74, 79, 80, 82, 95, 122, 128, 136, 138, 146, 154, 186, 192, 207, 210, 216, 218, 223, 248, 250, 255, 448, 458, 466, 472, 474, 479, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010, [4, 367]),
  (0x0, []),
  (0x800000000000000000001000000000000000000000000000000000000000000000008000000000001000011000001001, [0, 12, 36, 40, 60, 111, 300, 383]),
  (0x0, []),
  (0x8000000000100000000000000000000000100000800100000000000000100000000000000000000000000000000000000000000000100000000000000001, [0, 68, 260, 320, 335, 356, 452, 495]),
  (0x0, []),
  (0x90009110000010010000000000000000910091100000800110001010000011010000000000000000000000000000000010008011000090010100010100000111, [0, 4, 8, 32, 40, 56, 64, 76, 79, 96, 100, 111, 124, 256, 264, 268, 292, 300, 316, 320, 335, 356, 360, 364, 367, 376, 380, 383, 448, 460, 484, 488, 492, 495, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000040000000000000000000000000000000000040000000000000000080000000000000000055, [0, 2, 4, 6, 79, 150, 294, 511]),
  (0x0, []),
  (0x80000000000000004000000000000000800000000000000050404010000000008000000000000000444000004004000080008000800080005540041510154115, [0, 2, 4, 8, 14, 16, 18, 20, 28, 32, 34, 36, 42, 54, 56, 58, 60, 62, 79, 95, 111, 127, 146, 158, 182, 186, 190, 255, 292, 302, 310, 316, 318, 383, 446, 511]),
  (0x0, []),
  (0x80408050804480550000004000400040000000400000800400000010000000150000000000408010000000000004001500000000000080410000000000000015, [0, 2, 4, 64, 70, 79, 128, 130, 132, 146, 196, 207, 214, 256, 258, 260, 292, 322, 335, 358, 390, 406, 422, 448, 450, 452, 454, 463, 466, 470, 479, 484, 486, 495, 502, 511]),
  (0x0, []),
  (0xd540c415d015c1154040501044044101c450c410800580011510105511140515d0448011d00480011504051404551115c14180058011c1151501011501151555, [0, 2, 4, 6, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 56, 58, 60, 64, 66, 68, 72, 78, 79, 80, 84, 95, 96, 98, 111, 112, 118, 120, 126, 127, 128, 130, 132, 136, 140, 144, 146, 148, 150, 154, 162, 164, 168, 170, 178, 184, 186, 188, 192, 207, 210, 220, 222, 223, 224, 228, 239, 242, 246, 252, 254, 255, 256, 258, 260, 264, 266, 274, 276, 280, 284, 288, 290, 292, 294, 300, 308, 312, 314, 316, 320, 335, 336, 338, 351, 356, 362, 366, 367, 372, 374, 378, 382, 383, 384, 392, 398, 402, 410, 414, 420, 428, 430, 438, 446, 448, 450, 452, 456, 462, 463, 464, 466, 468, 476, 478, 479, 480, 482, 484, 490, 494, 495, 502, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000, [79]),
  (0x0, []),
  (0x80000000000000000000000000000100, [8, 127]),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 463]),
  (0x0, []),
  (0x80000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000081010000000000000101, [0, 8, 64, 72, 79, 120, 456, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000004, [2, 223]),
  (0x0, []),
  (0x8000000000000000000000000400000000000000800000000400000001040401, [0, 10, 18, 24, 58, 95, 154, 255]),
  (0x0, []),
  (0x800000040000000000000000000000000000000000000000000000000000000000048001000000000000000400000000000000040000000000000001, [0, 66, 130, 192, 207, 210, 450, 479]),
  (0x0, []),
  (0x84000000850404010000000000000000000000000000000000000000000000008500000085048001040000000404050104000000800584010100000001010105, [0, 2, 8, 16, 24, 56, 64, 74, 79, 80, 82, 95, 122, 128, 136, 138, 146, 154, 186, 192, 207, 210, 216, 218, 223, 248, 250, 255, 448, 458, 466, 472, 474, 479, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010, [4, 367]),
  (0x0, []),
  (0x800000000000000000001000000000000000000000000000000000000000000000008000000000001000011000001001, [0, 12, 36, 40, 60, 111, 300, 383]),
  (0x0, []),
  (0x8000000000100000000000000000000000100000800100000000000000100000000000000000000000000000000000000000000000100000000000000001, [0, 68, 260, 320, 335, 356, 452, 495]),
  (0x0, []),
  (0x90009110000010010000000000000000910091100000800110001010000011010000000000000000000000000000000010008011000090010100010100000111, [0, 4, 8, 32, 40, 56, 64, 76, 79, 96, 100, 111, 124, 256, 264, 268, 292, 300, 316, 320, 335, 356, 360, 364, 367, 376, 380, 383, 448, 460, 484, 488, 492, 495, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000040000000000000000000000000000000000040000000000000000080000000000000000055, [0, 2, 4, 6, 79, 150, 294, 511]),
  (0x0, []),
  (0x80000000000000004000000000000000800000000000000050404010000000008000000000000000444000004004000080008000800080005540041510154115, [0, 2, 4, 8, 14, 16, 18, 20, 28, 32, 34, 36, 42, 54, 56, 58, 60, 62, 79, 95, 111, 127, 146, 158, 182, 186, 190, 255, 292, 302, 310, 316, 318, 383, 446, 511]),
  (0x0, []),
  (0x80408050804480550000004000400040000000400000800400000010000000150000000000408010000000000004001500000000000080410000000000000015, [0, 2, 4, 64, 70, 79, 128, 130, 132, 146, 196, 207, 214, 256, 258, 260, 292, 322, 335, 358, 390, 406, 422, 448, 450, 452, 454, 463, 466, 470, 479, 484, 486, 495, 502, 511]),
  (0x0, []),
  (0xd540c415d015c1154040501044044101c450c410800580011510105511140515d0448011d00480011504051404551115c14180058011c1151501011501151555, [0, 2, 4, 6, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 56, 58, 60, 64, 66, 68, 72, 78, 79, 80, 84, 95, 96, 98, 111, 112, 118, 120, 126, 127, 128, 130, 132, 136, 140, 144, 146, 148, 150, 154, 162, 164, 168, 170, 178, 184, 186, 188, 192, 207, 210, 220, 222, 223, 224, 228, 239, 242, 246, 252, 254, 255, 256, 258, 260, 264, 266, 274, 276, 280, 284, 288, 290, 292, 294, 300, 308, 312, 314, 316, 320, 335, 336, 338, 351, 356, 362, 366, 367, 372, 374, 378, 382, 383, 384, 392, 398, 402, 410, 414, 420, 428, 430, 438, 446, 448, 450, 452, 456, 462, 463, 464, 466, 468, 476, 478, 479, 480, 482, 484, 490, 494, 495, 502, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000, [79]),
  (0x0, []),
  (0x80000000000080000000000000000100, [8, 79, 127]),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080010000000000000000, [64, 79, 463]),
  (0x0, []),
  (0x80000000000081000000000000000000000000000000000000000000000000000000000000000000000000000000000081000000000081010000000000000101, [0, 8, 64, 72, 79, 120, 127, 456, 463, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000080000000000000000004, [2, 79, 223]),
  (0x0, []),
  (0x8000000080000000000000000400000080000000800080000400000001040505, [0, 2, 8, 10, 18, 24, 58, 79, 95, 127, 154, 223, 255]),
  (0x0, []),
  (0x800080040000000000000000000000000000000000000000000000000000000080048001000000000000000400000000000080050000000000000005, [0, 2, 64, 66, 79, 130, 192, 207, 210, 223, 450, 463, 479]),
  (0x0, []),
  (0x84000000850485050000000000000000000000000000000000000000000000008500000085048101040000000404050585000000810585050500000001050505, [0, 2, 8, 10, 16, 18, 24, 56, 58, 64, 66, 72, 74, 79, 80, 82, 88, 95, 120, 122, 127, 128, 130, 136, 138, 146, 154, 186, 192, 200, 207, 210, 216, 218, 223, 248, 250, 255, 448, 450, 456, 458, 463, 466, 472, 474, 479, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000080000000000000000010, [4, 79, 367]),
  (0x0, []),
  (0x800080000000000000001000000000000000000000000000000000000000000080008000000080001000011000001111, [0, 4, 8, 12, 36, 40, 60, 79, 111, 127, 300, 367, 383]),
  (0x0, []),
  (0x8000000080100000000000000000000080100000800100000000000000100000000000000000000000000000000000000000000080110000000000000011, [0, 4, 64, 68, 79, 260, 320, 335, 356, 367, 452, 463, 495]),
  (0x0, []),
  (0x90009110000091110000000000000000910091100000810110001010000011110000000000000000000000000000000091008111000091111100011100001111, [0, 4, 8, 12, 32, 36, 40, 56, 60, 64, 68, 72, 76, 79, 96, 100, 104, 111, 120, 124, 127, 256, 260, 264, 268, 292, 300, 316, 320, 328, 335, 356, 360, 364, 367, 376, 380, 383, 448, 452, 456, 460, 463, 484, 488, 492, 495, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000080000000000000000040000000000000000080000000000000000040000000000000000080000000000000000055, [0, 2, 4, 6, 79, 150, 223, 294, 367, 511]),
  (0x0, []),
  (0x80000000000000004000000000000000800080000000000050405050000000008000000080000000444000004444000080008000800080005540055511555555, [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 28, 32, 34, 36, 38, 40, 42, 54, 56, 58, 60, 62, 79, 95, 111, 127, 146, 150, 154, 158, 182, 186, 190, 223, 255, 292, 294, 300, 302, 310, 316, 318, 367, 383, 446, 511]),
  (0x0, []),
  (0x80408050804480550000004000400040000080500000800500000050000000550000000080448011000000000044005500000000000080550000000000000055, [0, 2, 4, 6, 64, 66, 68, 70, 79, 128, 130, 132, 134, 146, 150, 192, 196, 207, 210, 214, 223, 256, 258, 260, 262, 292, 294, 320, 322, 335, 356, 358, 367, 390, 406, 422, 448, 450, 452, 454, 463, 466, 470, 479, 484, 486, 495, 502, 511]),
  (0x0, []),
  (0xd540d555d555d5554040505044444141d550d550810585055550505511545555d5448111d54491115544055444555555d54185559155d5555541055511555555, [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 28, 32, 34, 36, 38, 40, 42, 48, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 79, 80, 82, 84, 86, 88, 92, 95, 96, 98, 100, 102, 104, 106, 111, 112, 118, 120, 122, 124, 126, 127, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 154, 158, 162, 164, 166, 168, 170, 178, 182, 184, 186, 188, 190, 192, 196, 200, 204, 207, 210, 214, 216, 218, 220, 222, 223, 224, 228, 232, 239, 242, 246, 248, 250, 252, 254, 255, 256, 258, 260, 262, 264, 266, 268, 270, 274, 276, 278, 280, 284, 288, 290, 292, 294, 300, 302, 308, 310, 312, 314, 316, 318, 320, 322, 328, 330, 335, 336, 338, 344, 351, 356, 358, 360, 362, 364, 366, 367, 372, 374, 376, 378, 380, 382, 383, 384, 390, 392, 398, 402, 406, 410, 414, 420, 422, 428, 430, 438, 446, 448, 450, 452, 454, 456, 458, 460, 462, 463, 464, 466, 468, 470, 472, 474, 476, 478, 479, 480, 482, 484, 486, 488, 490, 492, 494, 495, 502, 504, 506, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, [])
]

def case_16_146 : Catalogue.Catalogue := #[
  (0x0, []),
  (0x80, [7]),
  (0x100000000000000, [56]),
  (0x8000000000000001, [0, 63]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x2000000000000000000, [73]),
  (0x80000000000000000002, [1, 79]),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000, [146]),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000, [146]),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000, [146]),
  (0x84000000000000000000000000000000000004, [2, 146, 151]),
  (0x40000000004000000000000000000000000000000010000, [16, 146, 186]),
  (0x840000000084000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 151, 186, 191]),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000004000100000000000000000000000000000000, [128, 146, 466]),
  (0x8400040000000000000000000000000000000000000000000000000000000000000000000000000084008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 151, 450, 466, 471]),
  (0x4000000000500000000000000000000000000000000000000000000000000000000000000000000050000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 186, 464, 466, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x8000000000000000004000000000000000000000000000000000001, [0, 146, 219]),
  (0x8800000000000000008c00000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 146, 147, 151, 219, 223]),
  (0x800000008000000040000000404000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 146, 154, 186, 219, 251]),
  (0x88000000880000008c0000008c8c0000080000008a000a008f0000008d8f878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 19, 23, 24, 26, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 151, 154, 155, 159, 186, 187, 191, 219, 223, 251, 255]),
  (0x80400010000000000000000000000000000000000000000000000000000000008040201000000000004000100000000000000010000000000000001, [0, 64, 128, 146, 192, 201, 210, 219, 448, 466, 475]),
  (0x888c088f00000000000000000000000000000000000000000000000000000000888c8a8d00000000008c008f0000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 131, 135, 146, 147, 151, 192, 194, 195, 199, 201, 203, 207, 210, 211, 215, 219, 223, 448, 449, 450, 451, 455, 459, 466, 467, 471, 475, 479]),
  (0xd0000000f0501010000000000000000000000000000000000000000000000000f0000000f050201050000000505010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 152, 154, 184, 186, 192, 201, 208, 210, 216, 217, 218, 219, 248, 249, 250, 251, 448, 456, 464, 466, 472, 473, 474, 475, 504, 506, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8d8a8d8f0000008d8f878f8f0000008a878f878f0000008d8f878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 19, 23, 24, 26, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 131, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 152, 154, 155, 159, 184, 185, 186, 187, 191, 192, 194, 195, 199, 201, 203, 207, 208, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000001, [0, 146, 438]),
  (0xc00000000000000000000000000000000000400000000000000000000000000000000000c40000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 146, 150, 151, 294, 438, 439]),
  (0x4040000000000000000000000000000000100000000000000000000000000000040400000004000000000000000000000101000100010001, [0, 16, 32, 48, 56, 146, 178, 186, 308, 438, 446]),
  (0xc0c0000000000000000000000000000040d00050000000000000000000000000c4c4000000c400000000000000000000d5c5009500d500d5, [0, 2, 4, 6, 7, 16, 18, 20, 22, 23, 32, 34, 36, 39, 48, 50, 54, 55, 56, 58, 60, 62, 63, 146, 150, 151, 178, 182, 183, 186, 190, 191, 292, 294, 308, 310, 311, 318, 438, 439, 446, 447]),
  (0x400000000400010040001000040001000000000000000000000000000000010000000000000000000000000004000100000000000000000000000000000001, [0, 128, 146, 256, 384, 402, 420, 438, 448, 466, 502]),
  (0xc0004000c400d500c000d000c400c50000000000000000000000500000009500000000000000000000000000c400d5000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 134, 135, 146, 150, 151, 256, 258, 260, 263, 292, 294, 384, 386, 390, 391, 402, 406, 407, 420, 422, 423, 438, 439, 448, 450, 452, 454, 455, 466, 470, 471, 486, 502, 503]),
  (0x45550001000500015555001000050001000000000000000001100011000100010000000000000000050500010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 176, 178, 184, 186, 256, 272, 288, 292, 308, 312, 384, 400, 402, 420, 432, 434, 436, 438, 440, 442, 444, 446, 448, 464, 466, 480, 496, 498, 500, 502, 504, 506, 510]),
  (0xd5d500d500d500d5d5d500d000c500c50000000000000000d5d000d5009500950000000000000000d5c5009500d500d50000000000000000d5c5009500d500d5, [0, 2, 4, 6, 7, 16, 18, 20, 22, 23, 32, 34, 36, 39, 48, 50, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 134, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 176, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 386, 390, 391, 400, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x80000000000000000040000000000000000000000000000000000010000000000000000008000000000000000004000000000000000002000000000000000001, [0, 73, 146, 219, 292, 438, 511]),
  (0x800000000000000000c00000000000000000800000000000000000f00000000000000000880000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 219, 223, 292, 293, 294, 295, 367, 438, 439, 511]),
  (0x80000000000000004040000000000000200000000000000010101010000000000800000008000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 219, 251, 292, 300, 308, 316, 381, 438, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffcfa59fddffd7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010040001000040001000000100000020100000010000000010000000008040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 219, 256, 292, 320, 329, 356, 384, 402, 420, 438, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00cf0000a0f00000aaa5000000f00000009f0000000088ccaadd0000000000cc00ff000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 131, 132, 133, 134, 135, 146, 147, 150, 151, 192, 194, 195, 196, 198, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 386, 387, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101005050101331033100201020111101011010101010f0502010f050201050501010505010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 152, 154, 160, 168, 176, 178, 184, 186, 192, 201, 208, 210, 216, 217, 218, 219, 224, 233, 240, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 400, 402, 408, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0cdcfc7cffff0fff0aaa5aaa5fff0f0ff9d9f979fffcdaa9dffddaaddffcfa59fddffd7ffffc7aa97aad7ffd7ffcfa59fddffd7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 86, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 114, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 154, 155, 156, 158, 159, 160, 161, 162, 163, 164, 167, 168, 170, 173, 175, 176, 177, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 198, 199, 201, 203, 205, 207, 208, 210, 211, 212, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 226, 227, 228, 231, 233, 235, 237, 239, 240, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 275, 276, 279, 280, 282, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 390, 391, 392, 393, 394, 398, 399, 400, 401, 402, 403, 406, 407, 408, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, [])
]

def case_18_186 : Catalogue.Catalogue := #[
  (0x0, []),
  (0x80, [7]),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000, [73]),
  (0x80000000000000000002, [1, 79]),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x0, []),
  (0x0, []),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x0, []),
  (0x0, []),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000, [186]),
  (0x800000000000000000000000000000000000000000000004, [2, 191]),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 506]),
  (0x80000000000000040000000000000000000000000000000000000000000000000000000000000000040000000000008500000000000000000000000000000005, [0, 2, 128, 130, 135, 186, 450, 511]),
  (0x0, []),
  (0x0, []),
  (0x800000000000000000000000000000000000000000000000000000000000100, [8, 251]),
  (0x8000000000000000080000000000000000000000000008000000000000008609, [0, 3, 9, 10, 15, 75, 187, 255]),
  (0x0, []),
  (0x0, []),
  (0x8000000000001000000000000000000000000000000000000000000000000000400000000000201000000000000010000000000000001000000000000000001, [0, 72, 136, 192, 201, 250, 456, 507]),
  (0x8800000000008e090000000000000000000000000000000000000000000000008c00000000008a890c000000000086030000000000008e05000000000000018f, [0, 1, 2, 3, 7, 8, 64, 66, 73, 74, 75, 79, 128, 129, 137, 138, 143, 186, 187, 192, 195, 199, 201, 203, 207, 250, 251, 255, 448, 451, 457, 458, 459, 463, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 446]),
  (0x8000000000000000000000000000000000000040000000000000000000000000400000000000000000000000000000000000009400000041, [0, 6, 34, 36, 39, 190, 294, 447]),
  (0x0, []),
  (0x0, []),
  (0x40000001000000000400001000000001000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000001, [0, 160, 288, 384, 420, 442, 480, 510]),
  (0xc00000d400000041c40000d0000000c10000000000000000000000d40000000500000000000000004400009400000011000000000000000000000001000000d5, [0, 2, 4, 6, 7, 32, 128, 132, 162, 164, 167, 186, 190, 256, 258, 290, 292, 294, 295, 384, 390, 391, 420, 422, 423, 442, 446, 447, 448, 454, 482, 484, 486, 487, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000001000000000000000000000000000040000000000000000000200000000000000010100000101, [0, 8, 32, 40, 105, 186, 300, 511]),
  (0x8000000000000000800000000000000000008000000000000000e090000000008000000000000000cc000000000000000000a800000082000000a49b0000d397, [0, 1, 2, 4, 7, 8, 9, 12, 14, 15, 32, 33, 35, 36, 39, 42, 45, 47, 73, 79, 107, 109, 111, 186, 187, 190, 191, 255, 292, 295, 301, 302, 303, 367, 447, 511]),
  (0x0, []),
  (0x0, []),
  (0xcc003311000003010400100000000100000013000000000000000011000001010400020100000000040001000000000100000001000003010000000100000101, [0, 8, 32, 64, 72, 73, 96, 128, 168, 186, 224, 233, 250, 256, 264, 288, 292, 360, 361, 364, 392, 428, 442, 448, 456, 457, 480, 484, 488, 489, 492, 493, 506, 507, 510, 511]),
  (0xcc00ec9b0000d397cc00e0300000c2030000ec5000000a05000010fb0000979dcc00a89800002211cc00a403000011b7000002970000fbc700000197000097ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 32, 33, 34, 36, 39, 40, 64, 65, 66, 70, 71, 72, 73, 75, 76, 77, 78, 79, 96, 97, 98, 100, 103, 105, 128, 129, 130, 132, 133, 135, 136, 140, 160, 161, 170, 173, 175, 186, 187, 190, 191, 192, 196, 201, 205, 227, 228, 231, 235, 237, 239, 250, 251, 254, 255, 256, 258, 259, 260, 263, 264, 265, 266, 268, 271, 288, 289, 291, 292, 293, 294, 295, 300, 320, 322, 329, 331, 356, 358, 362, 363, 365, 366, 367, 384, 385, 393, 398, 399, 420, 421, 429, 430, 431, 442, 443, 446, 447, 448, 449, 450, 452, 455, 456, 457, 460, 462, 463, 480, 481, 483, 484, 487, 490, 491, 493, 494, 495, 506, 507, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000, [186]),
  (0x800000000000000000000000000000000000000000000004, [2, 191]),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 506]),
  (0x80000000000000040000000000000000000000000000000000000000000000000000000000000000040000000000008500000000000000000000000000000005, [0, 2, 128, 130, 135, 186, 450, 511]),
  (0x0, []),
  (0x0, []),
  (0x800000000000000000000000000000000000000000000000000000000000100, [8, 251]),
  (0x8000000000000000080000000000000000000000000008000000000000008609, [0, 3, 9, 10, 15, 75, 187, 255]),
  (0x0, []),
  (0x0, []),
  (0x8000000000001000000000000000000000000000000000000000000000000000400000000000201000000000000010000000000000001000000000000000001, [0, 72, 136, 192, 201, 250, 456, 507]),
  (0x8800000000008e090000000000000000000000000000000000000000000000008c00000000008a890c000000000086030000000000008e05000000000000018f, [0, 1, 2, 3, 7, 8, 64, 66, 73, 74, 75, 79, 128, 129, 137, 138, 143, 186, 187, 192, 195, 199, 201, 203, 207, 250, 251, 255, 448, 451, 457, 458, 459, 463, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 446]),
  (0x8000000000000000000000000000000000000040000000000000000000000000400000000000000000000000000000000000009400000041, [0, 6, 34, 36, 39, 190, 294, 447]),
  (0x0, []),
  (0x0, []),
  (0x40000001000000000400001000000001000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000001, [0, 160, 288, 384, 420, 442, 480, 510]),
  (0xc00000d400000041c40000d0000000c10000000000000000000000d40000000500000000000000004400009400000011000000000000000000000001000000d5, [0, 2, 4, 6, 7, 32, 128, 132, 162, 164, 167, 186, 190, 256, 258, 290, 292, 294, 295, 384, 390, 391, 420, 422, 423, 442, 446, 447, 448, 454, 482, 484, 486, 487, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x80000000000000000000000000000000000000000000000000001000000000000000000000000000040000000000000000000200000000000000010100000101, [0, 8, 32, 40, 105, 186, 300, 511]),
  (0x8000000000000000800000000000000000008000000000000000e090000000008000000000000000cc000000000000000000a800000082000000a49b0000d397, [0, 1, 2, 4, 7, 8, 9, 12, 14, 15, 32, 33, 35, 36, 39, 42, 45, 47, 73, 79, 107, 109, 111, 186, 187, 190, 191, 255, 292, 295, 301, 302, 303, 367, 447, 511]),
  (0x0, []),
  (0x0, []),
  (0xcc003311000003010400100000000100000013000000000000000011000001010400020100000000040001000000000100000001000003010000000100000101, [0, 8, 32, 64, 72, 73, 96, 128, 168, 186, 224, 233, 250, 256, 264, 288, 292, 360, 361, 364, 392, 428, 442, 448, 456, 457, 480, 484, 488, 489, 492, 493, 506, 507, 510, 511]),
  (0xcc00ec9b0000d397cc00e0300000c2030000ec5000000a05000010fb0000979dcc00a89800002211cc00a403000011b7000002970000fbc700000197000097ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 32, 33, 34, 36, 39, 40, 64, 65, 66, 70, 71, 72, 73, 75, 76, 77, 78, 79, 96, 97, 98, 100, 103, 105, 128, 129, 130, 132, 133, 135, 136, 140, 160, 161, 170, 173, 175, 186, 187, 190, 191, 192, 196, 201, 205, 227, 228, 231, 235, 237, 239, 250, 251, 254, 255, 256, 258, 259, 260, 263, 264, 265, 266, 268, 271, 288, 289, 291, 292, 293, 294, 295, 300, 320, 322, 329, 331, 356, 358, 362, 363, 365, 366, 367, 384, 385, 393, 398, 399, 420, 421, 429, 430, 431, 442, 443, 446, 447, 448, 449, 450, 452, 455, 456, 457, 460, 462, 463, 480, 481, 483, 484, 487, 490, 491, 493, 494, 495, 506, 507, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x40000000000000000000000000000000000000000000000, [186]),
  (0x840000000000000000000000000000000000000000000004, [2, 186, 191]),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000100000000000000000000000000000000, [128, 186, 506]),
  (0x84000000000000040000000000000000000000000000000000000000000000000000000000000000840000000000008500000000000000000000000000000005, [0, 2, 128, 130, 135, 186, 191, 450, 506, 511]),
  (0x0, []),
  (0x0, []),
  (0x800000000000000040000000000000000000000000000000000000000000100, [8, 186, 251]),
  (0x88000000000000008c000000000000000000000000000800000000000000870d, [0, 2, 3, 8, 9, 10, 15, 75, 186, 187, 191, 251, 255]),
  (0x0, []),
  (0x0, []),
  (0xc000000000001000000000000000000000000000000000000000000000000000c00000000000201040000000000010100000000000001000000000000000101, [0, 8, 72, 128, 136, 186, 192, 201, 250, 251, 456, 506, 507]),
  (0x8c00000000008f0d0000000000000000000000000000000000000000000000008c00000000008a8d8c0000000000878f0000000000008f05000000000000878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 64, 66, 72, 73, 74, 75, 79, 128, 129, 130, 131, 135, 136, 137, 138, 143, 186, 187, 191, 192, 194, 195, 199, 201, 203, 207, 250, 251, 255, 448, 450, 451, 456, 457, 458, 459, 463, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000100000000, [32, 186, 446]),
  (0xc000000000000000000000000000000000000040000000000000000000000000c40000000000000000000000000000000000009500000045, [0, 2, 6, 32, 34, 36, 39, 186, 190, 191, 294, 446, 447]),
  (0x0, []),
  (0x0, []),
  (0x44000001000000004400001000000001000000000000000000000001000000000000000000000000040000010000000100000000000000000000000100000001, [0, 32, 128, 160, 186, 288, 384, 420, 442, 446, 480, 506, 510]),
  (0xc40000d500000045c40000d0000000c50000000000000000000000d5000000050000000000000000c4000095000000d5000000000000000000000095000000d5, [0, 2, 4, 6, 7, 32, 34, 36, 39, 128, 130, 132, 134, 135, 160, 162, 164, 167, 186, 190, 191, 256, 258, 288, 290, 292, 294, 295, 384, 386, 390, 391, 420, 422, 423, 442, 446, 447, 448, 450, 454, 480, 482, 484, 486, 487, 506, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x80000000000000004000000000000000000000000000000000001000000000000800000000000000040000000000000000000200000000000000010100000101, [0, 8, 32, 40, 105, 186, 251, 300, 446, 511]),
  (0x8000000000000000c00000000000000000008000000000000000f0d0000000008800000000000000cc000000000000000000aa0000008a000000b79f0000d7df, [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 14, 15, 32, 33, 34, 35, 36, 39, 40, 41, 42, 44, 45, 47, 73, 75, 79, 105, 107, 109, 111, 186, 187, 190, 191, 251, 255, 292, 294, 295, 300, 301, 302, 303, 367, 446, 447, 511]),
  (0x0, []),
  (0x0, []),
  (0xcc003311000003014400101000000101000013000000000000001111000001010c00020100000201040001010000010100000301000003010000010100000101, [0, 8, 32, 40, 64, 72, 73, 96, 104, 105, 128, 136, 160, 168, 186, 192, 201, 224, 233, 250, 251, 256, 264, 288, 292, 296, 300, 360, 361, 364, 384, 392, 420, 428, 442, 446, 448, 456, 457, 480, 484, 488, 489, 492, 493, 506, 507, 510, 511]),
  (0xcc00ffdf0000dfdfcc00f0f00000c7cf0000ff5000000a050000f7ff0000979dcc00aa9d0000aaddcc00b79f0000d7ff0000bf970000ffc70000b79f0000d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 32, 33, 34, 35, 36, 39, 40, 41, 42, 44, 45, 47, 64, 65, 66, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 96, 97, 98, 100, 103, 104, 105, 106, 107, 108, 109, 111, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 140, 142, 143, 160, 161, 162, 163, 164, 167, 168, 169, 170, 172, 173, 175, 186, 187, 190, 191, 192, 194, 195, 196, 198, 199, 201, 203, 205, 207, 224, 226, 227, 228, 231, 233, 235, 237, 239, 250, 251, 254, 255, 256, 258, 259, 260, 263, 264, 265, 266, 268, 271, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 300, 301, 302, 303, 320, 322, 329, 331, 356, 358, 360, 361, 362, 363, 364, 365, 366, 367, 384, 385, 386, 387, 390, 391, 392, 393, 394, 398, 399, 420, 421, 422, 423, 428, 429, 430, 431, 442, 443, 446, 447, 448, 449, 450, 451, 452, 454, 455, 456, 457, 458, 459, 460, 462, 463, 480, 481, 482, 483, 484, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 506, 507, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, [])
]

def case_32_292 : Catalogue.Catalogue := #[
  (0x0, []),
  (0x80, [7]),
  (0x100000000000000, [56]),
  (0x8000000000000001, [0, 63]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [448]),
  (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 455]),
  (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 504]),
  (0x80000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000081, [0, 7, 56, 448, 511]),
  (0x2000000000000000000, [73]),
  (0x80000000000000000002, [1, 79]),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 457]),
  (0x80020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002830000000000000003, [0, 1, 64, 65, 71, 73, 449, 463]),
  (0x2000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000003010000000000000101, [0, 8, 64, 72, 73, 120, 456, 505]),
  (0x82000000000083030000000000000000000000000000000000000000000000000000000000000000000000000000000083000000000083830300000000008383, [0, 1, 7, 8, 9, 15, 56, 57, 64, 65, 71, 72, 73, 79, 120, 121, 127, 448, 449, 456, 457, 463, 505, 511]),
  (0x4000000000000000000000000000000000000, [146]),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 466]),
  (0x8000040000000000000000000000000000000000000000000000000000000000000000000000000004008500000000000000000000000000000005, [0, 2, 128, 130, 135, 146, 450, 471]),
  (0x4000000000100000000000000000000000000000000000000000000000000000000000000000000010000000005000100000000000000000000000000010001, [0, 16, 128, 144, 146, 184, 464, 506]),
  (0x84000000008500050000000000000000000000000000000000000000000000000000000000000000850000000085008500000000000000000500000000850085, [0, 2, 7, 16, 18, 23, 56, 58, 128, 130, 135, 144, 146, 151, 184, 186, 191, 448, 450, 464, 466, 471, 506, 511]),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x80000010000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 448, 475]),
  (0x8008088f00000000000000000000000000000000000000000000000000000000088c8a8900000000000c00870000000000000a87000000000000008f, [0, 1, 2, 3, 7, 64, 65, 66, 71, 73, 75, 128, 129, 130, 135, 146, 147, 192, 195, 199, 201, 203, 207, 210, 211, 215, 219, 448, 449, 450, 451, 455, 459, 467, 479]),
  (0x900000007010101000000000000000000000000000000000000000000000000070000000f040201010000000405010101000000020103010100000001010101, [0, 8, 16, 24, 56, 64, 72, 73, 80, 89, 120, 128, 136, 144, 146, 154, 184, 192, 201, 210, 216, 217, 218, 219, 248, 249, 250, 448, 456, 464, 472, 473, 474, 504, 507]),
  (0x8f0000008f8f8f8f0000000000000000000000000000000000000000000000008f0000008f8c8a898f0000008c8f87878f0000008a878f878f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 64, 65, 66, 71, 72, 73, 74, 75, 79, 80, 81, 82, 87, 89, 91, 95, 120, 121, 122, 123, 127, 128, 129, 130, 135, 136, 137, 138, 143, 144, 145, 146, 147, 151, 154, 155, 159, 184, 185, 186, 187, 191, 192, 195, 199, 201, 203, 207, 210, 211, 215, 216, 217, 218, 219, 223, 248, 249, 250, 251, 255, 448, 449, 450, 451, 455, 456, 457, 458, 459, 463, 464, 465, 466, 467, 471, 472, 473, 474, 475, 479, 504, 505, 506, 507, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000010, [4, 295]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 316]),
  (0x80000010000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 319]),
  (0x10000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000, [256, 484]),
  (0x80000000100000000000000000000000000000000000000010000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 452, 487]),
  (0x10000001000000000000000000000000000000000000000001000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 480, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 365]),
  (0x800000000000000000200000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 293, 367]),
  (0x200000000000000000001000000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 300, 381]),
  (0x80002000000000002000b03000000000000000000000000000000000000000002000a20000002200b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 300, 301, 303, 317, 365, 383]),
  (0x2000000000010000000000000000000000100000020100000000000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 320, 329, 356, 448, 493]),
  (0x8020000020b30000000000000000000020b00000a2a1000000300000009300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 263, 292, 293, 320, 325, 327, 329, 333, 335, 356, 357, 359, 365, 448, 449, 452, 453, 455, 461, 485, 495]),
  (0x21001301000001010000000000000000130033100000020101001011000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 300, 312, 320, 329, 356, 360, 361, 364, 365, 376, 377, 380, 448, 456, 480, 488, 489, 492, 504, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b00000a2a1b300b0b30000939300000000000000000000000000000000b300a2930000b393b300a193000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 39, 40, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 300, 301, 303, 312, 313, 316, 317, 319, 320, 325, 327, 329, 333, 335, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001, [0, 438]),
  (0x800000000000000000000000000000000000400000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 294, 439]),
  (0x4000000000000000000000000000000000100000000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 308, 446]),
  (0x8040000000000000000000000000000040d0005000000000000000000000000040c40000004400000000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 308, 310, 311, 318, 438, 447]),
  (0x400000000000010000001000040001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 384, 402, 420, 448, 502]),
  (0x800040004000d5004000d000c400c10000000000000000000000500000009500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 263, 292, 294, 384, 390, 391, 402, 406, 407, 420, 422, 423, 438, 448, 450, 452, 454, 455, 470, 486, 503]),
  (0x41150001000100011555001000040001000000000000000001100011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 308, 312, 384, 402, 420, 432, 434, 436, 438, 440, 442, 444, 448, 464, 480, 496, 498, 500, 504, 510]),
  (0xd5d500d500d500d5d5d500d000c400c10000000000000000d5d000d5009500950000000000000000d5c4009500d500950000000000000000d5c10095009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 39, 48, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 308, 310, 311, 312, 314, 316, 318, 319, 384, 390, 391, 402, 406, 407, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x80000000000000000000000000000000000000000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 511]),
  (0x800000000000000000800000000000000000800000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 367, 439, 511]),
  (0x80000000000000004000000000000000200000000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 381, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010000001000040001000000100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 384, 402, 420, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00c30000a0f00000aaa5000000f00000009f0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 263, 292, 293, 294, 295, 320, 322, 325, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555101004040101331033100201020111101011010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 300, 308, 312, 316, 320, 329, 336, 345, 356, 360, 361, 364, 365, 372, 376, 377, 380, 381, 384, 392, 402, 410, 420, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff0f0ccccc3c3fff0fff0aaa5aaa5fff0f0ff9997979fffccaa99ffccaa99ffcca597ccff97b7ffc3aa97aa97ffd7ffc3a59f99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 39, 40, 42, 45, 47, 48, 49, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 103, 105, 107, 109, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 167, 168, 170, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 263, 264, 265, 266, 268, 271, 272, 273, 274, 276, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 325, 327, 329, 331, 333, 335, 336, 338, 341, 343, 345, 347, 349, 351, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 390, 391, 392, 393, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 420, 421, 422, 423, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000, [292]),
  (0x90000000000000000000000000000000000000000000000000000000000000000000000010, [4, 292, 295]),
  (0x10000010000000000000000000000000000000000000000000000000000000000000000100000000, [32, 292, 316]),
  (0x90000090000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 292, 295, 316, 319]),
  (0x10000000000000000000000000000000000000000000000010000000010000000000000000000000000000000000000000000000000000000000000000, [256, 292, 484]),
  (0x90000000100000000000000000000000000000000000000090000000910000000000000000000000000000000000000000000000000000000000000011, [0, 4, 256, 260, 263, 292, 295, 452, 484, 487]),
  (0x10000011000000000000000000000000000000000000000011000011000000010000000000000000000000000000000000000000000000000000000100000001, [0, 32, 256, 288, 292, 312, 316, 480, 484, 508]),
  (0x90000091000000110000000000000000000000000000000091000091000000910000000000000000000000000000000000000000000000001100009100000091, [0, 4, 7, 32, 36, 39, 56, 60, 256, 260, 263, 288, 292, 295, 312, 316, 319, 448, 452, 480, 484, 487, 508, 511]),
  (0x20000000000000000010000000000000000000000000000000000000000000000000000000000000000000000001, [0, 292, 365]),
  (0xa00000000000000000b00000000000000000000000000000000000000000000000000000200000000000000000b3, [0, 1, 4, 5, 7, 77, 292, 293, 295, 365, 367]),
  (0x200020000000000010001010000000000000000000000000000000000000000000000200000000000100010100000101, [0, 8, 32, 40, 56, 105, 292, 300, 316, 365, 381]),
  (0xa000a00000000000b000b0b000000000000000000000000000000000000000002000a20000002200b300b1b3000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 37, 39, 40, 44, 45, 47, 56, 57, 60, 61, 63, 73, 77, 105, 109, 111, 125, 292, 293, 295, 300, 301, 303, 316, 317, 319, 365, 367, 381, 383]),
  (0x2010000000010000000000000000000020100000020100000010000000010000000000000000000000000000000000000000000000010000000000000001, [0, 64, 256, 292, 320, 329, 356, 365, 448, 484, 493]),
  (0xa0b0000020b300000000000000000000a0b00000a2b1000000b0000000b300000000000000000000000000000000000000000000229300000000000000b3, [0, 1, 4, 5, 7, 64, 65, 68, 71, 73, 77, 256, 257, 260, 261, 263, 292, 293, 295, 320, 324, 325, 327, 329, 333, 335, 356, 357, 359, 365, 367, 448, 449, 452, 453, 455, 461, 484, 485, 487, 493, 495]),
  (0x31003311000001010000000000000000330033110000020111001111000001010000000000000000000000000000000001000201000003010100010100000101, [0, 8, 32, 40, 56, 64, 72, 73, 96, 105, 120, 256, 264, 288, 292, 296, 300, 312, 316, 320, 329, 352, 356, 360, 361, 364, 365, 376, 377, 380, 381, 448, 456, 480, 484, 488, 489, 492, 493, 504, 508, 509]),
  (0xb300b3b30000b3b30000000000000000b300b3b10000a2b1b300b1b3000093b300000000000000000000000000000000b300a2930000b393b300b1b3000093b3, [0, 1, 4, 5, 7, 8, 9, 12, 15, 32, 33, 36, 37, 39, 40, 44, 45, 47, 56, 57, 60, 61, 63, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 256, 257, 260, 261, 263, 264, 265, 268, 271, 288, 289, 292, 293, 295, 296, 300, 301, 303, 312, 313, 316, 317, 319, 320, 324, 325, 327, 329, 333, 335, 352, 356, 357, 359, 360, 361, 364, 365, 367, 376, 377, 380, 381, 383, 448, 449, 452, 453, 455, 456, 457, 460, 461, 463, 480, 481, 484, 485, 487, 488, 489, 492, 493, 495, 504, 505, 508, 509, 511]),
  (0x40000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000001, [0, 292, 438]),
  (0xc00000000000000000000000000000000000d00000000000000000000000000000000000400000000000000000000000000000000000d5, [0, 2, 4, 6, 7, 150, 292, 294, 295, 438, 439]),
  (0x4040000000000000000000000000000010100010000000000000000000000000000400000000000000000000000000000101000100010001, [0, 16, 32, 48, 56, 178, 292, 308, 316, 438, 446]),
  (0xc0c00000000000000000000000000000d0d000d000000000000000000000000040c40000004400000000000000000000d5d100d5009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 38, 39, 48, 52, 54, 55, 56, 58, 60, 62, 63, 146, 150, 178, 182, 183, 190, 292, 294, 295, 308, 310, 311, 316, 318, 319, 438, 439, 446, 447]),
  (0x400010000000010040001000040001000000000000000000000010000000010000000000000000000000000000000100000000000000000000000000000001, [0, 128, 256, 292, 384, 402, 420, 438, 448, 484, 502]),
  (0xc000d0004000d500c000d000c400d10000000000000000000000d0000000d500000000000000000000000000440095000000000000000000000000000000d5, [0, 2, 4, 6, 7, 128, 130, 132, 135, 146, 150, 256, 258, 260, 262, 263, 292, 294, 295, 384, 388, 390, 391, 402, 406, 407, 420, 422, 423, 438, 439, 448, 450, 452, 454, 455, 470, 484, 486, 487, 502, 503]),
  (0x51550011000100015555001100040001000000000000000011110011000100010000000000000000010400010005000100000000000000000101000100010001, [0, 16, 32, 48, 56, 128, 144, 146, 160, 178, 184, 256, 272, 288, 292, 304, 308, 312, 316, 384, 402, 416, 420, 432, 434, 436, 438, 440, 442, 444, 446, 448, 464, 480, 484, 496, 498, 500, 502, 504, 508, 510]),
  (0xd5d500d500d500d5d5d500d100c400d10000000000000000d5d100d5009500d50000000000000000d5c4009500d500950000000000000000d5d100d5009500d5, [0, 2, 4, 6, 7, 16, 18, 20, 23, 32, 34, 36, 38, 39, 48, 52, 54, 55, 56, 58, 60, 62, 63, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 256, 258, 260, 262, 263, 272, 274, 276, 279, 288, 290, 292, 294, 295, 304, 308, 310, 311, 312, 314, 316, 318, 319, 384, 388, 390, 391, 402, 406, 407, 416, 420, 422, 423, 432, 434, 436, 438, 439, 440, 442, 444, 446, 447, 448, 450, 452, 454, 455, 464, 466, 468, 470, 471, 480, 482, 484, 486, 487, 496, 498, 500, 502, 503, 504, 506, 508, 510, 511]),
  (0x80000000000000000040000000000000000020000000000000000010000000000000000000000000000000000004000000000000000002000000000000000001, [0, 73, 146, 292, 365, 438, 511]),
  (0x800000000000000000c00000000000000000a00000000000000000f00000000000000000800000000000000000cc0000000000000000aa0000000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 73, 75, 77, 79, 146, 147, 150, 151, 223, 292, 293, 294, 295, 365, 367, 438, 439, 511]),
  (0x80000000000000004040000000000000200020000000000010101010000000000800000000000000040400000404000002000200020002000101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 73, 89, 105, 121, 146, 154, 178, 186, 251, 292, 300, 308, 316, 365, 381, 438, 446, 511]),
  (0x8000000000000000c0c0000000000000a000a00000000000f0f0f0f0000000008800000088000000cccc0000cccc0000aa00aa00aa00aa00fff3f5ff99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 44, 45, 46, 47, 48, 49, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 73, 75, 77, 79, 89, 91, 93, 95, 105, 107, 109, 111, 121, 123, 125, 127, 146, 147, 150, 151, 154, 155, 158, 159, 178, 179, 182, 183, 186, 187, 190, 191, 219, 223, 251, 255, 292, 293, 294, 295, 300, 301, 302, 303, 308, 309, 310, 311, 316, 317, 318, 319, 365, 367, 381, 383, 438, 439, 446, 447, 511]),
  (0x80402010080402010040001000040001000020100000020100000010000000010000000000040201000000000004000100000000000002010000000000000001, [0, 64, 73, 128, 146, 192, 201, 210, 256, 292, 320, 329, 356, 365, 384, 402, 420, 438, 448, 457, 466, 475, 484, 493, 502, 511]),
  (0x80c0a0f088ccaaff00c000f000cc00f30000a0f00000aaf5000000f0000000ff0000000088ccaa990000000000cc00b7000000000000aad700000000000000ff, [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 75, 77, 79, 128, 129, 130, 132, 133, 135, 146, 147, 150, 151, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 219, 223, 256, 257, 258, 259, 260, 261, 262, 263, 292, 293, 294, 295, 320, 322, 324, 325, 326, 327, 329, 331, 333, 335, 356, 357, 358, 359, 365, 367, 384, 385, 388, 389, 390, 391, 402, 403, 406, 407, 420, 421, 422, 423, 438, 439, 448, 449, 450, 451, 452, 453, 454, 455, 457, 459, 461, 463, 466, 467, 470, 471, 475, 479, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xff5533110f0503015555111104040101331133110201020111111111010101010f0402010f040201050401010405010103010201020103010101010101010101, [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 80, 89, 96, 105, 112, 120, 121, 128, 136, 144, 146, 154, 160, 168, 178, 184, 186, 192, 201, 210, 216, 217, 218, 219, 224, 233, 242, 248, 249, 250, 251, 256, 264, 272, 280, 288, 292, 296, 300, 304, 308, 312, 316, 320, 329, 336, 345, 352, 356, 360, 361, 364, 365, 368, 372, 376, 377, 380, 381, 384, 392, 402, 410, 416, 420, 424, 428, 432, 434, 436, 438, 440, 442, 444, 446, 448, 456, 457, 464, 466, 472, 473, 474, 475, 480, 484, 488, 489, 492, 493, 496, 498, 500, 502, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0xfffffffffffffffffffff1f3ccccd3f3fff1fff5aab5aaf5fff3f5ff99b7d7ffffccaa99ffccaa99ffccb5b7ccff97b7ffd3aad7aa97ffd7fff3f5ff99b7d7ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 23, 24, 27, 28, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 44, 45, 46, 47, 48, 49, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 91, 93, 95, 96, 97, 98, 100, 102, 103, 105, 107, 109, 111, 112, 113, 116, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 155, 158, 159, 160, 161, 162, 164, 165, 167, 168, 170, 172, 173, 175, 178, 179, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 268, 270, 271, 272, 273, 274, 276, 277, 279, 280, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 298, 300, 301, 302, 303, 304, 305, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 322, 324, 325, 326, 327, 329, 331, 333, 335, 336, 338, 340, 341, 343, 345, 347, 349, 351, 352, 354, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 388, 389, 390, 391, 392, 393, 396, 398, 399, 402, 403, 406, 407, 410, 411, 414, 415, 416, 417, 420, 421, 422, 423, 424, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, [])
]

def case_36_484 : Catalogue.Catalogue := #[
  (0x0, []),
  (0x80, [7]),
  (0x100000000000000, [56]),
  (0x8000000000000001, [0, 63]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000, [73]),
  (0x80000000000000000002, [1, 79]),
  (0x2000000000000000000000000000100, [8, 121]),
  (0x80000000000002000200000000008303, [0, 1, 8, 9, 15, 57, 73, 127]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x4000000000000000000000000000000000000, [146]),
  (0x80000000000000000000000000000000000004, [2, 151]),
  (0x40000000000000000000000000000000000000000010000, [16, 186]),
  (0x800000000004000000000000000000000400000000850005, [0, 2, 16, 18, 23, 58, 146, 191]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x8000000000000000000000000000000000000000000000000000001, [0, 219]),
  (0x8000000000000000000800000000000000000800000000000000008f, [0, 1, 2, 3, 7, 75, 147, 223]),
  (0x800000000000000000000000400000000000000020000000100000001010101, [0, 8, 16, 24, 56, 89, 154, 251]),
  (0x8000000008000000080000008c0c0000080000008a000a008f0000008987878f, [0, 1, 2, 3, 7, 8, 9, 10, 15, 16, 17, 18, 23, 24, 27, 31, 56, 57, 58, 59, 63, 73, 75, 89, 91, 95, 123, 146, 147, 154, 155, 159, 187, 219, 255]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [484]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010, [4, 487]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 508]),
  (0x80000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 484, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 493]),
  (0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020920000000000000021, [0, 5, 65, 68, 71, 77, 485, 495]),
  (0x20001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000201000001000000010000000001, [0, 40, 72, 96, 105, 120, 492, 509]),
  (0xa000b0300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b200a2920000b2012100a103000011b3, [0, 1, 4, 5, 7, 8, 12, 32, 33, 40, 45, 47, 56, 61, 64, 73, 76, 77, 79, 97, 100, 103, 105, 109, 111, 121, 124, 125, 127, 484, 485, 492, 493, 495, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 502]),
  (0x800040000000000000000000000000000000000000000000000000000000000000000000000000000000000040009400000000000000000000000000000041, [0, 6, 130, 132, 135, 150, 486, 503]),
  (0x40100000000000000000000000000000000000000000000000000000000000000000000000000000010400010001000000000000000000000001000000000001, [0, 48, 144, 160, 178, 184, 500, 510]),
  (0xc0d00050000000000000000000000000000000000000000000000000000000000000000000000000d4c4009400d40001000000000000000041c10005001100d5, [0, 2, 4, 6, 7, 16, 20, 32, 34, 48, 54, 55, 56, 62, 128, 146, 148, 150, 151, 162, 164, 167, 178, 182, 183, 186, 188, 190, 191, 484, 486, 500, 502, 503, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000010000000000000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 484, 511]),
  (0x808080f0000000000000000000000000000000000000000000000000000000000000000080c8a89800000000008400a700000000000082c70000000000000097, [0, 1, 2, 4, 7, 64, 65, 66, 70, 71, 73, 79, 128, 129, 130, 133, 135, 146, 151, 195, 196, 199, 203, 205, 207, 211, 214, 215, 223, 484, 485, 486, 487, 495, 503, 511]),
  (0xf0101010000000000000000000000000000000000000000000000000000000000f04020107000000050001000005010103010000000103010100000100010101, [0, 8, 16, 32, 56, 64, 72, 73, 80, 112, 120, 121, 128, 136, 144, 146, 168, 184, 186, 216, 217, 218, 224, 233, 242, 248, 249, 250, 251, 484, 492, 500, 508, 509, 510, 511]),
  (0xf0f0f0f000000000000000000000000000000000000000000000000000000000f8c8a898f8040201a70ca40344ef9797c7c20a052297ef979703059f11b5d3ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 14, 15, 16, 18, 20, 21, 23, 24, 28, 32, 33, 34, 35, 36, 39, 40, 42, 48, 49, 56, 57, 58, 60, 63, 64, 65, 66, 68, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 82, 84, 87, 89, 93, 96, 98, 105, 107, 113, 118, 119, 120, 121, 122, 126, 127, 128, 129, 130, 132, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 149, 150, 151, 154, 158, 160, 161, 170, 173, 175, 178, 179, 184, 185, 186, 189, 191, 192, 201, 210, 219, 220, 221, 222, 223, 227, 228, 231, 235, 237, 239, 243, 246, 247, 251, 252, 253, 254, 255, 484, 485, 486, 487, 492, 493, 494, 495, 500, 501, 502, 503, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [484]),
  (0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010, [4, 487]),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 508]),
  (0x80000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 484, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 493]),
  (0x8020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020920000000000000021, [0, 5, 65, 68, 71, 77, 485, 495]),
  (0x20001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000201000001000000010000000001, [0, 40, 72, 96, 105, 120, 492, 509]),
  (0xa000b0300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b200a2920000b2012100a103000011b3, [0, 1, 4, 5, 7, 8, 12, 32, 33, 40, 45, 47, 56, 61, 64, 73, 76, 77, 79, 97, 100, 103, 105, 109, 111, 121, 124, 125, 127, 484, 485, 492, 493, 495, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 502]),
  (0x800040000000000000000000000000000000000000000000000000000000000000000000000000000000000040009400000000000000000000000000000041, [0, 6, 130, 132, 135, 150, 486, 503]),
  (0x40100000000000000000000000000000000000000000000000000000000000000000000000000000010400010001000000000000000000000001000000000001, [0, 48, 144, 160, 178, 184, 500, 510]),
  (0xc0d00050000000000000000000000000000000000000000000000000000000000000000000000000d4c4009400d40001000000000000000041c10005001100d5, [0, 2, 4, 6, 7, 16, 20, 32, 34, 48, 54, 55, 56, 62, 128, 146, 148, 150, 151, 162, 164, 167, 178, 182, 183, 186, 188, 190, 191, 484, 486, 500, 502, 503, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80000010000000000000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 484, 511]),
  (0x808080f0000000000000000000000000000000000000000000000000000000000000000080c8a89800000000008400a700000000000082c70000000000000097, [0, 1, 2, 4, 7, 64, 65, 66, 70, 71, 73, 79, 128, 129, 130, 133, 135, 146, 151, 195, 196, 199, 203, 205, 207, 211, 214, 215, 223, 484, 485, 486, 487, 495, 503, 511]),
  (0xf0101010000000000000000000000000000000000000000000000000000000000f04020107000000050001000005010103010000000103010100000100010101, [0, 8, 16, 32, 56, 64, 72, 73, 80, 112, 120, 121, 128, 136, 144, 146, 168, 184, 186, 216, 217, 218, 224, 233, 242, 248, 249, 250, 251, 484, 492, 500, 508, 509, 510, 511]),
  (0xf0f0f0f000000000000000000000000000000000000000000000000000000000f8c8a898f8040201a70ca40344ef9797c7c20a052297ef979703059f11b5d3ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 14, 15, 16, 18, 20, 21, 23, 24, 28, 32, 33, 34, 35, 36, 39, 40, 42, 48, 49, 56, 57, 58, 60, 63, 64, 65, 66, 68, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 82, 84, 87, 89, 93, 96, 98, 105, 107, 113, 118, 119, 120, 121, 122, 126, 127, 128, 129, 130, 132, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 149, 150, 151, 154, 158, 160, 161, 170, 173, 175, 178, 179, 184, 185, 186, 189, 191, 192, 201, 210, 219, 220, 221, 222, 223, 227, 228, 231, 235, 237, 239, 243, 246, 247, 251, 252, 253, 254, 255, 484, 485, 486, 487, 492, 493, 494, 495, 500, 501, 502, 503, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, [484]),
  (0x90000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010, [4, 484, 487]),
  (0x10000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000, [32, 484, 508]),
  (0x90000090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000009100000011, [0, 4, 32, 36, 39, 60, 484, 487, 508, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x2010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000, [64, 484, 493]),
  (0xa0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020930000000000000031, [0, 4, 5, 64, 65, 68, 71, 77, 484, 485, 487, 493, 495]),
  (0x30003010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000201000001010000010100000001, [0, 32, 40, 64, 72, 96, 105, 120, 484, 492, 493, 508, 509]),
  (0xb000b0b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b300a2930000b3933100b1b3000011b3, [0, 1, 4, 5, 7, 8, 12, 32, 33, 36, 37, 39, 40, 44, 45, 47, 56, 60, 61, 64, 65, 68, 71, 72, 73, 76, 77, 79, 96, 97, 100, 103, 105, 109, 111, 120, 121, 124, 125, 127, 484, 485, 487, 492, 493, 495, 508, 509, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x400010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000, [128, 484, 502]),
  (0xc000d0000000000000000000000000000000000000000000000000000000000000000000000000000000000040009500000000000000000000000000000051, [0, 4, 6, 128, 130, 132, 135, 150, 484, 486, 487, 502, 503]),
  (0x50500010000000000000000000000000000000000000000000000000000000000000000000000000010400010001000100000000000000000001000100000001, [0, 32, 48, 128, 144, 160, 178, 184, 484, 500, 502, 508, 510]),
  (0xd0d000d0000000000000000000000000000000000000000000000000000000000000000000000000d5c4009500d50095000000000000000051d100d5001100d5, [0, 2, 4, 6, 7, 16, 20, 32, 34, 36, 38, 39, 48, 52, 54, 55, 56, 60, 62, 128, 130, 132, 135, 144, 146, 148, 150, 151, 160, 162, 164, 167, 178, 182, 183, 184, 186, 188, 190, 191, 484, 486, 487, 500, 502, 503, 508, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x80402010000000000000000000000000000000000000000000000000000000000000000000040201000000000000000100000000000000010000000000000001, [0, 64, 128, 192, 201, 210, 484, 493, 502, 511]),
  (0x80c0a0f0000000000000000000000000000000000000000000000000000000000000000080ccaa9f0000000000c400b7000000000000a2d700000000000000f7, [0, 1, 2, 4, 5, 6, 7, 64, 65, 66, 68, 70, 71, 73, 77, 79, 128, 129, 130, 132, 133, 135, 146, 150, 151, 192, 193, 194, 195, 196, 199, 201, 203, 205, 207, 210, 211, 214, 215, 223, 484, 485, 486, 487, 493, 495, 502, 503, 511]),
  (0xf0503010000000000000000000000000000000000000000000000000000000000f04020107050301050401010005010103010201000103010101010100010101, [0, 8, 16, 32, 40, 48, 56, 64, 72, 73, 80, 96, 105, 112, 120, 121, 128, 136, 144, 146, 160, 168, 178, 184, 186, 192, 200, 201, 208, 210, 216, 217, 218, 224, 233, 242, 248, 249, 250, 251, 484, 492, 493, 500, 502, 508, 509, 510, 511]),
  (0xf0f0f0f000000000000000000000000000000000000000000000000000000000ffccaa9fffdfbf9ff7ccb5b744ff97b7f7d3aad72297ffd7f7f3f5ff11b5d3ff, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 14, 15, 16, 18, 20, 21, 23, 24, 28, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 44, 45, 46, 47, 48, 49, 52, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 87, 89, 93, 96, 97, 98, 100, 102, 103, 105, 107, 109, 111, 112, 113, 116, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 132, 133, 135, 136, 137, 138, 140, 143, 144, 145, 146, 147, 148, 149, 150, 151, 154, 158, 160, 161, 162, 164, 165, 167, 168, 170, 172, 173, 175, 178, 179, 182, 183, 184, 185, 186, 188, 189, 190, 191, 192, 193, 194, 195, 196, 199, 200, 201, 202, 203, 204, 205, 207, 208, 209, 210, 211, 212, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 231, 233, 235, 237, 239, 242, 243, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 484, 485, 486, 487, 492, 493, 494, 495, 500, 501, 502, 503, 508, 509, 510, 511]),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, []),
  (0x0, [])
]

end Catalogues

namespace Guarded

open Promise (repRow)
open Catalogue Catalogues
open ContractionGuard ReadOnce
open CutExpression

private def rowU (p : Fin 9) : Fin 3 := ⟨p.val / 3, by omega⟩
private def rowV (p : Fin 9) : Fin 3 := ⟨p.val % 3, by omega⟩

private theorem rowIndex (p : Fin 9) : 3 * (rowU p).val + (rowV p).val = p.val := by
  simp only [rowU, rowV]
  omega

private def Good (a : Nat) (p q : Fin 9) : Prop :=
  (238 : Nat).testBit p.val = true ∧ (238 : Nat).testBit q.val = false ∧
    ∀ i : Fin 6, a.testBit i.val = false →
      (repRow 3 (rowU p) (rowV p)).testBit i.val = true →
      (repRow 3 (rowU q) (rowV q)).testBit i.val = true

private def Guard (a x : Nat) : Prop :=
  ∀ p q : Fin 9, Good a p q → x.testBit p.val = true ∧ x.testBit q.val = false

private instance (a : Nat) (p q : Fin 9) : Decidable (Good a p q) := by unfold Good; infer_instance
private instance (a x : Nat) : Decidable (Guard a x) := by unfold Guard; infer_instance

private theorem obeys {a b x : Nat} (outer : Expr b) (disjoint : a &&& b = 0)
    (out : outer.tableWith x = 238) : Guard a x := by
  intro p q good
  have pos : (238 : Nat).testBit (3 * (rowU p).val + (rowV p).val) = true := by
    rw [rowIndex]
    exact good.1
  have neg : (238 : Nat).testBit (3 * (rowU q).val + (rowV q).val) = false := by
    rw [rowIndex]
    exact good.2.1
  have f := forced_shared_bits outer disjoint out (rowU p) (rowV p) (rowU q) (rowV q)
    pos neg (fun i lt => good.2.2 ⟨i,lt⟩)
  rwa [rowIndex, rowIndex] at f

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem plainClosed : ∀ s : Fin plain.size, checkRow plain s.val = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem plainAgree : ∀ s : Fin 64, agrees plain s.val := by
  decide +kernel

private theorem plainLeaf : ∀ i : Fin 6, bit plain (2 ^ i.val) (inputBits i.val) = true := by
  decide +kernel

private theorem readOnce_mem {a x : Nat} (h : ReadOnce a x) : x ∈ entries plain a := by
  induction h with
  | input i =>
    exact (bit_iff (plainAgree ⟨2 ^ i.val, (range_of_read_once (ReadOnce.input i)).2.1⟩)).mp (plainLeaf i)
  | @gate a b x y choose separate h1 h2 ih1 ih2 =>
    have ra : a < plain.size := (range_of_read_once h1).2.1
    have rb : b < plain.size := (range_of_read_once h2).2.1
    have merged : a ||| b < 64 := Nat.or_lt_two_pow (n := 6)
      (range_of_read_once h1).2.1 (range_of_read_once h2).2.1
    have child := close plainClosed ra rb (plainAgree ⟨_, merged⟩) separate ih1 ih2
    cases choose
    · exact child.2
    · exact child.1

private theorem plainAbsent : ∀ s : Fin 64, bit plain s.val 238 = false := by decide +kernel

theorem no_read_once {a : Nat} (h : ReadOnce a 238) : False :=
  let f : Fin 64 := ⟨a, (range_of_read_once h).2.1⟩
  excluded (plainAgree f) (plainAbsent f) (readOnce_mem h)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem checkedGuard : ∀ a : Fin 64,
    (entries plain a.val).all (fun x => !decide (Guard a.val x) || decide ((a.val,x) ∈ candidates)) = true := by
  decide +kernel

theorem only_candidates {a b x : Nat} (h : ReadOnce a x) (outer : Expr b)
    (disjoint : a &&& b = 0) (out : outer.tableWith x = 238) : (a,x) ∈ candidates := by
  have xmem := readOnce_mem h
  have all := checkedGuard ⟨a,(range_of_read_once h).2.1⟩
  have row := List.all_eq_true.mp all x xmem
  simpa [obeys outer disjoint out] using row

end Guarded

namespace Context

open Catalogue
open ContractionGuard
open ReadOnce (inputBits combine)
open CutExpression (Expr markerIndex)

structure Verified (rows : Catalogue) (removed shared : Nat) : Prop where
  sizeEq : rows.size = 256
  closed : ∀ s : Fin 256, checkRow rows s.val = true
  consistent : ∀ s : Fin 256, agrees rows s.val
  raw : ∀ i : Fin 6, removed &&& 2 ^ i.val = 0 → bit rows (2 ^ i.val) (inputBits i.val) = true
  marker : ∀ b : Bool, bit rows (2 ^ markerIndex b) shared = true
  absent : ∀ s : Fin 256, bit rows s.val 238 = false

theorem context_mem {rows : Catalogue} {removed shared s : Nat}
    (h : Verified rows removed shared)
    (e : Expr s) (disjoint : removed &&& s = 0) :
    e.tableWith shared ∈ entries rows s := by
  induction e with
  | input i =>
    have bounded := (support_bounds (Expr.input i)).2
    exact (bit_iff (h.consistent ⟨_, bounded⟩)).mp (h.raw i disjoint)
  | marker b =>
    have bounded := (support_bounds (Expr.marker b)).2
    exact (bit_iff (h.consistent ⟨_, bounded⟩)).mp (h.marker b)
  | @gate a b choice sep l r hl hr =>
    rw [Nat.and_or_distrib_left] at disjoint
    obtain ⟨dl, dr⟩ := Nat.or_eq_zero_iff.mp disjoint
    have ar : a < rows.size := h.sizeEq.symm ▸ (support_bounds l).2
    have br : b < rows.size := h.sizeEq.symm ▸ (support_bounds r).2
    have merged := (support_bounds (Expr.gate choice sep l r)).2
    have cc := close (fun i => h.closed ⟨i.val, h.sizeEq ▸ i.isLt⟩)
      ar br (h.consistent ⟨_, merged⟩) sep (hl dl) (hr dr)
    cases choice
    · exact cc.2
    · exact cc.1

theorem excludes {rows : Catalogue} {removed shared s : Nat}
    (h : Verified rows removed shared) (e : Expr s)
    (disjoint : removed &&& s = 0) (out : e.tableWith shared = 238) : False := by
  let f : Fin 256 := ⟨s, (support_bounds e).2⟩
  exact excluded (h.consistent f) (h.absent f) (out ▸ context_mem h e disjoint)

end Context

namespace NfMin

open Link

theorem nf_of_min {n s : Nat} {g : Nat → Bool} {R : Nat → Prop} {M : Model}
    (hv : Valid n s g R M)
    (hmin : ∀ N, Valid n s g R N → meas n s N < meas n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas_sw hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by have := hall (s - 1 - j) (by omega); rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

end NfMin

namespace NormalizePlain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Link
open Promise (repRow repRows repRow_eq gMask_row)
open Normalized ThreeLive
open scoped BigOperators

private theorem start_valid (C : Circuit) (hC : Monotone2 C) (sz : C.size ≤ 6)
    (hr : ∀ u v : Fin 3, C.eval (oneEach u v) = CycleTransfer.compressed u v) :
    Valid 6 7 table (· ∈ rows) (ofCirc 6 7 C) := by
  change C.gates.length ≤ 6 at sz
  apply valid_ofCirc 6 7 table (· ∈ rows) C hC (by omega)
  intro r member
  obtain ⟨u, v, rfl⟩ : ∃ (u : Fin 3) (v : Fin 3), repRow 3 u v = r := by
    simpa [repRows] using member
  change C.eval (List.ofFn (fun i : Fin (3+3) => (repRow 3 u v).testBit i)) = _
  rw [repRow_eq]
  exact (hr u v).trans (gMask_row 238 u v).symm

private theorem ind_le_one (M : Model) (i : Nat) : ind 6 M i ≤ 1 := by
  unfold ind
  split <;> decide

private theorem padded_weight (M : Model) (h : M.pad 6 6) : muf 7 (ind 6 M) ≤ 27 := by
  rw [muf, Finset.sum_range_succ]
  have upper : (∑ i ∈ Finset.range 6, (7 - i) * ind 6 M i) ≤
      ∑ i ∈ Finset.range 6, (7 - i) := by
    apply Finset.sum_le_sum
    intro i _
    simpa using Nat.mul_le_mul_left (7 - i) (ind_le_one M i)
  have zero : ind 6 M 6 = 0 := if_pos h
  rw [zero, Nat.mul_zero, Nat.add_zero]
  exact upper.trans (by decide)

private theorem full_weight (M : Model) (h : (activeGates M).card = 7) :
    muf 7 (ind 6 M) = 28 := by
  have subset : activeGates M ⊆ Finset.range 7 := Finset.filter_subset _ _
  have all : activeGates M = Finset.range 7 := Finset.eq_of_subset_of_card_le subset (by simp [h])
  rw [muf, ← show (∑ i ∈ Finset.range 7, (7-i)) = 28 by decide]
  apply Finset.sum_congr rfl
  intro i mem
  have active : i ∈ activeGates M := all ▸ mem
  have alive := (Finset.mem_filter.mp active).2
  simp [ind, alive]

private theorem normalized_small {M₀ : Model} (h₀ : Valid 6 7 table (· ∈ rows) M₀)
    (padded : M₀.pad 6 6) :
    ∃ M, Valid 6 7 table (· ∈ rows) M ∧ NF 6 7 M ∧ (activeGates M).card ≤ 6 := by
  classical
  have hex : ∃ m, ∃ M, Valid 6 7 table (· ∈ rows) M ∧ meas 6 7 M = m :=
    ⟨_, M₀, h₀, rfl⟩
  obtain ⟨M, hv, found⟩ := Nat.find_spec hex
  have minimal (N : Model) (hn : Valid 6 7 table (· ∈ rows) N) :
      meas 6 7 M ≤ meas 6 7 N := by
    rw [found]
    exact Nat.find_min' hex ⟨N, hn, rfl⟩
  have nf := NfMin.nf_of_min hv (fun N hn lt => (Nat.not_lt_of_ge (minimal N hn)) lt)
  have upper : (activeGates M).card ≤ 7 := by
    have subset : activeGates M ⊆ Finset.range 7 := Finset.filter_subset _ _
    simpa using Finset.card_le_card subset
  refine ⟨M, hv, nf, ?_⟩
  by_contra large
  have seven : (activeGates M).card = 7 := by omega
  have min₀ := minimal M₀ h₀
  unfold meas at min₀
  rw [full_weight M seven] at min₀
  have weight := padded_weight M₀ padded
  have sm := ssum_le h₀
  omega

theorem normalize (h : RepSizeAtMost CycleTransfer.compressed 6) :
    ∃ M, Valid 6 7 table (· ∈ rows) M ∧ NF 6 7 M ∧ (activeGates M).card ≤ 6 := by
  obtain ⟨C, hC, sz, hr⟩ := h
  have valid := start_valid C hC sz hr
  have outOfRange : C.gates.length ≤ 6 := sz
  have get : C.gates[6]? = none := List.getElem?_eq_none (by omega)
  have padded : (ofCirc 6 7 C).pad 6 6 := by
    simp [Model.pad, ofCirc, gateAt, List.getD_eq_getElem?_getD, get, Link.code]
  exact normalized_small valid padded

end NormalizePlain

namespace ContextChecks

open Catalogues Context
open ReadOnce CutExpression

open Catalogue

private abbrev ClosedBlock (rows : Catalogue) (k : Nat) : Prop :=
  ∀ j : Fin 16, checkRow rows (16 * k + j.val) = true

private theorem closed_by_blocks {rows : Catalogue}
    (h : ∀ i : Fin 16, ClosedBlock rows i.val) :
    ∀ s : Fin 256, checkRow rows s.val = true := by
  intro s
  let i : Fin 16 := ⟨s.val / 16, by have := s.isLt; omega⟩
  let j : Fin 16 := ⟨s.val % 16, by omega⟩
  have index : 16 * i.val + j.val = s.val := by dsimp [i,j]; omega
  have result := h i j
  rwa [index] at result

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_0 : ClosedBlock case_1_7 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_1 : ClosedBlock case_1_7 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_2 : ClosedBlock case_1_7 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_3 : ClosedBlock case_1_7 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_4 : ClosedBlock case_1_7 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_5 : ClosedBlock case_1_7 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_6 : ClosedBlock case_1_7 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_7 : ClosedBlock case_1_7 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_8 : ClosedBlock case_1_7 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_9 : ClosedBlock case_1_7 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_10 : ClosedBlock case_1_7 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_11 : ClosedBlock case_1_7 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_12 : ClosedBlock case_1_7 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_13 : ClosedBlock case_1_7 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_14 : ClosedBlock case_1_7 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_1_7_15 : ClosedBlock case_1_7 15 := by
  decide +kernel

private theorem closed_1_7 : ∀ s : Fin 256, checkRow case_1_7 s.val = true :=
  closed_by_blocks fun i => by
    fin_cases i
    · exact block_1_7_0
    · exact block_1_7_1
    · exact block_1_7_2
    · exact block_1_7_3
    · exact block_1_7_4
    · exact block_1_7_5
    · exact block_1_7_6
    · exact block_1_7_7
    · exact block_1_7_8
    · exact block_1_7_9
    · exact block_1_7_10
    · exact block_1_7_11
    · exact block_1_7_12
    · exact block_1_7_13
    · exact block_1_7_14
    · exact block_1_7_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verify_1_7 : Verified case_1_7 1 7 := by
  refine ⟨?_, closed_1_7, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_0 : ClosedBlock case_2_56 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_1 : ClosedBlock case_2_56 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_2 : ClosedBlock case_2_56 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_3 : ClosedBlock case_2_56 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_4 : ClosedBlock case_2_56 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_5 : ClosedBlock case_2_56 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_6 : ClosedBlock case_2_56 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_7 : ClosedBlock case_2_56 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_8 : ClosedBlock case_2_56 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_9 : ClosedBlock case_2_56 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_10 : ClosedBlock case_2_56 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_11 : ClosedBlock case_2_56 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_12 : ClosedBlock case_2_56 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_13 : ClosedBlock case_2_56 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_14 : ClosedBlock case_2_56 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_2_56_15 : ClosedBlock case_2_56 15 := by
  decide +kernel

private theorem closed_2_56 : ∀ s : Fin 256, checkRow case_2_56 s.val = true :=
  closed_by_blocks fun i => by
    fin_cases i
    · exact block_2_56_0
    · exact block_2_56_1
    · exact block_2_56_2
    · exact block_2_56_3
    · exact block_2_56_4
    · exact block_2_56_5
    · exact block_2_56_6
    · exact block_2_56_7
    · exact block_2_56_8
    · exact block_2_56_9
    · exact block_2_56_10
    · exact block_2_56_11
    · exact block_2_56_12
    · exact block_2_56_13
    · exact block_2_56_14
    · exact block_2_56_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verify_2_56 : Verified case_2_56 2 56 := by
  refine ⟨?_, closed_2_56, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_0 : ClosedBlock case_4_448 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_1 : ClosedBlock case_4_448 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_2 : ClosedBlock case_4_448 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_3 : ClosedBlock case_4_448 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_4 : ClosedBlock case_4_448 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_5 : ClosedBlock case_4_448 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_6 : ClosedBlock case_4_448 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_7 : ClosedBlock case_4_448 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_8 : ClosedBlock case_4_448 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_9 : ClosedBlock case_4_448 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_10 : ClosedBlock case_4_448 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_11 : ClosedBlock case_4_448 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_12 : ClosedBlock case_4_448 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_13 : ClosedBlock case_4_448 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_14 : ClosedBlock case_4_448 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_4_448_15 : ClosedBlock case_4_448 15 := by
  decide +kernel

private theorem closed_4_448 : ∀ s : Fin 256, checkRow case_4_448 s.val = true :=
  closed_by_blocks fun i => by
    fin_cases i
    · exact block_4_448_0
    · exact block_4_448_1
    · exact block_4_448_2
    · exact block_4_448_3
    · exact block_4_448_4
    · exact block_4_448_5
    · exact block_4_448_6
    · exact block_4_448_7
    · exact block_4_448_8
    · exact block_4_448_9
    · exact block_4_448_10
    · exact block_4_448_11
    · exact block_4_448_12
    · exact block_4_448_13
    · exact block_4_448_14
    · exact block_4_448_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verify_4_448 : Verified case_4_448 4 448 := by
  refine ⟨?_, closed_4_448, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_0 : ClosedBlock case_8_73 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_1 : ClosedBlock case_8_73 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_2 : ClosedBlock case_8_73 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_3 : ClosedBlock case_8_73 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_4 : ClosedBlock case_8_73 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_5 : ClosedBlock case_8_73 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_6 : ClosedBlock case_8_73 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_7 : ClosedBlock case_8_73 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_8 : ClosedBlock case_8_73 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_9 : ClosedBlock case_8_73 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_10 : ClosedBlock case_8_73 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_11 : ClosedBlock case_8_73 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_12 : ClosedBlock case_8_73 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_13 : ClosedBlock case_8_73 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_14 : ClosedBlock case_8_73 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_8_73_15 : ClosedBlock case_8_73 15 := by
  decide +kernel

private theorem closed_8_73 : ∀ s : Fin 256, checkRow case_8_73 s.val = true :=
  closed_by_blocks fun i => by
    fin_cases i
    · exact block_8_73_0
    · exact block_8_73_1
    · exact block_8_73_2
    · exact block_8_73_3
    · exact block_8_73_4
    · exact block_8_73_5
    · exact block_8_73_6
    · exact block_8_73_7
    · exact block_8_73_8
    · exact block_8_73_9
    · exact block_8_73_10
    · exact block_8_73_11
    · exact block_8_73_12
    · exact block_8_73_13
    · exact block_8_73_14
    · exact block_8_73_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verify_8_73 : Verified case_8_73 8 73 := by
  refine ⟨?_, closed_8_73, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_0 : ClosedBlock case_9_79 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_1 : ClosedBlock case_9_79 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_2 : ClosedBlock case_9_79 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_3 : ClosedBlock case_9_79 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_4 : ClosedBlock case_9_79 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_5 : ClosedBlock case_9_79 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_6 : ClosedBlock case_9_79 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_7 : ClosedBlock case_9_79 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_8 : ClosedBlock case_9_79 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_9 : ClosedBlock case_9_79 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_10 : ClosedBlock case_9_79 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_11 : ClosedBlock case_9_79 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_12 : ClosedBlock case_9_79 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_13 : ClosedBlock case_9_79 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_14 : ClosedBlock case_9_79 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_9_79_15 : ClosedBlock case_9_79 15 := by
  decide +kernel

private theorem closed_9_79 : ∀ s : Fin 256, checkRow case_9_79 s.val = true :=
  closed_by_blocks fun i => by
    fin_cases i
    · exact block_9_79_0
    · exact block_9_79_1
    · exact block_9_79_2
    · exact block_9_79_3
    · exact block_9_79_4
    · exact block_9_79_5
    · exact block_9_79_6
    · exact block_9_79_7
    · exact block_9_79_8
    · exact block_9_79_9
    · exact block_9_79_10
    · exact block_9_79_11
    · exact block_9_79_12
    · exact block_9_79_13
    · exact block_9_79_14
    · exact block_9_79_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verify_9_79 : Verified case_9_79 9 79 := by
  refine ⟨?_, closed_9_79, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_0 : ClosedBlock case_16_146 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_1 : ClosedBlock case_16_146 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_2 : ClosedBlock case_16_146 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_3 : ClosedBlock case_16_146 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_4 : ClosedBlock case_16_146 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_5 : ClosedBlock case_16_146 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_6 : ClosedBlock case_16_146 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_7 : ClosedBlock case_16_146 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_8 : ClosedBlock case_16_146 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_9 : ClosedBlock case_16_146 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_10 : ClosedBlock case_16_146 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_11 : ClosedBlock case_16_146 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_12 : ClosedBlock case_16_146 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_13 : ClosedBlock case_16_146 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_14 : ClosedBlock case_16_146 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_16_146_15 : ClosedBlock case_16_146 15 := by
  decide +kernel

private theorem closed_16_146 : ∀ s : Fin 256, checkRow case_16_146 s.val = true :=
  closed_by_blocks fun i => by
    fin_cases i
    · exact block_16_146_0
    · exact block_16_146_1
    · exact block_16_146_2
    · exact block_16_146_3
    · exact block_16_146_4
    · exact block_16_146_5
    · exact block_16_146_6
    · exact block_16_146_7
    · exact block_16_146_8
    · exact block_16_146_9
    · exact block_16_146_10
    · exact block_16_146_11
    · exact block_16_146_12
    · exact block_16_146_13
    · exact block_16_146_14
    · exact block_16_146_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verify_16_146 : Verified case_16_146 16 146 := by
  refine ⟨?_, closed_16_146, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_0 : ClosedBlock case_18_186 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_1 : ClosedBlock case_18_186 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_2 : ClosedBlock case_18_186 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_3 : ClosedBlock case_18_186 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_4 : ClosedBlock case_18_186 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_5 : ClosedBlock case_18_186 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_6 : ClosedBlock case_18_186 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_7 : ClosedBlock case_18_186 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_8 : ClosedBlock case_18_186 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_9 : ClosedBlock case_18_186 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_10 : ClosedBlock case_18_186 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_11 : ClosedBlock case_18_186 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_12 : ClosedBlock case_18_186 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_13 : ClosedBlock case_18_186 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_14 : ClosedBlock case_18_186 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_18_186_15 : ClosedBlock case_18_186 15 := by
  decide +kernel

private theorem closed_18_186 : ∀ s : Fin 256, checkRow case_18_186 s.val = true :=
  closed_by_blocks fun i => by
    fin_cases i
    · exact block_18_186_0
    · exact block_18_186_1
    · exact block_18_186_2
    · exact block_18_186_3
    · exact block_18_186_4
    · exact block_18_186_5
    · exact block_18_186_6
    · exact block_18_186_7
    · exact block_18_186_8
    · exact block_18_186_9
    · exact block_18_186_10
    · exact block_18_186_11
    · exact block_18_186_12
    · exact block_18_186_13
    · exact block_18_186_14
    · exact block_18_186_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verify_18_186 : Verified case_18_186 18 186 := by
  refine ⟨?_, closed_18_186, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_0 : ClosedBlock case_32_292 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_1 : ClosedBlock case_32_292 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_2 : ClosedBlock case_32_292 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_3 : ClosedBlock case_32_292 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_4 : ClosedBlock case_32_292 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_5 : ClosedBlock case_32_292 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_6 : ClosedBlock case_32_292 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_7 : ClosedBlock case_32_292 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_8 : ClosedBlock case_32_292 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_9 : ClosedBlock case_32_292 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_10 : ClosedBlock case_32_292 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_11 : ClosedBlock case_32_292 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_12 : ClosedBlock case_32_292 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_13 : ClosedBlock case_32_292 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_14 : ClosedBlock case_32_292 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_32_292_15 : ClosedBlock case_32_292 15 := by
  decide +kernel

private theorem closed_32_292 : ∀ s : Fin 256, checkRow case_32_292 s.val = true :=
  closed_by_blocks fun i => by
    fin_cases i
    · exact block_32_292_0
    · exact block_32_292_1
    · exact block_32_292_2
    · exact block_32_292_3
    · exact block_32_292_4
    · exact block_32_292_5
    · exact block_32_292_6
    · exact block_32_292_7
    · exact block_32_292_8
    · exact block_32_292_9
    · exact block_32_292_10
    · exact block_32_292_11
    · exact block_32_292_12
    · exact block_32_292_13
    · exact block_32_292_14
    · exact block_32_292_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verify_32_292 : Verified case_32_292 32 292 := by
  refine ⟨?_, closed_32_292, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_0 : ClosedBlock case_36_484 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_1 : ClosedBlock case_36_484 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_2 : ClosedBlock case_36_484 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_3 : ClosedBlock case_36_484 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_4 : ClosedBlock case_36_484 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_5 : ClosedBlock case_36_484 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_6 : ClosedBlock case_36_484 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_7 : ClosedBlock case_36_484 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_8 : ClosedBlock case_36_484 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_9 : ClosedBlock case_36_484 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_10 : ClosedBlock case_36_484 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_11 : ClosedBlock case_36_484 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_12 : ClosedBlock case_36_484 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_13 : ClosedBlock case_36_484 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_14 : ClosedBlock case_36_484 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem block_36_484_15 : ClosedBlock case_36_484 15 := by
  decide +kernel

private theorem closed_36_484 : ∀ s : Fin 256, checkRow case_36_484 s.val = true :=
  closed_by_blocks fun i => by
    fin_cases i
    · exact block_36_484_0
    · exact block_36_484_1
    · exact block_36_484_2
    · exact block_36_484_3
    · exact block_36_484_4
    · exact block_36_484_5
    · exact block_36_484_6
    · exact block_36_484_7
    · exact block_36_484_8
    · exact block_36_484_9
    · exact block_36_484_10
    · exact block_36_484_11
    · exact block_36_484_12
    · exact block_36_484_13
    · exact block_36_484_14
    · exact block_36_484_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verify_36_484 : Verified case_36_484 36 484 := by
  refine ⟨?_, closed_36_484, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem no_shared {a b x : Nat} (h : ReadOnce a x) (outer : Expr b)
    (sep : a &&& b = 0) (out : outer.tableWith x = 238) : False := by
  have listed := Guarded.only_candidates h outer sep out
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  rcases listed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact excludes verify_1_7 outer sep out
  · exact excludes verify_2_56 outer sep out
  · exact excludes verify_4_448 outer sep out
  · exact excludes verify_8_73 outer sep out
  · exact excludes verify_9_79 outer sep out
  · exact excludes verify_16_146 outer sep out
  · exact excludes verify_18_186 outer sep out
  · exact excludes verify_32_292 outer sep out
  · exact excludes verify_36_484 outer sep out

end ContextChecks

namespace Candidate

open PEqualNP.Represents
open ThreeLive

theorem no_six_cycle : ¬ RepSizeAtMost CycleTransfer.compressed 6 := by
  intro h
  obtain ⟨M, hv, hn, cap⟩ := NormalizePlain.normalize h
  have lower := at_least_five hv hn
  by_cases five : (activeGates M).card = 5
  · obtain ⟨s, hread⟩ := ReadOnce.five_gates_read_once hv hn five
    exact Guarded.no_read_once hread
  · obtain ⟨a, b, x, outer, plain, separate, out⟩ :=
      Contraction.six_gates_contract hv hn (by omega)
    exact ContextChecks.no_shared plain outer separate out

theorem no_ten :
    ¬ RepSizeAtMost (fun u v : Fin 5 => (12075574 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  fun h => no_six_cycle (Reduction.to_cycle h)

end Candidate

end PEqualNP.Outside.L_meta_10229_aux

theorem PEqualNP.Outside.L_meta_10229 :
    ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12075574 : ℕ).testBit (5 * u.val + v.val)) 10) :=
  PEqualNP.Outside.L_meta_10229_aux.Candidate.no_ten
