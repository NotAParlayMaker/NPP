import Mathlib
import PEqualNP.Defs

namespace LMeta567

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.MetaComplexity.Helpers

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

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

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

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

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

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

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

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

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

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

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

theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

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

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

end

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers.PermInputs

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

end PEqualNP.MetaComplexity.Helpers.PermInputs

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

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
  PEqualNP.MetaComplexity.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS

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

end PEqualNP.MetaComplexity.Helpers.Readers

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

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

theorem Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩

end

end PEqualNP.MetaComplexity.Helpers.Readers

namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

theorem set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]

theorem set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]

theorem set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

end

end PEqualNP.MetaComplexity.Helpers.Readers

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

def rd (N p a w : ℕ) : ℕ := if w < N + p then w else if w = N + p then a else w - 1

def rdel (N p a : ℕ) (gs : List Gate) : List Gate :=
  gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (rd N p a)⟩

def TailOK (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧ (g.op = GateOp.not ∨
    (g.op = GateOp.or ∧ ∀ x : Fin N → Bool, vl gs x (N + j) = true → F x = true))

def TailGE (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (t : ℕ) : Prop :=
  t ≤ gs.length ∧ ∀ j, gs.length ≤ j + t → j < gs.length → TailOK N F gs j

def StmtLift : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p l h : ℕ) (g : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) →
    gs[p]? = some g → g.op = GateOp.or → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    (∀ x : Fin N → Bool, vl gs x h = true → F x = true) →
    Least N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (N + (gs.length - 1)) ∧
    (¬ TailOK N F gs p → ∀ t, TailGE N F gs t →
      TailGE N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (t + 1))

def StmtXMove : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p p' l q h : ℕ) (g g' : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) → p < p' →
    gs[p]? = some g → g.op = GateOp.and → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    gs[p']? = some g' → g'.op = GateOp.and → (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    ∃ (gs' : List Gate) (o' : ℕ), Least N F gs' o' ∧
      ∀ t, TailGE N F gs t → TailGE N F gs' (t + 2)

def StmtExch : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o h : ℕ) (T : Finset ℕ),
    CleanL N gs → (∀ x : Fin N → Bool, vl gs x o = F x) → (∃ x y : Fin N → Bool, F x ≠ F y) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (N + r)) →
    ∃ (gs' : List Gate) (o' : ℕ), CleanL N gs' ∧ (∀ x : Fin N → Bool, vl gs' x o' = F x) ∧
      gs'.length + T.card ≤ gs.length + 2

def zeroOn {N : ℕ} (D : Finset (Fin N)) (x : Fin N → Bool) : Fin N → Bool :=
  fun i => if i ∈ D then false else x i

structure DeepHyp {N : ℕ} (F : (Fin N → Bool) → Bool) (D : Finset (Fin N)) : Prop where

  nc : ∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
    F (Function.update x y b) ≠ F (Function.update x' y b)

  nf : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y'

  win : ∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
    ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
      F (Function.update x' y true) = true

  mono : ∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true

  zero : F (fun _ => false) = false

def IsLit (N : ℕ) (gs : List Gate) (y : Fin N) (l : ℕ) : Prop :=
  l = (y : ℕ) ∨ ∃ pn, l = N + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩

def DFree {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (h : ℕ) : Prop :=
  ∀ y ∈ D, y ∉ (suppsFrom gs (inputSupps N)).getD h ∅

def OneReader {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) : Prop :=
  (∀ y ∈ D, ∀ p q : ℕ, Reads gs p (y : ℕ) → Reads gs q (y : ℕ) → p = q) ∧
  (∀ y ∈ D, ∀ pn : ℕ, gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ →
    ∀ p q : ℕ, Reads gs p (N + pn) → Reads gs q (N + pn) → p = q)

def Front {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (p : ℕ) (g : Gate) (y : Fin N)
    (l h : ℕ) : Prop :=
  gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    (g.inputs = [l, h] ∨ g.inputs = [h, l]) ∧ y ∈ D ∧ IsLit N gs y l ∧ DFree D gs h

def StmtFront : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o : ℕ), DeepHyp F D → D.Nonempty → Least (n + 1) F gs o → OneReader D gs →
    ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧ o ≠ n + 1 + p

def StmtWin : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    (g.op = GateOp.or → ∀ x : Fin (n + 1) → Bool, vl gs x h = true → F x = true) ∧
    (g.op = GateOp.and →
      (∀ x : Fin (n + 1) → Bool, vl gs x h = false → F x = true) ∧ n + 1 ≤ h)

def StmtTwo : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    g.op = GateOp.and → (∃ r, r ≠ p ∧ Reads gs r h) →
    ∃ (r : ℕ) (g' : Gate) (q : ℕ), r ≠ p ∧ gs[r]? = some g' ∧ g'.op = GateOp.and ∧
      (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) ∧
      ∀ t, Reads gs t h → t = p ∨ t = r

def StmtAnd : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ) (g : Gate)
    (y : Fin (n + 1)),
    Least (n + 1) F gs o →
    (∀ b : Bool, ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b)) →
    Dep F y → gs[p]? = some g → g.op = GateOp.and →
    (g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) → IsLit (n + 1) gs y l →
    ph < gs.length → (∀ t, Reads gs t (n + 1 + ph) → t = p) →
    o ≠ n + 1 + p → o ≠ n + 1 + ph →
    (l = (y : ℕ) → Drop F y false 3 gs.length) ∧
    (l ≠ (y : ℕ) → Drop F y true 4 gs.length)

def StmtExt : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧ gs.length ≤ s ∧
      (¬ OneReader D gs ∨
        ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧
          g.op = GateOp.and ∧ n + 1 ≤ h ∧ o ≠ n + 1 + p ∧ ∀ t, Reads gs t h → t = p)

def StmtML : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ y ∈ D,
      (∃ s' : ℕ, s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y false)) s') ∨
      (∃ s' : ℕ, s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y true)) s')

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

def andSwap (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) : List Gate :=
  gs.set ph ⟨GateOp.not, [(y : ℕ)]⟩

theorem andSwap_length (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) :
    (andSwap gs ph y).length = gs.length := by
  simp [andSwap]

theorem andSwap_get_ne (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (r : ℕ) (hr : r ≠ ph) :
    (andSwap gs ph y)[r]? = gs[r]? := by
  simp [andSwap, Ne.symm hr]

theorem andSwap_get_eq (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (hph : ph < gs.length) :
    (andSwap gs ph y)[ph]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
  simp [andSwap, hph]

theorem andSwap_clean {N : ℕ} (gs : List Gate) (ph : ℕ) (y : Fin N) (hcl : CleanL N gs)
    (hph : ph < gs.length) : CleanL N (andSwap gs ph y) := by
  intro r g' hr'
  by_cases hrp : r = ph
  · subst hrp
    rw [andSwap_get_eq gs r y hph] at hr'
    cases hr'
    exact Or.inl ⟨rfl, y, by omega, rfl⟩
  · rw [andSwap_get_ne gs ph y r hrp] at hr'
    exact hcl r g' hr'

theorem andSwap_agree {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (p ph l : ℕ) (g : Gate)
    (y : Fin N) (hph : ph < gs.length) (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, N + ph] ∨ g.inputs = [N + ph, l]) (hlne : l ≠ N + ph)
    (hone : ∀ t, Reads gs t (N + ph) → t = p) (x : Fin N → Bool) (hlx : vl gs x l = false) :
    ∀ w, w ≠ N + ph → vl (andSwap gs ph y) x w = vl gs x w := by
  have hcl' := andSwap_clean gs ph y hcl hph
  have hlen := andSwap_length gs ph y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwk : w < N
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      have hrp : r ≠ ph := fun e => hw (by rw [e])
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g' =>
        have hr' : (andSwap gs ph y)[r]? = some g' := by
          rw [andSwap_get_ne gs ph y r hrp]; exact hr
        rw [vl_gate _ hcl' x r g' hr', vl_gate gs hcl x r g' hr]
        by_cases hrp' : r = p
        · subst hrp'
          rw [hgp] at hr
          cases hr
          have hllt : l < N + r := (hcl r g hgp).lt l (by rcases hin with h | h <;> simp [h])
          have hl' : vl (andSwap gs ph y) x l = false := by rw [ih l hllt hlne]; exact hlx
          rw [hop]
          rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hl', hlx]
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hrp' (hone r ⟨g', hr, e ▸ ha⟩))

theorem andUpd_self {N : ℕ} (x : Fin N → Bool) (y : Fin N) (b : Bool) :
    Function.update x y b y = b := Function.update_self y b x

theorem and_core (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ)
    (g : Gate) (y : Fin (n + 1)) (L : Least (n + 1) F gs o) (b : Bool)
    (hnc : ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) (hlne : l ≠ n + 1 + ph)
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (n + 1 + ph) → t = p)
    (ho2 : o ≠ n + 1 + ph)
    (hlx : ∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = false)
    (S : Finset ℕ) (hS : ∀ q ∈ S, RC n (andSwap gs ph y) y b q) :
    Drop F y b S.card gs.length := by
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hag : ∀ x : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o = F (Function.update x y b) := by
    intro x
    rw [andSwap_agree gs L.hcl p ph l g y hph hgp hop hin hlne hone _
      (hlx _ (andUpd_self x y b)) o ho2, L.hev]
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o
        ≠ vl (andSwap gs ph y) (Function.update x' y b) o := by
    obtain ⟨x, x', h⟩ := hnc
    exact ⟨x, x', by rw [hag, hag]; exact h⟩
  obtain ⟨s', hs', hc⟩ := save n (fun x => vl (andSwap gs ph y) x o) (andSwap gs ph y) o hcl'
    (fun _ => rfl) y b hnc' S hS
  refine ⟨s', by rw [andSwap_length] at hs'; exact hs', ?_⟩
  have e : (fun x : Fin (n + 1) → Bool => F (Function.update x y b))
      = fun x => (fun x => vl (andSwap gs ph y) x o) (Function.update x y b) := by
    funext x
    exact (hag x).symm
  rw [e]
  exact hc

theorem stmtAnd : StmtAnd := by
  intro n F gs o p ph l g y L hnc _hdep hgp hop hin hlit hph hone ho1 ho2
  have hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', h⟩ := hnc false
    exact ⟨_, _, h⟩
  have hlmem : l ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hhmem : n + 1 + ph ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hphp : n + 1 + ph < n + 1 + p := (L.hcl p g hgp).lt _ hhmem
  have hllt : l < n + 1 + p := (L.hcl p g hgp).lt _ hlmem
  have hlne : l ≠ n + 1 + ph := by
    intro e
    apply L.no_alias hfnc p hp (n + 1 + ph) hphp
    intro u
    rw [vl_gate gs L.hcl u p g hgp, hop]
    rcases hin with h | h <;> rw [h, ← e] <;> simp [GateOp.eval]
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hgp' : (andSwap gs ph y)[p]? = some g := by
    rw [andSwap_get_ne gs ph y p (by omega)]; exact hgp
  obtain ⟨S, hpS, hSr⟩ := L.live hfnc p hp ho1
  have hSr' : Reads (andSwap gs ph y) S (n + 1 + p) := by
    obtain ⟨g', hg', hm⟩ := hSr
    exact ⟨g', by rw [andSwap_get_ne gs ph y S (by omega)]; exact hg', hm⟩
  have hphR : Reads (andSwap gs ph y) ph y := ⟨_, andSwap_get_eq gs ph y hph, by simp⟩
  have hpR : Reads (andSwap gs ph y) p l := ⟨g, hgp', hlmem⟩
  refine ⟨fun hly => ?_, fun hly => ?_⟩
  ·
    subst hly
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = false → vl gs x y = false := by
      intro x hx
      rw [vl_input gs x y y.isLt]
      exact hx
    have hcp : IsC n (andSwap gs ph y) y false (n + 1 + p) :=
      isC_reader hcl' y p g hgp' hlmem false (Or.inr (by simp [fixBit, hop]))
    have h3 := and_core n F gs o p ph y g y L false (hnc false) hgp hop hin hlne hph hone ho2 hlx
      {ph, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact rc_input false hphR
        · exact rc_input false hpR
        · exact rc_of_reads hSr' hcp)
    rwa [Finset.card_eq_three.2 ⟨ph, p, S, by omega, by omega, by omega, rfl⟩] at h3
  ·
    rcases hlit with e | ⟨pn, rfl, hpn⟩
    · exact absurd e hly
    have hpnp : pn < p := by omega
    have hpnph : pn ≠ ph := fun e => hlne (by rw [e])
    have hpn' : (andSwap gs ph y)[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
      rw [andSwap_get_ne gs ph y pn hpnph]; exact hpn
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = true → vl gs x (n + 1 + pn) = false := by
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn (y : ℕ) rfl rfl, vl_input gs x y y.isLt]
      simp [hx]
    have hpnR : Reads (andSwap gs ph y) pn y := ⟨_, hpn', by simp⟩
    obtain ⟨c, hc⟩ := isC_reader hcl' y pn _ hpn' (by simp) true (Or.inl rfl)
    have hc0 : c = false := by
      have h1 := st_val_const n _ hcl' y true _ c hc (fun _ => false)
      rw [vl_not _ hcl' _ pn _ hpn' (y : ℕ) rfl rfl, vl_input _ _ y y.isLt] at h1
      simp [ins] at h1
      exact h1
    subst hc0
    have hcp : IsC n (andSwap gs ph y) y true (n + 1 + p) :=
      const_read n _ hcl' y true p g hgp' (n + 1 + pn) hlmem (by simp [hc, fixBit, hop])
    have h4 := and_core n F gs o p ph (n + 1 + pn) g y L true (hnc true) hgp hop hin hlne hph
      hone ho2 hlx {ph, pn, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact rc_input true hphR
        · exact rc_input true hpnR
        · exact rc_of_reads hpR ⟨false, hc⟩
        · exact rc_of_reads hSr' hcp)
    have hcard : ({ph, pn, p, S} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨pn, p, S, by omega, by omega, by omega, rfl⟩]
    rwa [hcard] at h4

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.Exchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

theorem elim_prefix (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ t : List Gate, (elim n gs acc).2 = acc.2 ++ t := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList ++ t, ?_⟩
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ht]
    simp [elimStep]

def startStats (m h : ℕ) : List Stat :=
  (List.range m).map fun i => if i = h then Stat.const true else Stat.wire i

theorem startStats_getD (m h i : ℕ) :
    (startStats m h).getD i (Stat.const false) =
      if i < m then (if i = h then Stat.const true else Stat.wire i) else Stat.const false := by
  unfold startStats
  by_cases hi : i < m
  · simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]

theorem inv_start (n h : ℕ) (pre : List Gate) (y : List Bool) (hy : y.length = n)
    (hh : (wiresFrom pre y).getD h false = true) :
    Inv n y (wiresFrom pre y) (startStats (n + pre.length) h, pre) := by
  have lw : (wiresFrom pre y).length = n + pre.length := by rw [length_wiresFrom, hy]
  refine ⟨by simp [startStats, lw], ?_⟩
  intro i
  rw [startStats_getD]
  by_cases hi : i < n + pre.length
  · by_cases hih : i = h
    · subst hih; simp only [hi, ite_true]; exact ⟨trivial, hh.symm⟩
    · simp only [hi, hih, ite_true, ite_false]; exact ⟨hi, rfl⟩
  · simp only [hi, ite_false]
    exact ⟨trivial, by rw [List.getD_eq_default _ _ (by omega)]; rfl⟩

end PEqualNP.MetaComplexity.Exchange

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem exch_startStats_length (m h : ℕ) : (Exchange.startStats m h).length = m := by
  simp [Exchange.startStats]

theorem exch_clean_take (N k : ℕ) (gs : List Gate) (hcl : CleanL N gs) :
    CleanL N (gs.take k) := by
  intro p g hp
  rw [List.getElem?_take] at hp
  by_cases hpk : p < k
  · rw [if_pos hpk] at hp; exact hcl p g hp
  · rw [if_neg hpk] at hp; cases hp

theorem exch_const_reader (N : ℕ) (post : List Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ post, NOk g) (h q : ℕ) (g : Gate) (hq : post[q]? = some g)
    (hop : g.op = GateOp.or ∨ g.op = GateOp.not) (hh : h ∈ g.inputs) (hlt : h < acc.1.length)
    (hst : acc.1.getD h (Stat.const false) = Stat.const true) :
    ∃ c, (elim N post acc).1.getD (acc.1.length + q) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post', rfl, rfl⟩ := split_at post q g hq
  rw [elim_split_getD N pre g post' acc _ _ (le_refl _)]
  have hgok : NOk g := hok g (by simp)
  have hl : (elim N pre acc).1.length = acc.1.length + pre.length := elim_fst_len N pre acc
  simp only [elimStep]
  rw [getD_snoc_len _ _ _ _ hl]
  apply simplify_const _ _ _ hgok.1.1 (by simpa using hgok.1.2)
    (fun h' => by simpa using hgok.2 h') true
  · intro h'; rcases hop with h2 | h2 <;> rw [h2] at h' <;> cases h'
  · intro _; rfl
  · refine List.mem_map.2 ⟨h, hh, ?_⟩
    rw [elim_getD N h _ pre acc hlt]; exact hst

theorem stmtExch : StmtExch := by
  intro N F gs o h T hcl hev hnc hcov hT
  have hyl : ∀ x : Fin N → Bool, (List.ofFn x).length = N := by simp

  have hnotT : ¬ ∀ x : Fin N → Bool, F x = true := by
    intro hT'
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (by rw [hT' x, hT' y])
  have hex : ∃ x0 : Fin N → Bool, vl gs x0 h = true := by
    by_contra hne
    push Not at hne
    exact hnotT fun x => hcov x (by simpa using hne x)
  obtain ⟨x0, hx0⟩ := hex
  have hhs : h < N + gs.length := by
    by_contra hlt
    rw [vl_beyond gs x0 h (by omega)] at hx0
    cases hx0
  set k := h + 1 - N with hk
  have hks : k ≤ gs.length := by omega
  have hhk : h < N + k := by omega
  set pre := gs.take k with hpre
  set post := gs.drop k with hpost
  have hlpre : pre.length = k := by simp [hpre]; omega
  have hlpost : post.length = gs.length - k := by simp [hpost]
  have hnok : ∀ g ∈ gs, NOk g := clean_nok N gs hcl
  have hnokpost : ∀ g ∈ post, NOk g := fun g hg => hnok g (List.mem_of_mem_drop hg)
  have hclpre : CleanL N pre := exch_clean_take N k gs hcl
  have hwg : ∀ y : List Bool, wiresFrom gs y = wiresFrom post (wiresFrom pre y) := by
    intro y
    rw [← wiresFrom_append, hpre, hpost, List.take_append_drop]
  have hwh : ∀ x : Fin N → Bool, vl gs x h = (wiresFrom pre (List.ofFn x)).getD h false := by
    intro x
    show (wiresFrom gs (List.ofFn x)).getD h false = _
    rw [hwg, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]

  set acc0 : List Stat × List Gate := (Exchange.startStats (N + pre.length) h, pre) with hacc0
  have hl0 : acc0.1.length = N + k := by
    rw [hacc0, exch_startStats_length, hlpre]
  set acc := elim N post acc0 with hacc
  have hinv : ∀ x : Fin N → Bool, vl gs x h = true →
      Inv N (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc := by
    intro x hx
    rw [hwg, hacc]
    exact inv_elim N _ (hyl x) post _ _ (fun g hg => (hnokpost g hg).1)
      (Exchange.inv_start N h pre _ (hyl x) (by rw [← hwh]; exact hx))
  obtain ⟨tl, htl⟩ := Exchange.elim_prefix N post acc0
  rw [← hacc] at htl
  have hLk : acc.2.length = k + tl.length := by rw [htl]; simp [hacc0, hlpre]
  have hclacc : CleanL N acc.2 :=
    clean_elim N (List.ofFn x0) (hyl x0) post _ _ (fun g hg => (hnokpost g hg).1)
      (Exchange.inv_start N h pre _ (hyl x0) (by rw [← hwh]; exact hx0)) hclpre

  have hsth0 : acc0.1.getD h (Stat.const false) = Stat.const true := by
    rw [hacc0, Exchange.startStats_getD]; simp [hlpre, hhk]
  have hsth : acc.1.getD h (Stat.const false) = Stat.const true := by
    rw [hacc, elim_getD N h _ post acc0 (by omega)]; exact hsth0

  have hTk : ∀ t ∈ T, k ≤ t := by
    intro t ht
    rcases hT t ht with hr | ⟨r, g, _, _, hrh, htr⟩
    · have := reads_lt hcl hr; omega
    · have := reads_lt hcl hrh; have := reads_lt hcl htr; omega

  have hcount := Helpers.elim_count N acc0 post hnokpost (T.image fun t => t - k) (by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hp
    have htk := hTk t ht
    have hpt : post[t - k]? = gs[t]? := by
      rw [hpost, List.getElem?_drop]; congr 1; omega
    rcases hT t ht with ⟨g, hg, hhg⟩ | ⟨r, g', hg', hop, hrh, ⟨g, hg, hrg⟩⟩
    · refine ⟨g, by rw [hpt]; exact hg, h, hhg, ?_, true, ?_⟩
      · have := (hcl t g hg).lt h hhg; omega
      · rw [← hacc]; exact hsth
    · refine ⟨g, by rw [hpt]; exact hg, N + r, hrg, ?_, ?_⟩
      · have := (hcl t g hg).lt _ hrg; omega
      · have hrk : k ≤ r := by have := reads_lt hcl hrh; omega
        obtain ⟨g'', hg'', hhg''⟩ := hrh
        rw [hg'] at hg''
        cases hg''
        have hpr : post[r - k]? = some g' := by
          rw [hpost, List.getElem?_drop]
          have e : k + (r - k) = r := by omega
          rw [e]; exact hg'
        obtain ⟨c, hc⟩ := exch_const_reader N post acc0 hnokpost h (r - k) g' hpr hop hhg''
          (by omega) hsth0
        refine ⟨c, ?_⟩
        have e : acc0.1.length + (r - k) = N + r := by omega
        rw [e] at hc; exact hc)
  have hcard : (T.image fun t => t - k).card = T.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have := hTk a ha; have := hTk b hb
    simp only at hab; omega
  rw [hcard, ← hacc] at hcount
  have hsize : acc.2.length + T.card ≤ gs.length := by
    have : acc0.2.length = k := by simp [hacc0, hlpre]
    omega

  have hwhA : ∀ x : Fin N → Bool, (wiresFrom acc.2 (List.ofFn x)).getD h false = vl gs x h := by
    intro x
    rw [htl, wiresFrom_append, hwh, getD_wiresFrom _ _ _ (by
      rw [length_wiresFrom, hyl]; simp [hacc0, hlpre]; exact hhk)]
  have hval : ∀ x : Fin N → Bool, vl gs x h = true →
      (acc.1.getD o (Stat.const false)).val (wiresFrom acc.2 (List.ofFn x)) = F x := by
    intro x hx
    rw [((hinv x hx).2 o).2, ← hev x]; rfl
  have hvalid : (acc.1.getD o (Stat.const false)).Valid (N + acc.2.length) :=
    ((hinv x0 hx0).2 o).1
  cases hst : acc.1.getD o (Stat.const false) with
  | const c =>
    cases c with
    | true =>
      exfalso
      apply hnotT
      intro x
      by_cases hx : vl gs x h = true
      · rw [← hval x hx, hst]; rfl
      · exact hcov x (by simpa using hx)
    | false =>

      refine ⟨pre ++ [⟨GateOp.not, [h]⟩], N + k, ?_, ?_, ?_⟩
      · intro p g hp
        by_cases hlt : p < pre.length
        · rw [List.getElem?_append_left hlt] at hp; exact hclpre p g hp
        · rw [List.getElem?_append_right (by omega)] at hp
          have hp0 : p - pre.length = 0 := by
            by_contra hne
            rw [List.getElem?_singleton, if_neg hne] at hp; cases hp
          rw [hp0, List.getElem?_singleton, if_pos rfl] at hp
          cases hp
          have hpl : p = k := by omega
          rw [hpl]
          exact Or.inl ⟨rfl, h, by omega, rfl⟩
      · intro x
        show (wiresFrom (pre ++ [⟨GateOp.not, [h]⟩]) (List.ofFn x)).getD (N + k) false = _
        rw [wiresFrom_append]
        have hl : (wiresFrom pre (List.ofFn x)).length = N + k := by
          rw [length_wiresFrom, hyl, hlpre]
        show ((wiresFrom pre (List.ofFn x)) ++ [GateOp.not.eval
          ([h].map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]).getD (N + k) false = _
        rw [getD_snoc_len _ _ _ _ hl]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
        rw [← hwh]
        by_cases hx : vl gs x h = true
        · rw [hx, ← hval x hx, hst]; rfl
        · rw [hcov x (by simpa using hx)]; simpa using hx
      · simp only [List.length_append, List.length_cons, List.length_nil, hlpre]
        omega
  | wire j =>
    rw [hst] at hvalid
    have hj : j < N + acc.2.length := hvalid
    set L := acc.2.length with hL
    refine ⟨acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, N + L]⟩], N + L + 1, ?_, ?_, ?_⟩
    · intro p g hp
      by_cases hlt : p < L
      · rw [List.getElem?_append_left hlt] at hp; exact hclacc p g hp
      · rw [List.getElem?_append_right (by omega)] at hp
        by_cases h0 : p - L = 0
        · rw [h0] at hp
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          subst hp
          have hpl : p = L := by omega
          rw [hpl]
          exact Or.inl ⟨rfl, h, by omega, rfl⟩
        · by_cases h1 : p - L = 1
          · rw [h1] at hp
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] at hp
            subst hp
            have hpl : p = L + 1 := by omega
            rw [hpl]
            exact Or.inr ⟨Or.inr rfl, j, N + L, by omega, by omega, rfl⟩
          · obtain ⟨d, hd⟩ : ∃ d, p - L = d + 2 := ⟨p - L - 2, by omega⟩
            rw [hd] at hp
            simp at hp
    · intro x
      show (wiresFrom (acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, N + L]⟩])
        (List.ofFn x)).getD (N + L + 1) false = _
      rw [wiresFrom_append]
      set W := wiresFrom acc.2 (List.ofFn x) with hW
      have hl : W.length = N + L := by rw [hW, length_wiresFrom, hyl]
      set W' := W ++ [GateOp.not.eval ([h].map fun i => W.getD i false)] with hW'
      have hl' : W'.length = N + L + 1 := by simp [hW', hl]
      show (W' ++ [GateOp.or.eval ([j, N + L].map fun i => W'.getD i false)]).getD
        (N + L + 1) false = _
      rw [getD_snoc_len _ _ _ _ hl']
      have e1 : W'.getD j false = W.getD j false := List.getD_append _ _ _ _ (by omega)
      have e2 : W'.getD (N + L) false = !(W.getD h false) := by
        rw [hW', getD_snoc_len _ _ _ _ hl]; simp [GateOp.eval]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id, Bool.or_false, e1, e2]
      rw [hW, hwhA]
      by_cases hx : vl gs x h = true
      · rw [hx, ← hval x hx, hst]; simp [Stat.val]
      · have hx' : vl gs x h = false := by simpa using hx
        rw [hcov x hx', hx']; simp
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem rdel_length (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) :
    (rdel N p a gs).length + 1 = gs.length := by
  simp [rdel]; omega

theorem rdel_get_lt (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : j < p) :
    (rdel N p a gs)[j]? = gs[j]? := by
  unfold rdel
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj]

theorem rdel_get_ge (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : p ≤ j) :
    (rdel N p a gs)[j]? =
      (gs[j + 1]?).map fun g => (⟨g.op, g.inputs.map (rd N p a)⟩ : Gate) := by
  unfold rdel
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega

theorem vl_append_lt {N : ℕ} (gs gs' : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : w < N + gs.length) : vl (gs ++ gs') x w = vl gs x w := by
  unfold vl
  rw [wiresFrom_append, getD_wiresFrom _ _ w (by rw [length_wiresFrom]; simp; omega)]

theorem rd_lt (N p a w : ℕ) (hw : w < N + p) : rd N p a w = w := by
  simp [rd, hw]

theorem rd_eq (N p a : ℕ) : rd N p a (N + p) = a := by
  simp [rd]

theorem rd_gt (N p a w : ℕ) (hw : N + p < w) : rd N p a w = w - 1 := by
  unfold rd
  split_ifs <;> omega

theorem rdel_clean (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) : CleanL N (rdel N p a gs) := by
  intro j g hj
  by_cases hjp : j < p
  · rw [rdel_get_lt N p a gs hp j hjp] at hj
    exact hcl j g hj
  · rw [rdel_get_ge N p a gs hp j (by omega)] at hj
    obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hj
    have hc := hcl (j + 1) g0 hg0
    have hmap : ∀ i, i < N + (j + 1) → rd N p a i < N + j := by
      intro i hi
      unfold rd
      split_ifs <;> omega
    rcases hc with ⟨h1, i, hi, h2⟩ | ⟨h1, i, k, hi, hk, h2⟩
    · exact Or.inl ⟨h1, rd N p a i, hmap i hi, by simp [h2]⟩
    · exact Or.inr ⟨h1, rd N p a i, rd N p a k, hmap i hi, hmap k hk, by simp [h2]⟩

theorem rdel_prefix (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) :
    ∀ w : ℕ, w < N + p → vl (rdel N p a gs) x w = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwN : w < N
    · rw [vl_input _ x w hwN, vl_input _ x w hwN]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < p := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem (by omega)⟩
      have hg' : (rdel N p a gs)[j]? = some g := by rw [rdel_get_lt N p a gs hp j hj, hg]
      rw [vl_gate _ hcl' x j g hg', vl_gate _ hcl x j g hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i ((hcl j g hg).lt i hi) (by have := (hcl j g hg).lt i hi; omega)

theorem rdel_all (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) (hx : vl gs x (N + p) = vl gs x a) :
    ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  have hlen := rdel_length N p a gs hp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases lt_trichotomy w (N + p) with hw | rfl | hw
    · rw [rd_lt N p a w hw]
      exact rdel_prefix N p a gs hcl hp ha x w hw
    · rw [rd_eq, hx]
      exact rdel_prefix N p a gs hcl hp ha x a ha
    · rw [rd_gt N p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = N + (j + 1) := ⟨w - N - 1, by omega⟩
      have e : N + (j + 1) - 1 = N + j := by omega
      rw [e]
      by_cases hjl : j + 1 < gs.length
      · obtain ⟨g, hg⟩ : ∃ g, gs[j + 1]? = some g := ⟨gs[j + 1], List.getElem?_eq_getElem hjl⟩
        have hg' : (rdel N p a gs)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
          rw [rdel_get_ge N p a gs hp j (by omega), hg]; rfl
        rw [vl_gate _ hcl' x j _ hg', vl_gate _ hcl x (j + 1) g hg]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i ((hcl (j + 1) g hg).lt i hi)
      · rw [vl_beyond _ x _ (by omega), vl_beyond _ x _ (by omega)]

theorem TailGE.zero (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) : TailGE N F gs 0 :=
  ⟨Nat.zero_le _, fun j h1 h2 => absurd h2 (by omega)⟩

theorem TailGE.le {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t : ℕ}
    (h : TailGE N F gs t) : t ≤ gs.length := h.1

theorem TailGE.lt_of_not {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t p : ℕ}
    (h : TailGE N F gs t) (hp : p < gs.length) (hn : ¬ TailOK N F gs p) : p + t < gs.length := by
  by_contra hc
  exact hn (h.2 p (by omega) hp)

theorem tailGE_rdel_app (N : ℕ) (F : (Fin N → Bool) → Bool) (gs new : List Gate) (p a t : ℕ)
    (S : (Fin N → Bool) → Prop) (hcl : CleanL N gs) (hp : p < gs.length) (ha : a < N + p)
    (ht : TailGE N F gs t) (hpt : p + t < gs.length)
    (hS : ∀ x, S x → vl gs x (N + p) = vl gs x a) (hF : ∀ x, ¬ S x → F x = true)
    (hnew : ∀ i, i < new.length → TailOK N F (rdel N p a gs ++ new) (gs.length - 1 + i)) :
    TailGE N F (rdel N p a gs ++ new) (t + new.length) := by
  have hlen := rdel_length N p a gs hp
  have hl' : (rdel N p a gs ++ new).length = gs.length - 1 + new.length := by
    simp; omega
  refine ⟨by rw [hl']; omega, ?_⟩
  intro j h1 h2
  rw [hl'] at h1 h2
  by_cases hj : gs.length - 1 ≤ j
  · have := hnew (j - (gs.length - 1)) (by omega)
    rwa [show gs.length - 1 + (j - (gs.length - 1)) = j by omega] at this
  · have hok := ht.2 (j + 1) (by omega) (by omega)
    obtain ⟨g, hg, hop⟩ := hok
    have hj' : (rdel N p a gs ++ new)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
      rw [List.getElem?_append_left (by omega), rdel_get_ge N p a gs hp j (by omega), hg]; rfl
    refine ⟨_, hj', ?_⟩
    rcases hop with hop | ⟨hop, hbel⟩
    · exact Or.inl hop
    · refine Or.inr ⟨hop, fun x hx => ?_⟩
      by_cases hSx : S x
      · apply hbel x
        rw [← rdel_all N p a gs hcl hp ha x (hS x hSx) (N + (j + 1)),
          rd_gt N p a _ (by omega), show N + (j + 1) - 1 = N + j by omega,
          ← vl_append_lt (rdel N p a gs) new x (N + j) (by omega)]
        exact hx
      · exact hF x hSx

theorem least_of {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs0 : List Gate} {o o0 : ℕ}
    (h0 : Least N F gs0 o0) (hcl : CleanL N gs) (hev : ∀ x, vl gs x o = F x)
    (hle : gs.length ≤ gs0.length) : Least N F gs o :=
  ⟨hcl, hev, fun gs' o' hc he => le_trans hle (h0.hmin gs' o' hc he)⟩

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem deepHyp_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp F D) (hne : D.Nonempty) : ∃ x y : Fin N → Bool, F x ≠ F y := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, x', h⟩ := hD.nc y hy false
  exact ⟨_, _, h⟩

theorem deepHyp_dep {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp F D) {y : Fin N} (hy : y ∈ D) : Dep F y := by
  have h0 : F (zeroOn D (fun _ => false)) = false := by
    have : zeroOn D (fun _ : Fin N => false) = fun _ => false := by
      funext i; simp [zeroOn]
    rw [this]; exact hD.zero
  obtain ⟨x', -, hx'y, hF, hF'⟩ := hD.win y hy _ h0
  refine ⟨x', ?_⟩
  rw [hx'y, hF, show (!false) = true from rfl, hF']
  simp

theorem least_len {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs' : List Gate} {o o' : ℕ}
    (L : Least N F gs o) (L' : Least N F gs' o') : gs.length = gs'.length :=
  le_antisymm (L.hmin gs' o' L'.hcl L'.hev) (L'.hmin gs o L.hcl L.hev)

theorem vl_bin {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) :
    (g.op = GateOp.or → vl gs x (N + p) = (vl gs x l || vl gs x h)) ∧
    (g.op = GateOp.and → vl gs x (N + p) = (vl gs x l && vl gs x h)) := by
  rw [vl_gate gs hcl x p g hg]
  constructor <;> intro hop <;> rw [hop] <;>
    rcases hin with e | e <;> rw [e] <;> simp [GateOp.eval, Bool.or_comm, Bool.and_comm]

theorem not_tailOK_or {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))}
    {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin (n + 1)} {l h : ℕ}
    (hD : DeepHyp F D) (L : Least (n + 1) F gs o) (hf : Front D gs p g y l h)
    (hop : g.op = GateOp.or) : ¬ TailOK (n + 1) F gs p := by
  obtain ⟨hg, -, hin, hy, hlit, -⟩ := hf
  rintro ⟨g', hg', hop' | ⟨-, hbel⟩⟩
  · rw [hg] at hg'; cases hg'; rw [hop] at hop'; cases hop'
  · rw [hg] at hg'; cases hg'

    have key : ∀ b : Bool, (∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = true) → False := by
      intro b hb
      obtain ⟨x, x', hne⟩ := hD.nc y hy b
      have : ∀ z : Fin (n + 1) → Bool, F (Function.update z y b) = true := by
        intro z
        apply hbel
        rw [(vl_bin gs L.hcl _ p l h g hg hin).1 hop, hb _ (by simp)]
        rfl
      exact hne (by rw [this, this])
    rcases hlit with rfl | ⟨pn, rfl, hpn⟩
    · apply key true
      intro x hx
      rw [vl_input gs x y y.isLt]
      simpa using hx
    · apply key false
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn y rfl rfl, vl_input gs x y y.isLt]
      simpa using hx

theorem stmtExt (hLift : StmtLift) (hX : StmtXMove) (hFront : StmtFront) (hWin : StmtWin)
    (hTwo : StmtTwo) : StmtExt := by
  classical
  intro n F D s hD hne hs
  have hnc := deepHyp_nc hD hne
  obtain ⟨gs0, o0, L0, hl0⟩ := exists_least (n + 1) F s hnc hs
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧
    TailGE (n + 1) F gs t
  have hP0 : P 0 := ⟨gs0, o0, L0, TailGE.zero _ _ _⟩

  have hbound : ∀ t, P t → t ≤ gs0.length := by
    rintro t ⟨gs, o, L, ht⟩
    exact (least_len L L0) ▸ ht.le
  set M := Nat.findGreatest P gs0.length with hM
  obtain ⟨gs, o, L, ht⟩ : P M := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ t, P t → t ≤ M := fun t h => Nat.le_findGreatest (hbound t h) h
  refine ⟨gs, o, L, by rw [least_len L L0]; exact hl0, ?_⟩
  by_contra hstop
  push Not at hstop
  obtain ⟨hone, hnoand⟩ := hstop
  obtain ⟨p, g, y, l, h, hf, hop⟩ := hFront n F D gs o hD hne L hone
  have hw := hWin n F D gs o p g y l h hD L hone hf
  obtain ⟨hg, hor, hin, -, -, -⟩ := id hf
  rcases hor with hand | hor
  ·
    obtain ⟨hbel, hhN⟩ := hw.2 hand
    obtain ⟨t, htr, htp⟩ := hnoand p g y l h hf hand hhN hop
    obtain ⟨r, g', q, hrp, hg', hand', hin', -⟩ :=
      hTwo n F D gs o p g y l h hD L hone hf hand ⟨t, htp, htr⟩
    obtain ⟨gs', o', L', ht'⟩ : P (M + 2) := by
      rcases lt_or_gt_of_ne hrp with hlt | hlt
      · obtain ⟨gs', o', L', ht'⟩ :=
          hX (n + 1) F gs o r p q l h g' g L hnc hlt hg' hand' hin' hg hand hin hbel
        exact ⟨gs', o', L', ht' M ht⟩
      · obtain ⟨gs', o', L', ht'⟩ :=
          hX (n + 1) F gs o p r l q h g g' L hnc hlt hg hand hin hg' hand' hin' hbel
        exact ⟨gs', o', L', ht' M ht⟩
    have := hmax _ ⟨gs', o', L', ht'⟩
    omega
  ·
    have hbel := hw.1 hor
    obtain ⟨L', ht'⟩ := hLift (n + 1) F gs o p l h g L hnc hg hor hin hbel
    have := hmax _ ⟨_, _, L', ht' (not_tailOK_or hD L hf hor) M ht⟩
    omega

theorem stmtML (hAnd : StmtAnd) (hExt : StmtExt) : StmtML := by
  intro n F D s hD hne hs
  have hnc := deepHyp_nc hD hne
  obtain ⟨gs, o, L, hls, halt⟩ := hExt n F D s hD hne hs
  rcases halt with hone | ⟨p, g, y, l, h, hf, hand, hhN, hop, honly⟩
  · simp only [OneReader, not_and_or] at hone
    push Not at hone
    rcases hone with ⟨y, hy, p, q, hp, hq, hpq⟩ | ⟨y, hy, pn, hpn, p, q, hp, hq, hpq⟩
    · refine ⟨y, hy, ?_⟩
      rcases L.two_readers y (hD.nc y hy) p q hpq hp hq with
        ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
      · exact Or.inl (h3.mono le_rfl hls)
      · exact Or.inl (h4.mono (by omega) hls)
      · exact Or.inr (h4.mono le_rfl hls)
    · refine ⟨y, hy, Or.inl ?_⟩
      exact (L.not_two_readers y (hD.nc y hy) pn _ hpn rfl (by simp) p q hpq hp hq).1.mono
        le_rfl hls
  · obtain ⟨hg, -, hin, hy, hlit, hfree⟩ := hf
    refine ⟨y, hy, ?_⟩
    have hrd : Reads gs p h := ⟨g, hg, by rcases hin with e | e <;> rw [e] <;> simp⟩
    have hhlt := reads_lt L.hcl hrd
    have hplt := reads_len hrd
    have hdep := deepHyp_dep hD hy

    have hoh : o ≠ h := by
      rintro rfl
      obtain ⟨x, hx⟩ := hdep
      apply hx
      rw [← L.hev, ← L.hev]
      exact (agree_wiresFrom (Function.update x y (!x y)) x gs _ _ _
        (agree_inputs _ _)).2.2 o (by
          intro k hk
          have : k ≠ y := fun e => hfree y hy (e ▸ hk)
          simp [Function.update_of_ne this])
    obtain ⟨ph, rfl⟩ : ∃ ph, h = n + 1 + ph := ⟨h - (n + 1), by omega⟩
    have hA := hAnd n F gs o p ph l g y L (hD.nc y hy) hdep hg hand hin hlit (by omega)
      honly hop hoh
    by_cases hl : l = (y : ℕ)
    · exact Or.inl ((hA.1 hl).mono le_rfl hls)
    · exact Or.inr ((hA.2 hl).mono le_rfl hls)

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem out_lt_of_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hev : ∀ x, vl gs x o = F x) (hnc : ∃ x y : Fin N → Bool, F x ≠ F y) :
    o < N + gs.length := by
  by_contra hc
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev x, ← hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]

theorem stmtLift : StmtLift := by
  intro N F gs o p l h g hle hnc hg hop hin hbel
  have hcl := hle.hcl
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hlen := rdel_length N p l gs hp
  have ho := out_lt_of_nc hle.hev hnc

  have hlh : l < N + p ∧ h < N + p := by
    rcases hcl p g hg with ⟨h1, _⟩ | ⟨_, j, k, hj, hk, h2⟩
    · rw [hop] at h1; cases h1
    · rcases hin with e | e <;> rw [e] at h2 <;> simp at h2 <;> omega
  obtain ⟨hl, hh⟩ := hlh

  have hS : ∀ x : Fin N → Bool, vl gs x h = false → vl gs x (N + p) = vl gs x l := by
    intro x hx
    rw [vl_gate _ hcl x p g hg, hop]
    rcases hin with e | e <;> rw [e] <;> simp [hx, GateOp.eval]
  have hro : rd N p l o < N + (gs.length - 1) := by
    unfold rd; split_ifs <;> omega
  set gs2 := rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩] with hgs2
  have hcl' := rdel_clean N p l gs hcl hp hl
  have hcl2 : CleanL N gs2 := by
    intro j g' hj
    by_cases hj' : j < (rdel N p l gs).length
    · rw [hgs2, List.getElem?_append_left hj'] at hj
      exact hcl' j g' hj
    · rw [hgs2, List.getElem?_append_right (by omega)] at hj
      obtain ⟨e1, e2⟩ := List.getElem?_eq_some_iff.1 hj
      simp at e1
      have ej : j = (rdel N p l gs).length := by omega
      subst ej
      simp at e2
      subst e2
      exact Or.inr ⟨Or.inr rfl, rd N p l o, h, by omega, by omega, rfl⟩
  have hlast : (gs2)[gs.length - 1]? = some ⟨GateOp.or, [rd N p l o, h]⟩ := by
    rw [hgs2, List.getElem?_append_right (by omega)]
    rw [show gs.length - 1 - (rdel N p l gs).length = 0 by omega]; rfl
  have hval : ∀ x : Fin N → Bool, vl gs2 x (N + (gs.length - 1)) = F x := by
    intro x
    rw [vl_gate _ hcl2 x _ _ hlast]
    have e1 : vl gs2 x (rd N p l o) = vl (rdel N p l gs) x (rd N p l o) :=
      vl_append_lt _ _ x _ (by omega)
    have e2 : vl gs2 x h = vl gs x h := by
      rw [vl_append_lt _ _ x _ (by omega), rdel_prefix N p l gs hcl hp hl x h hh]
    simp only [List.map, GateOp.eval, e1, e2]
    cases hx : vl gs x h
    · rw [rdel_all N p l gs hcl hp hl x (hS x hx) o, hle.hev x]; simp
    · rw [hbel x hx]; simp
  refine ⟨least_of hle hcl2 hval (by simp [hgs2]; omega), ?_⟩
  intro hnt t ht
  have hpt := ht.lt_of_not hp hnt
  have := tailGE_rdel_app N F gs [⟨GateOp.or, [rd N p l o, h]⟩] p l t
    (fun x : Fin N → Bool => vl gs x h = false) hcl hp hl ht hpt hS
    (fun x hx => hbel x (by simpa using hx)) ?_
  · simpa using this
  · intro i hi
    simp at hi
    subst hi
    refine ⟨_, by simpa using hlast, Or.inr ⟨rfl, fun x hx => ?_⟩⟩
    rw [← hval x]; simpa using hx

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem not_tailOK_and {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {j : ℕ} {g : Gate}
    (hg : gs[j]? = some g) (hop : g.op = GateOp.and) : ¬ TailOK N F gs j := by
  rintro ⟨g0, hg0, h | ⟨h, _⟩⟩ <;>
  · rw [hg] at hg0
    cases hg0
    rw [hop] at h
    cases h

theorem vl_and_true {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) (hx : vl gs x h = true) :
    vl gs x (N + p) = vl gs x l := by
  rw [vl_gate gs hcl x p g hg, hop]
  rcases hin with hi | hi <;> rw [hi] <;> simp [GateOp.eval, hx]

theorem stmtXMove : StmtXMove := by
  intro N F gs o p p' l q h g g' hL hnc hpp hg hop hin hg' hop' hin' hbel
  have hcl := hL.hcl
  have hp's : p' < gs.length := (List.getElem?_eq_some_iff.1 hg').1
  have hl : l < N + p := (hcl p g hg).lt l (by rcases hin with hi | hi <;> simp [hi])
  have hh : h < N + p := (hcl p g hg).lt h (by rcases hin with hi | hi <;> simp [hi])
  have hq : q < N + p' := (hcl p' g' hg').lt q (by rcases hin' with hi | hi <;> simp [hi])
  have ho : o < N + gs.length := by
    by_contra hc
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hL.hev x, ← hL.hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]

  have hcl1 := rdel_clean N p' q gs hcl hp's hq
  have hlen1 := rdel_length N p' q gs hp's
  have hp1 : p < (rdel N p' q gs).length := by omega
  have hg1 : (rdel N p' q gs)[p]? = some g := by rw [rdel_get_lt N p' q gs hp's p hpp, hg]

  have hcl2 := rdel_clean N p l (rdel N p' q gs) hcl1 hp1 hl
  have hlen2 := rdel_length N p l (rdel N p' q gs) hp1
  have ho2 : rd N p l (rd N p' q o) < N + (rdel N p l (rdel N p' q gs)).length := by
    unfold rd
    split_ifs <;> omega
  have hh2 : h < N + (rdel N p l (rdel N p' q gs)).length := by omega

  have hgood : ∀ x : Fin N → Bool, vl gs x h = true →
      vl (rdel N p l (rdel N p' q gs)) x (rd N p l (rd N p' q o)) = F x ∧
      vl (rdel N p l (rdel N p' q gs)) x h = true := by
    intro x hx
    have hx1 := vl_and_true gs hcl x p' q h g' hg' hop' hin' hx
    have hx2 : vl (rdel N p' q gs) x (N + p) = vl (rdel N p' q gs) x l := by
      rw [rdel_prefix N p' q gs hcl hp's hq x (N + p) (by omega),
        rdel_prefix N p' q gs hcl hp's hq x l (by omega)]
      exact vl_and_true gs hcl x p l h g hg hop hin hx
    refine ⟨?_, ?_⟩
    · rw [rdel_all N p l _ hcl1 hp1 hl x hx2, rdel_all N p' q gs hcl hp's hq x hx1, hL.hev x]
    · rw [rdel_prefix N p l _ hcl1 hp1 hl x h hh,
        rdel_prefix N p' q gs hcl hp's hq x h (by omega), hx]

  set gs2 := rdel N p l (rdel N p' q gs) with hgs2
  set o2 := rd N p l (rd N p' q o) with ho2def
  set new : List Gate := [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [o2, N + gs2.length]⟩] with hnew
  have hget0 : (gs2 ++ new)[gs2.length]? = some ⟨GateOp.not, [h]⟩ := by simp [hnew]
  have hget1 : (gs2 ++ new)[gs2.length + 1]? = some ⟨GateOp.or, [o2, N + gs2.length]⟩ := by
    simp [hnew]
  have hclA : CleanL N (gs2 ++ new) := by
    intro j g0 hj
    by_cases hj2 : j < gs2.length
    · rw [List.getElem?_append_left hj2] at hj
      exact hcl2 j g0 hj
    · rw [List.getElem?_append_right (by omega)] at hj
      have hjl : j - gs2.length < 2 := by
        have := (List.getElem?_eq_some_iff.1 hj).1
        simpa [hnew] using this
      rcases (by omega : j - gs2.length = 0 ∨ j - gs2.length = 1) with e | e
      · rw [e] at hj
        simp [hnew] at hj
        subst hj
        exact Or.inl ⟨rfl, h, by omega, rfl⟩
      · rw [e] at hj
        simp [hnew] at hj
        subst hj
        exact Or.inr ⟨Or.inr rfl, o2, N + gs2.length, by omega, by omega, rfl⟩
  have hvtop : ∀ x : Fin N → Bool, vl (gs2 ++ new) x (N + (gs2.length + 1)) = F x := by
    intro x
    have h0 : vl (gs2 ++ new) x (N + gs2.length) = !vl gs2 x h := by
      rw [vl_gate _ hclA x _ _ hget0]
      simp [GateOp.eval, vl_append_lt gs2 new x h hh2]
    rw [vl_gate _ hclA x _ _ hget1]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [h0, vl_append_lt gs2 new x o2 ho2]
    by_cases hx : vl gs x h = true
    · obtain ⟨e1, e2⟩ := hgood x hx
      rw [e1, e2]
      simp
    · have hF := hbel x (by simpa using hx)
      have e2 : vl gs2 x h = vl gs x h := by
        rw [hgs2, rdel_prefix N p l _ hcl1 hp1 hl x h hh,
          rdel_prefix N p' q gs hcl hp's hq x h (by omega)]
      rw [hF, e2]
      simp [hx]
  have hlenA : (gs2 ++ new).length = gs.length := by simp [hnew]; omega
  refine ⟨gs2 ++ new, N + (gs2.length + 1),
    least_of hL hclA hvtop (le_of_eq hlenA), ?_⟩
  intro t ht
  have hpt' : p' + t < gs.length := ht.lt_of_not hp's (not_tailOK_and hg' hop')
  have hF : ∀ x : Fin N → Bool, ¬ (vl gs x h = true) → F x = true :=
    fun x hx => hbel x (by simpa using hx)
  have ht1 : TailGE N F (rdel N p' q gs) t := by
    have := tailGE_rdel_app N F gs [] p' q t (fun x => vl gs x h = true) hcl hp's hq ht hpt'
      (fun x hx => vl_and_true gs hcl x p' q h g' hg' hop' hin' hx) hF
      (fun i hi => absurd hi (by simp))
    simpa using this
  have hS2 : ∀ x : Fin N → Bool, vl gs x h = true →
      vl (rdel N p' q gs) x (N + p) = vl (rdel N p' q gs) x l := by
    intro x hx
    rw [rdel_prefix N p' q gs hcl hp's hq x (N + p) (by omega),
      rdel_prefix N p' q gs hcl hp's hq x l (by omega)]
    exact vl_and_true gs hcl x p l h g hg hop hin hx
  have hlen2' : gs2.length = (rdel N p' q gs).length - 1 := by omega
  have := tailGE_rdel_app N F (rdel N p' q gs) new p l t (fun x => vl gs x h = true) hcl1 hp1 hl
    ht1 (by omega) hS2 hF (by
      intro i hi
      have hi2 : i < 2 := by simpa [hnew] using hi
      rw [← hlen2']
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact ⟨_, by simpa using hget0, Or.inl rfl⟩
      · refine ⟨_, hget1, Or.inr ⟨rfl, fun x hx => ?_⟩⟩
        rw [show N + (gs2.length + 1) = N + (gs2.length + 1) from rfl, hvtop x] at hx
        exact hx)
  simpa [hnew] using this

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem vl_dfree {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {h : ℕ} (hD : DFree D gs h)
    (u u' : Fin N → Bool) (hu : ∀ i, i ∉ D → u i = u' i) : vl gs u h = vl gs u' h := by
  unfold vl
  exact (agree_wiresFrom u u' gs _ _ _ (agree_inputs _ _)).2.2 h (fun i hi =>
    hu i (fun hiD => hD i hiD hi))

theorem out_ne_lit {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL N gs) (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (y : Fin N)
    (hnc : ∀ b : Bool, ∃ x x' : Fin N → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (l : ℕ) (hl : IsLit N gs y l) : o ≠ l := by
  intro e
  subst e
  obtain ⟨x, x', hne⟩ := hnc false
  apply hne
  rw [← hev, ← hev]
  rcases hl with e | ⟨pn, e, hpn⟩
  · rw [e, vl_input _ _ _ y.isLt, vl_input _ _ _ y.isLt]
    simp
  · rw [e, vl_not gs hcl _ pn _ hpn (y : ℕ) rfl rfl, vl_not gs hcl _ pn _ hpn (y : ℕ) rfl rfl,
      vl_input _ _ _ y.isLt, vl_input _ _ _ y.isLt]
    simp

theorem win_core {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)} {gs : List Gate}
    {o p : ℕ} {g : Gate} {y : Fin N} {l h : ℕ} (H : DeepHyp F D) (hcl : CleanL N gs)
    (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (hO : OneReader D gs)
    (hF : Front D gs p g y l h) : ∀ x : Fin N → Bool, vl gs x h = fixBit g → F x = true := by
  obtain ⟨hp, hop, hin, hy, hl, hD⟩ := hF
  intro x hx
  cases hFx : F x with
  | true => rfl
  | false =>
  exfalso
  have hz : F (zeroOn D x) = false := by
    cases e : F (zeroOn D x) with
    | false => rfl
    | true => rw [H.mono x e] at hFx; cases hFx
  obtain ⟨x', hx'D, _, hF0, hF1⟩ := H.win y hy x hz
  have hagr : ∀ i, i ∉ D → x i = Function.update x' y true i := by
    intro i hi
    have hiy : i ≠ y := fun e => hi (e ▸ hy)
    rw [Function.update_of_ne hiy, hx'D i hi]
  have hagr' : ∀ i, i ∉ D → x i = x' i := fun i hi => (hx'D i hi).symm
  have hlmem : l ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hc1 : vl gs x' (N + p) = fixBit g :=
    vl_abs gs hcl x' p g hp hop h hhmem (by rw [← vl_dfree hD x x' hagr']; exact hx)
  have hc2 : vl gs (Function.update x' y true) (N + p) = fixBit g :=
    vl_abs gs hcl _ p g hp hop h hhmem (by rw [← vl_dfree hD x _ hagr]; exact hx)
  have hol : o ≠ l := out_ne_lit hcl hev y (H.nc y hy) l hl
  have hoy : o ≠ (y : ℕ) := out_ne_lit hcl hev y (H.nc y hy) y (Or.inl rfl)
  have key := agree_B gs hcl x' (Function.update x' y true) (fun j => j = (y : ℕ) ∨ j = l)
    (o + 1)
    (by
      intro j hj hB
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
      have hne : (⟨j, hj⟩ : Fin N) ≠ y := fun e => hB (Or.inl (by rw [← e]))
      rw [Function.update_of_ne hne])
    (by
      intro q g' hq _ hBq hBa _
      obtain ⟨a, ha, hBa⟩ := hBa
      have hreads : Reads gs q a := ⟨g', hq, ha⟩
      have hqp : q = p := by
        rcases hl with el | ⟨pn, el, hpn⟩
        · have hay : a = (y : ℕ) := by
            rcases hBa with e | e
            · exact e
            · rw [e, el]
          exact hO.1 y hy q p (hay ▸ hreads) ⟨g, hp, el ▸ hlmem⟩
        · rcases hBa with e | e
          · exfalso
            have hq' := hO.1 y hy q pn (e ▸ hreads) ⟨_, hpn, by simp⟩
            apply hBq
            right
            rw [el, hq']
          · exact hO.2 y hy pn hpn q p (by rw [← el, ← e]; exact hreads)
              ⟨g, hp, el ▸ hlmem⟩
      rw [hqp, hc1, hc2])
    o (by omega) (by rintro (e | e) <;> contradiction)
  rw [hev, hev, hF0, hF1] at key
  cases key

theorem stmtWin : StmtWin := by
  intro n F D gs o p g y l h H L hO hF
  have core := win_core H L.hcl L.hev hO hF
  refine ⟨fun e x hx => core x (by simp [fixBit, e, hx]),
    fun e => ⟨fun x hx => core x (by simp [fixBit, e, hx]), ?_⟩⟩
  by_contra hge
  have hlt : h < n + 1 := by omega
  have h0 := core (fun _ => false) (by rw [vl_input _ _ _ hlt]; simp [fixBit, e])
  rw [H.zero] at h0
  cases h0

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem vl_update_of_not_supp {N : ℕ} (gs : List Gate) (h : ℕ) (y : Fin N)
    (hy : y ∉ (suppsFrom gs (inputSupps N)).getD h ∅) (x : Fin N → Bool) (b : Bool) :
    vl gs (Function.update x y b) h = vl gs x h := by
  have A := agree_wiresFrom (Function.update x y b) x gs _ _ _
    (agree_inputs (Function.update x y b) x)
  refine A.2.2 h ?_
  intro i hi
  have hiy : i ≠ y := fun e => hy (e ▸ hi)
  exact Function.update_of_ne hiy b x

theorem stmtTwo : StmtExch → StmtWin → StmtTwo := by
  intro hEx hWin n F D gs o p g y l h hD L hOne hF hand hsec
  obtain ⟨hgp, _, hin, hyD, hlit, hfree⟩ := hF
  have hcl := L.hcl

  have hnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', hx⟩ := hD.nc y hyD false
    exact ⟨_, _, hx⟩
  obtain ⟨-, hW⟩ := hWin n F D gs o p g y l h hD L hOne ⟨hgp, Or.inl hand, hin, hyD, hlit, hfree⟩
  obtain ⟨hcov, hhN⟩ := hW hand

  have hT : ∀ T : Finset ℕ, (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (n + 1 + r)) →
      T.card ≤ 2 := by
    intro T hTm
    obtain ⟨gs', o', hc', he', hlen⟩ := hEx (n + 1) F gs o h T hcl L.hev hnc hcov hTm
    have := L.hmin gs' o' hc' he'
    omega
  have hpread : Reads gs p h := ⟨g, hgp, by rcases hin with e | e <;> rw [e] <;> simp⟩
  obtain ⟨r, hrp, hrr⟩ := hsec

  have hall : ∀ t, Reads gs t h → t = p ∨ t = r := by
    intro t ht
    by_contra hne
    push_neg at hne
    have := hT {p, r, t} (by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inl hpread
      · exact Or.inl hrr
      · exact Or.inl ht)
    rw [Finset.card_insert_of_notMem (by simp [hrp.symm, hne.1.symm]),
      Finset.card_insert_of_notMem (by simp [hne.2.symm]), Finset.card_singleton] at this
    omega
  obtain ⟨gr, hgr, hhr⟩ := hrr
  have hrlen : r < gs.length := (List.getElem?_eq_some_iff.1 hgr).1
  have hhlt : h < n + 1 + r := reads_lt hcl ⟨gr, hgr, hhr⟩
  rcases hcl r gr hgr with ⟨hnot, j, _, hjin⟩ | ⟨hop, j, k, _, _, hjk⟩
  ·
    exfalso
    have hj : j = h := by rw [hjin] at hhr; simp at hhr; exact hhr.symm
    rw [hj] at hjin
    by_cases ho : o = n + 1 + r
    ·
      have h0 : F (zeroOn D (fun _ => false)) = false := by
        have : zeroOn D (fun _ : Fin (n + 1) => false) = fun _ => false := by
          funext i; simp [zeroOn]
        rw [this]; exact hD.zero
      obtain ⟨x', _, hx'y, hFx', hFx''⟩ := hD.win y hyD _ h0
      have e1 := L.hev x'
      have e2 := L.hev (Function.update x' y true)
      rw [ho, vl_not gs hcl _ r gr hgr h hnot hjin] at e1 e2
      rw [vl_update_of_not_supp gs h y (hfree y hyD) x' true] at e2
      have : F x' = F (Function.update x' y true) := by rw [← e1, ← e2]
      rw [this, hFx''] at hFx'
      exact Bool.noConfusion hFx'
    · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
      have htp : t ≠ p := by
        rintro rfl
        obtain ⟨g2, hg2, hmem⟩ := htr
        have := gate_eq hgp hg2 rfl
        subst this
        have hm : n + 1 + r = l ∨ n + 1 + r = h := by
          rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
        rcases hm with e | e
        · rcases hlit with e' | ⟨pn, e', hpn⟩
          · have := y.isLt; omega
          · have hrpn : r = pn := by omega
            subst hrpn
            have := gate_eq hgr hpn rfl
            rw [this] at hjin
            simp at hjin
            have := y.isLt; omega
        · omega
      have := hT {p, r, t} (by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact Or.inl hpread
        · exact Or.inl ⟨gr, hgr, hhr⟩
        · exact Or.inr ⟨r, gr, hgr, Or.inr hnot, ⟨gr, hgr, hhr⟩, htr⟩)
      rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
      omega
  · rcases hop with hop | hop
    ·
      refine ⟨r, gr, (if j = h then k else j), hrp, hgr, hop, ?_, hall⟩
      rw [hjk] at hhr ⊢
      by_cases hjh : j = h
      · subst hjh; right; simp
      · left
        simp at hhr ⊢
        omega
    ·
      exfalso
      by_cases ho : o = n + 1 + r
      ·
        apply hnc.elim
        intro x hx
        obtain ⟨x', hxx'⟩ := hx
        have key : ∀ z : Fin (n + 1) → Bool, F z = true := by
          intro z
          cases hz : vl gs z h
          · exact hcov z hz
          · rw [← L.hev z, ho, vl_gate gs hcl z r gr hgr, hop, hjk]
            rw [hjk] at hhr
            simp at hhr
            rcases hhr with e | e <;> subst e <;> simp [GateOp.eval, hz]
        exact hxx' (by rw [key x, key x'])
      · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
        have htp : t ≠ p := by
          rintro rfl
          obtain ⟨g2, hg2, hmem⟩ := htr
          have := gate_eq hgp hg2 rfl
          subst this
          have hm : n + 1 + r = l ∨ n + 1 + r = h := by
            rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
          rcases hm with e | e
          · rcases hlit with e' | ⟨pn, e', hpn⟩
            · have := y.isLt; omega
            · have hrpn : r = pn := by omega
              subst hrpn
              have := gate_eq hgr hpn rfl
              rw [this] at hop
              exact GateOp.noConfusion hop
          · omega
        have := hT {p, r, t} (by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact Or.inl hpread
          · exact Or.inl ⟨gr, hgr, hhr⟩
          · exact Or.inr ⟨r, gr, hgr, Or.inl hop, ⟨gr, hgr, hhr⟩, htr⟩)
        rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
        omega

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

theorem ml_of_front (hFront : StmtFront) : StmtML :=
  stmtML stmtAnd (stmtExt stmtLift stmtXMove hFront stmtWin (stmtTwo stmtExch stmtWin))

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem front_suppsFrom_prefix {m : ℕ} (gs : List Gate) :
    ∀ L : List (Finset (Fin m)), ∃ T, suppsFrom gs L = L ++ T := by
  induction gs with
  | nil => intro L; exact ⟨[], by simp [suppsFrom]⟩
  | cons g gs ih =>
    intro L
    obtain ⟨T, hT⟩ := ih (L ++ [gateSupp L g])
    exact ⟨[gateSupp L g] ++ T, by
      show suppsFrom gs (L ++ [gateSupp L g]) = _
      rw [hT, List.append_assoc]⟩

theorem front_supp_input {m : ℕ} (gs : List Gate) (i : ℕ) (hi : i < m) :
    (suppsFrom gs (inputSupps m)).getD i ∅ = {(⟨i, hi⟩ : Fin m)} := by
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix gs (inputSupps m)
  rw [hT, List.getD_append _ _ _ _ (by simp [inputSupps]; exact hi)]
  simp [inputSupps, hi]

theorem front_supp_beyond {m : ℕ} (gs : List Gate) (w : ℕ) (hw : m + gs.length ≤ w) :
    (suppsFrom gs (inputSupps m)).getD w ∅ = ∅ :=
  List.getD_eq_default _ _ (by rw [length_suppsFrom]; simp [inputSupps]; omega)

theorem front_supp_gate {m : ℕ} (gs : List Gate) (hcl : CleanL m gs) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (i : Fin m) :
    i ∈ (suppsFrom gs (inputSupps m)).getD (m + p) ∅ ↔
      ∃ a ∈ g.inputs, i ∈ (suppsFrom gs (inputSupps m)).getD a ∅ := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  set L0 := suppsFrom pre (inputSupps m) with hL0
  have hl0 : L0.length = m + pre.length := by rw [hL0, length_suppsFrom]; simp [inputSupps]
  have e : suppsFrom (pre ++ g :: post) (inputSupps m)
      = suppsFrom post (L0 ++ [gateSupp L0 g]) := by
    rw [suppsFrom_append]; rfl
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix post (L0 ++ [gateSupp L0 g])
  have full : ∀ j, j < m + pre.length →
      (suppsFrom (pre ++ g :: post) (inputSupps m)).getD j ∅ = L0.getD j ∅ := by
    intro j hj
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (suppsFrom (pre ++ g :: post) (inputSupps m)).getD (m + pre.length) ∅
      = gateSupp L0 g := by
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]), ← hl0, getD_snoc_eq]
  rw [top, mem_gateSupp]
  constructor
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [full a (hlt a ha)]; exact hia⟩
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [← full a (hlt a ha)]; exact hia⟩

section

variable {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))} {gs : List Gate}
  {o : ℕ}

theorem front_nlit (DH : DeepHyp F D) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool) :
    ¬ ∀ u, F u = xor (u y) c := by
  intro h
  obtain ⟨x, x', hx⟩ := DH.nc y hy false
  apply hx
  rw [h, h]
  simp

theorem front_fnc (DH : DeepHyp F D) {y : Fin (n + 1)} (hy : y ∈ D) :
    ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
  obtain ⟨x, x', hx⟩ := DH.nc y hy false
  exact ⟨_, _, hx⟩

theorem front_dep (DH : DeepHyp F D) (L : Least (n + 1) F gs o) {y : Fin (n + 1)} (hy : y ∈ D) :
    y ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
  have hz : zeroOn D (fun _ : Fin (n + 1) => false) = fun _ => false := by
    funext i; simp [zeroOn]
  obtain ⟨x', -, -, hF0, hF1⟩ := DH.win y hy (fun _ => false) (by rw [hz]; exact DH.zero)
  by_contra hno
  have hag := (agree_wiresFrom (Function.update x' y true) x' gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ y := fun e => hno (e ▸ hk)
      simp [Function.update_of_ne this])
  have e : F (Function.update x' y true) = F x' := by
    rw [← L.hev, ← L.hev]
    exact hag
  rw [hF0, hF1] at e
  cases e

theorem front_dlit (L : Least (n + 1) F gs o) (hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x')
    (p0 : ℕ) (hmin : ∀ r < p0, ∀ g, gs[r]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅) :
    ∀ w, w < n + 1 + p0 → (∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD w ∅) →
      ∃ y ∈ D, ∃ c : Bool, (∀ u, vl gs u w = xor (u y) c) ∧
        (w = y ∨ ∃ pn, pn < p0 ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rintro hw ⟨i, hi, his⟩
    by_cases hwn : w < n + 1
    · rw [front_supp_input gs w hwn, Finset.mem_singleton] at his
      subst his
      exact ⟨⟨w, hwn⟩, hi, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
    · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
      cases hg : gs[r]? with
      | none =>
        have hlen : gs.length ≤ r := List.getElem?_eq_none_iff.1 hg
        rw [front_supp_beyond gs _ (by omega)] at his
        simp at his
      | some g =>
        have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
        rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
        · obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl r g hg i).1 his
          rw [hin, List.mem_singleton] at ha
          subst ha
          obtain ⟨y, hy, c, hv, hs⟩ := ih a (by omega) (by omega) ⟨i, hi, hia⟩
          rcases hs with e | ⟨pn, hpn, e, hgpn⟩
          · have hge : g = ⟨GateOp.not, [(y : ℕ)]⟩ := by
              cases g
              simp only at hop hin
              rw [hop, hin, e]
            refine ⟨y, hy, !c, fun u => ?_, Or.inr ⟨r, by omega, rfl, by rw [← hge]; exact hg⟩⟩
            rw [vl_not gs L.hcl u r g hg a hop hin, hv]
            cases u y <;> cases c <;> rfl
          · exfalso
            have hpl : pn < gs.length := (List.getElem?_eq_some_iff.1 hgpn).1
            refine L.no_alias hfnc r hrl y (by have := y.isLt; omega) (fun u => ?_)
            rw [vl_not gs L.hcl u r g hg a hop hin, e,
              vl_not gs L.hcl u pn _ hgpn (y : ℕ) rfl rfl, vl_input gs u y y.isLt]
            simp
        · exact absurd his (hmin r (by omega) g hg hop i hi)

theorem front_out (DH : DeepHyp F D) (L : Least (n + 1) F gs o) (p : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (l : ℕ)
    (hl : l ∈ g.inputs) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool)
    (hv : ∀ u, vl gs u l = xor (u y) c) : o ≠ n + 1 + p := by
  intro e
  obtain ⟨x, x', hx⟩ := DH.nc y hy (xor (fixBit g) c)
  have hc : ∀ z : Fin (n + 1) → Bool, F (Function.update z y (xor (fixBit g) c)) = fixBit g := by
    intro z
    rw [← L.hev, e]
    refine vl_abs gs L.hcl _ p g hg hop l hl ?_
    rw [hv]
    simp
  exact hx (by rw [hc, hc])

theorem front_two (DH : DeepHyp F D) (L : Least (n + 1) F gs o) (OR : OneReader D gs) (p : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (j k : ℕ)
    (hin : g.inputs = [j, k]) (hj : j < n + 1 + p) (hk : k < n + 1 + p)
    (yj : Fin (n + 1)) (hyj : yj ∈ D) (cj : Bool) (hvj : ∀ u, vl gs u j = xor (u yj) cj)
    (hsj : j = yj ∨ ∃ pn, pn < p ∧ j = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yj : ℕ)]⟩)
    (yk : Fin (n + 1)) (hyk : yk ∈ D) (ck : Bool) (hvk : ∀ u, vl gs u k = xor (u yk) ck)
    (hsk : k = yk ∨ ∃ pn, pn < p ∧ k = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yk : ℕ)]⟩) :
    False := by
  have hfnc := front_fnc DH hyj
  have htl : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hRj : Reads gs p j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs p k := ⟨g, hg, by rw [hin]; simp⟩

  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), v ∈ D → Reads gs p w →
      (w = v ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(v : ℕ)]⟩) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = p := by
    intro w v hv hw hs p' a ha hr hne
    rcases hs with e | ⟨r, _, er, hg'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact OR.1 v hv p' p hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨_, hg', by simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := OR.1 v hv p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact OR.2 v hv r hg' p' p hr hw

  have hvjk : yj ≠ yk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc p htl j hj (fun u => by
        rw [vl_gate gs L.hcl u p g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, hr1, ej, hg1⟩ <;> rcases hsk with ek | ⟨r2, hr2, ek, hg2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := OR.1 yj hyj p r2 (by rw [← ej]; exact hRj) ⟨_, hg2, by rw [← e]; simp⟩
      omega
    · have := OR.1 yk hyk p r1 (by rw [← ek]; exact hRk) ⟨_, hg1, by rw [e]; simp⟩
      omega
    · have := OR.1 yj hyj r1 r2 ⟨_, hg1, by simp⟩ ⟨_, hg2, by rw [← e]; simp⟩
      exact hjk (by rw [ej, ek, this])

  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ yj → i ≠ yk → u i = u' i) →
      vl gs u (n + 1 + p) = vl gs u' (n + 1 + p) → F u = F u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (yj : ℕ) ∨ n + 1 + p' = (yk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = p := by
        rcases hBa' with e | e | e | e
        · exact hopnd j yj hyj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j yj hyj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (yj : ℕ) ∨ o = (yk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact front_nlit DH hyj false (fun x => by
          rw [← L.hev, e, vl_input gs x yj yj.isLt]; simp)
      · exact front_nlit DH hyk false (fun x => by
          rw [← L.hev, e, vl_input gs x yk yk.isLt]; simp)
      · exact front_nlit DH hyj cj (fun x => by rw [← L.hev, e, hvj])
      · exact front_nlit DH hyk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ yj → i ≠ yk →
      set2 x yj a yk b i = set2 x yj a' yk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x yj yk a b i e1 e2, set2_o x yj yk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x yj a yk b) (n + 1 + p) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ p g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  apply DH.nf yj hyj yk hyk hvjk
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

end

theorem stmtFront : StmtFront := by
  intro n F D gs o DH hD L OR
  classical
  obtain ⟨y0, hy0⟩ := hD
  have hfnc := front_fnc DH hy0
  by_cases hex : ∃ p g, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + p) ∅
  · obtain ⟨g, hg, hop, i, hi, his⟩ := Nat.find_spec hex
    set p := Nat.find hex with hpdef
    have hmin : ∀ r < p, ∀ g', gs[r]? = some g' → (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r hr g' hg' hop' i hi his => Nat.find_min hex hr ⟨g', hg', hop', i, hi, his⟩
    rcases L.hcl p g hg with ⟨hop2, _⟩ | ⟨_, j, k, hj, hk, hin⟩
    · rcases hop with h | h <;> rw [h] at hop2 <;> cases hop2
    obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl p g hg i).1 his
    rw [hin] at ha
    have hlitof : ∀ (w : ℕ) (y : Fin (n + 1)),
        (w = y ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) →
        IsLit (n + 1) gs y w := by
      rintro w y (e | ⟨pn, _, e, hpn⟩)
      · exact Or.inl e
      · exact Or.inr ⟨pn, e, hpn⟩
    by_cases mj : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD j ∅ <;>
      by_cases mk : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD k ∅
    · exfalso
      obtain ⟨yj, hyj, cj, hvj, hsj⟩ := front_dlit L hfnc p hmin j hj mj
      obtain ⟨yk, hyk, ck, hvk, hsk⟩ := front_dlit L hfnc p hmin k hk mk
      exact front_two DH L OR p g hg hop j k hin hj hk yj hyj cj hvj hsj yk hyk ck hvk hsk
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin j hj mj
      refine ⟨p, g, y, j, k, ⟨hg, hop, Or.inl hin, hy, hlitof j y hs,
        fun y' hy' hm => mk ⟨y', hy', hm⟩⟩,
        front_out DH L p g hg hop j (by rw [hin]; simp) hy c hv⟩
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin k hk mk
      refine ⟨p, g, y, k, j, ⟨hg, hop, Or.inr hin, hy, hlitof k y hs,
        fun y' hy' hm => mj ⟨y', hy', hm⟩⟩,
        front_out DH L p g hg hop k (by rw [hin]; simp) hy c hv⟩
    · exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact mj ⟨i, hi, hia⟩
      · exact mk ⟨i, hi, hia⟩
  · exfalso
    have hmin : ∀ r < gs.length, ∀ g', gs[r]? = some g' →
        (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r _ g' hg' hop' i hi his => hex ⟨r, g', hg', hop', i, hi, his⟩
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨y, hy, c, hv, _⟩ := front_dlit L hfnc gs.length hmin o hol
        ⟨y0, hy0, front_dep DH L hy0⟩
      exact front_nlit DH hy c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, x', hxx⟩ := hfnc
      apply hxx
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs x' o (by omega)]

end PEqualNP.MetaComplexity.EdgeFn

namespace PEqualNP.MetaComplexity.EdgeFn

theorem stmtML_final : StmtML := ml_of_front stmtFront

end PEqualNP.MetaComplexity.EdgeFn

namespace Up

open PEqualNP.MetaComplexity.Helpers.PermInputs

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem plug {m r s : ℕ} (f : (Fin m → Bool) → Bool) (H : (Fin (m+1) → Bool) → Bool)
    (hf : HasCircuitSize m f r) (hh : HasCircuitSize (m+1) H s)
    (live : ∃ x, f x = true) :
    HasCircuitSize m (fun x => H (Fin.snoc x (f x))) (r+s) := by
  obtain ⟨D,okD,szD,evD⟩ := hf
  let M := m + D.gates.length
  have len (x : Fin m → Bool) : (D.wires (List.ofFn x)).length = M := by
    have aux (gs : List Gate) (W : List Bool) :
        (gs.foldl stepW W).length = W.length + gs.length := by
      induction gs generalizing W with
      | nil => simp
      | cons h t ih => simp [List.foldl,ih,stepW]; omega
    change (D.gates.foldl stepW _).length = _
    rw [aux]; simp [M]
  have valid : D.output < M := by
    obtain ⟨x,hx⟩ := live
    by_contra! hx'
    have h := evD x
    unfold Circuit.eval at h
    rw [List.getD_eq_default _ _ (by rw [len]; exact hx'), hx] at h
    contradiction
  let π : Fin (m+1) → Fin M := Fin.snoc (fun i : Fin m => (⟨i.val, by dsimp [M]; omega⟩ : Fin M)) ⟨D.output,valid⟩
  obtain ⟨C,okC,szC,evC⟩ := relabel_size π H s hh
  refine ⟨⟨D.gates ++ C.gates,C.output⟩,?_,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact okD g h
    · exact okC g h
  · change (D.gates++C.gates).length ≤ _
    change D.gates.length ≤ _ at szD
    change C.gates.length ≤ _ at szC
    simp; omega
  · intro x
    let W := D.wires (List.ofFn x)
    let z : Fin M → Bool := fun i => W.getD i.val false
    have ofz : List.ofFn z = W := by
      apply List.ext_getElem <;> simp [z,W,len]
    have hz : z ∘ π = Fin.snoc x (f x) := by
      funext i; refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [z,π,W,Circuit.eval] using evD x
      · have keep (gs : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
            (gs.foldl stepW w).getD j false = w.getD j false := by
          induction gs generalizing w with
          | nil => rfl
          | cons h t ih =>
            rw [List.foldl_cons,ih (stepW w h) (by simp [stepW]; omega)]
            exact List.getD_append _ _ _ _ hj
        simp only [Function.comp_apply,π,Fin.snoc_castSucc]
        change (D.gates.foldl stepW (List.ofFn x)).getD j.val false = x j
        rw [keep _ _ _ (by simp)]
        simp [List.getD_eq_getElem]
    have h : C.eval (List.ofFn z) = H (z ∘ π) := evC z
    rw [hz] at h
    change ((D.gates ++ C.gates).foldl stepW _).getD C.output false = _
    rw [List.foldl_append]
    change (C.gates.foldl stepW W).getD C.output false = _
    change (C.gates.foldl stepW (List.ofFn z)).getD C.output false = _ at h
    rw [ofz] at h
    exact h
theorem weaken {m s t : ℕ} {f : (Fin m → Bool) → Bool}
    (h : HasCircuitSize m f s) (hle : s ≤ t) : HasCircuitSize m f t := by
  obtain ⟨C, ok, sz, ev⟩ := h
  exact ⟨C,ok,sz.trans hle,ev⟩
theorem input {m : ℕ} (i : Fin m) : HasCircuitSize m (fun x => x i) 0 := by
  refine ⟨⟨[],i.val⟩,by simp [FanInTwo],by simp [Circuit.size],?_⟩
  intro x; simp [Circuit.eval,Circuit.wires,List.getD_eq_getElem]
theorem addWire {m : ℕ} (a b : Fin m) (op : GateOp) (ho : op = .and ∨ op = .or) :
    HasCircuitSize m (fun x => op.eval [x a,x b]) 1 := by
  refine ⟨⟨[⟨op,[a,b]⟩],m⟩,?_,by simp [Circuit.size],?_⟩
  · intro g hg; simp at hg; subst g
    obtain rfl|rfl := ho <;> simp
  · intro x
    simp [Circuit.eval,Circuit.wires,List.getD_eq_getElem]
theorem binary {m s t : ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : HasCircuitSize m f s) (hg : HasCircuitSize m g t)
    (lf : ∃ x, f x = true) (lg : ∃ x, g x = true)
    (op : GateOp) (ho : op = .and ∨ op = .or) :
    HasCircuitSize m (fun x => op.eval [f x,g x]) (s+t+1) := by
  let G : (Fin (m+1) → Bool) → Bool := fun z => g (fun i => z i.castSucc)
  have hG : HasCircuitSize (m+1) G t := relabel_size Fin.castSucc g t hg
  have lG : ∃ x, G x = true := by
    obtain ⟨x,hx⟩ := lg
    exact ⟨Fin.snoc x false, by simpa [G] using hx⟩
  have h1 := addWire (Fin.last m).castSucc (Fin.last (m+1)) op ho
  have h2 := plug G _ hG h1 lG
  have h3 := plug f _ hf h2 lf
  simpa [G,Nat.add_assoc] using h3
theorem orSize {m s t : ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : HasCircuitSize m f s) (hg : HasCircuitSize m g t) :
    HasCircuitSize m (fun x => f x || g x) (s+t+1) := by
  by_cases lf : ∃ x, f x = true
  · by_cases lg : ∃ x, g x = true
    · simpa [GateOp.eval] using binary hf hg lf lg .or (Or.inr rfl)
    · have h x : g x = false := by cases he : g x <;> simp_all
      simpa [h] using weaken hf (show s ≤ s+t+1 by omega)
  · have h x : f x = false := by cases he : f x <;> simp_all
    simpa [h] using weaken hg (show t ≤ s+t+1 by omega)
theorem andLive {m s t : ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : HasCircuitSize m f s) (hg : HasCircuitSize m g t)
    (lf : ∃ x, f x = true) (lg : ∃ x, g x = true) :
    HasCircuitSize m (fun x => f x && g x) (s+t+1) := by
  simpa [GateOp.eval] using binary hf hg lf lg .and (Or.inl rfl)

end Up

namespace Tail

open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.EdgeFn

def pa (n : ℕ) : Fin (n + 2) := (Fin.last n).castSucc

def pb (n : ℕ) : Fin (n + 2) := Fin.last (n + 1)

def pre {n : ℕ} (x : Fin (n + 2) → Bool) : Fin n → Bool := fun i => x i.castSucc.castSucc

def maj (n : ℕ) (X : (Fin n → Bool) → Bool) : (Fin (n + 2) → Bool) → Bool :=
  fun x : Fin (n + 2) → Bool => (X (fun i : Fin n => x i.castSucc.castSucc) && (x (Fin.last n).castSucc || x (Fin.last (n + 1)))) || (x (Fin.last n).castSucc && x (Fin.last (n + 1)))

def lift {n : ℕ} (y : Fin n → Bool) (u v : Bool) : Fin (n + 2) → Bool :=
  fun j => if h : j.val < n then y ⟨j.val, h⟩ else if j.val = n then u else v

theorem maj_eq (n : ℕ) (X : (Fin n → Bool) → Bool) (x : Fin (n + 2) → Bool) :
    maj n X x = ((X (pre x) && (x (pa n) || x (pb n))) || (x (pa n) && x (pb n))) := rfl

theorem pa_val (n : ℕ) : (pa n).val = n := rfl

theorem pb_val (n : ℕ) : (pb n).val = n + 1 := rfl

theorem cc_val {n : ℕ} (i : Fin n) : (i.castSucc.castSucc : Fin (n + 2)).val = i.val := rfl

theorem pa_ne_pb (n : ℕ) : pa n ≠ pb n := by
  intro h
  have h1 := congrArg Fin.val h
  rw [pa_val, pb_val] at h1
  omega

theorem cc_ne_pa {n : ℕ} (i : Fin n) : (i.castSucc.castSucc : Fin (n + 2)) ≠ pa n := by
  intro h
  have h1 := congrArg Fin.val h
  rw [pa_val, cc_val] at h1
  have hi := i.isLt
  omega

theorem cc_ne_pb {n : ℕ} (i : Fin n) : (i.castSucc.castSucc : Fin (n + 2)) ≠ pb n := by
  intro h
  have h1 := congrArg Fin.val h
  rw [pb_val, cc_val] at h1
  have hi := i.isLt
  omega

theorem pre_upd_a {n : ℕ} (x : Fin (n + 2) → Bool) (c : Bool) :
    pre (Function.update x (pa n) c) = pre x := by
  funext i
  show Function.update x (pa n) c i.castSucc.castSucc = x i.castSucc.castSucc
  rw [Function.update_apply, if_neg (cc_ne_pa i)]

theorem pre_upd_b {n : ℕ} (x : Fin (n + 2) → Bool) (c : Bool) :
    pre (Function.update x (pb n) c) = pre x := by
  funext i
  show Function.update x (pb n) c i.castSucc.castSucc = x i.castSucc.castSucc
  rw [Function.update_apply, if_neg (cc_ne_pb i)]

theorem upd_a_a {n : ℕ} (x : Fin (n + 2) → Bool) (c : Bool) :
    Function.update x (pa n) c (pa n) = c := by
  rw [Function.update_apply, if_pos rfl]

theorem upd_b_b {n : ℕ} (x : Fin (n + 2) → Bool) (c : Bool) :
    Function.update x (pb n) c (pb n) = c := by
  rw [Function.update_apply, if_pos rfl]

theorem upd_a_b {n : ℕ} (x : Fin (n + 2) → Bool) (c : Bool) :
    Function.update x (pa n) c (pb n) = x (pb n) := by
  rw [Function.update_apply, if_neg (pa_ne_pb n).symm]

theorem upd_b_a {n : ℕ} (x : Fin (n + 2) → Bool) (c : Bool) :
    Function.update x (pb n) c (pa n) = x (pa n) := by
  rw [Function.update_apply, if_neg (pa_ne_pb n)]

theorem maj_upd_a (n : ℕ) (X : (Fin n → Bool) → Bool) (x : Fin (n + 2) → Bool) (c : Bool) :
    maj n X (Function.update x (pa n) c) = ((X (pre x) && (c || x (pb n))) || (c && x (pb n))) := by
  rw [maj_eq, pre_upd_a, upd_a_a, upd_a_b]

theorem maj_upd_b (n : ℕ) (X : (Fin n → Bool) → Bool) (x : Fin (n + 2) → Bool) (c : Bool) :
    maj n X (Function.update x (pb n) c) = ((X (pre x) && (x (pa n) || c)) || (x (pa n) && c)) := by
  rw [maj_eq, pre_upd_b, upd_b_a, upd_b_b]

theorem maj_set_ab (n : ℕ) (X : (Fin n → Bool) → Bool) (x : Fin (n + 2) → Bool) (u v : Bool) :
    maj n X (set2 x (pa n) u (pb n) v) = ((X (pre x) && (u || v)) || (u && v)) := by
  show maj n X (Function.update (Function.update x (pa n) u) (pb n) v) = _
  rw [maj_upd_b, pre_upd_a, upd_a_a]

theorem maj_set_ba (n : ℕ) (X : (Fin n → Bool) → Bool) (x : Fin (n + 2) → Bool) (u v : Bool) :
    maj n X (set2 x (pb n) u (pa n) v) = ((X (pre x) && (v || u)) || (v && u)) := by
  show maj n X (Function.update (Function.update x (pb n) u) (pa n) v) = _
  rw [maj_upd_a, pre_upd_b, upd_b_b]

theorem pre_lift {n : ℕ} (y : Fin n → Bool) (u v : Bool) : pre (lift y u v) = y := by
  funext i
  show lift y u v i.castSucc.castSucc = y i
  unfold lift
  have h : (i.castSucc.castSucc : Fin (n + 2)).val < n := i.isLt
  rw [dif_pos h]
  rfl

theorem lift_a {n : ℕ} (y : Fin n → Bool) (u v : Bool) : lift y u v (pa n) = u := by
  unfold lift
  have h : ¬ (pa n).val < n := by rw [pa_val]; omega
  rw [dif_neg h, if_pos (pa_val n)]

theorem lift_b {n : ℕ} (y : Fin n → Bool) (u v : Bool) : lift y u v (pb n) = v := by
  unfold lift
  have h : ¬ (pb n).val < n := by rw [pb_val]; omega
  have h' : ¬ (pb n).val = n := by rw [pb_val]; omega
  rw [dif_neg h, if_neg h']

theorem deep (n : ℕ) (X : (Fin n → Bool) → Bool) (yt yf : Fin n → Bool)
    (ht : X yt = true) (hf : X yf = false) :
    DeepHyp (maj n X) ({pa n, pb n} : Finset (Fin (n + 2))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy c
    have hy2 : y = pa n ∨ y = pb n := by simpa using hy
    rcases hy2 with rfl | rfl
    · refine ⟨lift yt c (!c), lift yf c (!c), ?_⟩
      rw [maj_upd_a, maj_upd_a, pre_lift, pre_lift, lift_b, lift_b, ht, hf]
      cases c <;> decide
    · refine ⟨lift yt (!c) c, lift yf (!c) c, ?_⟩
      rw [maj_upd_b, maj_upd_b, pre_lift, pre_lift, lift_a, lift_a, ht, hf]
      cases c <;> decide
  · intro y hy y' hy' hne hpf
    have hy2 : y = pa n ∨ y = pb n := by simpa using hy
    have hy2' : y' = pa n ∨ y' = pb n := by simpa using hy'
    obtain ⟨α, β, h⟩ := hpf
    have h1 := h (lift yt false false)
    have h2 := h (lift yf false false)
    rcases hy2 with rfl | rfl <;> rcases hy2' with rfl | rfl
    · exact hne rfl
    · simp only [maj_set_ab, pre_lift, ht] at h1
      simp only [maj_set_ab, pre_lift, hf] at h2
      revert h1 h2
      cases α <;> cases β <;> decide
    · simp only [maj_set_ba, pre_lift, ht] at h1
      simp only [maj_set_ba, pre_lift, hf] at h2
      revert h1 h2
      cases α <;> cases β <;> decide
    · exact hne rfl
  · intro y hy x _
    have hy2 : y = pa n ∨ y = pb n := by simpa using hy
    rcases hy2 with rfl | rfl
    · refine ⟨Function.update (Function.update x (pa n) false) (pb n) (!X (pre x)), ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hi2 : ¬ i = pa n ∧ ¬ i = pb n := by simpa using hi
        rw [Function.update_apply, if_neg hi2.2, Function.update_apply, if_neg hi2.1]
      · rw [upd_b_a, upd_a_a]
      · rw [maj_upd_b, pre_upd_a, upd_a_a]
        cases X (pre x) <;> rfl
      · rw [maj_upd_a, pre_upd_b, pre_upd_a, upd_b_b]
        cases X (pre x) <;> rfl
    · refine ⟨Function.update (Function.update x (pb n) false) (pa n) (!X (pre x)), ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hi2 : ¬ i = pa n ∧ ¬ i = pb n := by simpa using hi
        rw [Function.update_apply, if_neg hi2.1, Function.update_apply, if_neg hi2.2]
      · rw [upd_a_b, upd_b_b]
      · rw [maj_upd_a, pre_upd_b, upd_b_b]
        cases X (pre x) <;> rfl
      · rw [maj_upd_b, pre_upd_a, pre_upd_b, upd_a_a]
        cases X (pre x) <;> rfl
  · intro x hx
    have ha : zeroOn ({pa n, pb n} : Finset (Fin (n + 2))) x (pa n) = false := by simp [zeroOn]
    have hb : zeroOn ({pa n, pb n} : Finset (Fin (n + 2))) x (pb n) = false := by simp [zeroOn]
    rw [maj_eq, ha, hb] at hx
    simp at hx
  · rw [maj_eq]
    simp

def pi2 (n : ℕ) : Fin (n + 2) → Fin (n + 1) :=
  fun j => if h : j.val < n then ⟨j.val, Nat.lt_succ_of_lt h⟩ else Fin.last n

def Hc {n : ℕ} (X : (Fin n → Bool) → Bool) (c : Bool) : (Fin (n + 1) → Bool) → Bool :=
  fun x => (X (fun i : Fin n => x i.castSucc) && (c || x (Fin.last n))) || (c && x (Fin.last n))

theorem pi2_cc {n : ℕ} (i : Fin n) : pi2 n i.castSucc.castSucc = i.castSucc := by
  unfold pi2
  have h : (i.castSucc.castSucc : Fin (n + 2)).val < n := i.isLt
  rw [dif_pos h]
  exact Fin.ext rfl

theorem pi2_a (n : ℕ) : pi2 n (pa n) = Fin.last n := by
  unfold pi2
  have h : ¬ (pa n).val < n := by rw [pa_val]; omega
  rw [dif_neg h]

theorem pi2_b (n : ℕ) : pi2 n (pb n) = Fin.last n := by
  unfold pi2
  have h : ¬ (pb n).val < n := by rw [pb_val]; omega
  rw [dif_neg h]

theorem pre_pi2 {n : ℕ} (x : Fin (n + 1) → Bool) :
    pre (x ∘ pi2 n) = fun i : Fin n => x i.castSucc := by
  funext i
  show x (pi2 n i.castSucc.castSucc) = x i.castSucc
  rw [pi2_cc]

theorem relab_a (n : ℕ) (X : (Fin n → Bool) → Bool) (c : Bool) (x : Fin (n + 1) → Bool) :
    maj n X (Function.update (x ∘ pi2 n) (pa n) c) = Hc X c x := by
  rw [maj_upd_a, pre_pi2]
  show ((X (fun i : Fin n => x i.castSucc) && (c || x (pi2 n (pb n)))) || (c && x (pi2 n (pb n)))) = _
  rw [pi2_b]
  rfl

theorem relab_b (n : ℕ) (X : (Fin n → Bool) → Bool) (c : Bool) (x : Fin (n + 1) → Bool) :
    maj n X (Function.update (x ∘ pi2 n) (pb n) c) = Hc X c x := by
  rw [maj_upd_b, pre_pi2]
  show ((X (fun i : Fin n => x i.castSucc) && (x (pi2 n (pa n)) || c)) || (x (pi2 n (pa n)) && c)) =
    ((X (fun i : Fin n => x i.castSucc) && (c || x (Fin.last n))) || (c && x (Fin.last n)))
  rw [pi2_a]
  generalize X (fun i : Fin n => x i.castSucc) = p
  generalize x (Fin.last n) = q
  cases c <;> cases p <;> cases q <;> rfl

theorem Hc_snoc {n : ℕ} (X : (Fin n → Bool) → Bool) (c v : Bool) (y : Fin n → Bool) :
    Hc X c (Fin.snoc y v : Fin (n + 1) → Bool) = ((X y && (c || v)) || (c && v)) := by
  simp [Hc]

theorem upd_snoc {n : ℕ} (y : Fin n → Bool) (v w : Bool) :
    Function.update (Fin.snoc y v : Fin (n + 1) → Bool) (Fin.last n) w =
      (Fin.snoc y w : Fin (n + 1) → Bool) := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [Function.update_apply, if_neg (Fin.castSucc_lt_last i).ne]
    simp
  · simp

theorem drop_last {n : ℕ} (X : (Fin n → Bool) → Bool) (yt yf : Fin n → Bool)
    (ht : X yt = true) (hf : X yf = false) (c : Bool) (t : ℕ)
    (h : HasCircuitSize (n + 1) (Hc X c) (t + 1)) : HasCircuitSize n X t := by
  have hdep : ∃ x : Fin (n + 1) → Bool,
      Hc X c (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ Hc X c x := by
    cases c
    · refine ⟨(Fin.snoc yt false : Fin (n + 1) → Bool), ?_⟩
      simp [upd_snoc, Hc_snoc, ht]
    · refine ⟨(Fin.snoc yf false : Fin (n + 1) → Bool), ?_⟩
      simp [upd_snoc, Hc_snoc, hf]
  have hnc : ∃ y y' : Fin n → Bool,
      Hc X c (Fin.snoc y (!c) : Fin (n + 1) → Bool) ≠ Hc X c (Fin.snoc y' (!c) : Fin (n + 1) → Bool) := by
    refine ⟨yt, yf, ?_⟩
    rw [Hc_snoc, Hc_snoc, ht, hf]
    cases c <;> decide
  have key := gate_elim n (Hc X c) (!c) t hdep hnc h
  have e : X = fun y : Fin n → Bool => Hc X c (Fin.snoc y (!c) : Fin (n + 1) → Bool) := by
    funext y
    rw [Hc_snoc]
    cases c <;> cases X y <;> rfl
  rw [e]
  exact key

theorem size_zero {m : ℕ} {f : (Fin m → Bool) → Bool} (h : HasCircuitSize m f 0) :
    (∀ x, f x = false) ∨ ∃ j : Fin m, ∀ x, f x = x j := by
  obtain ⟨C, _, hsz, hev⟩ := h
  have hlen : C.gates.length = 0 := Nat.le_zero.mp hsz
  have hg : C.gates = [] := List.eq_nil_of_length_eq_zero hlen
  have hw : ∀ x : Fin m → Bool, f x = (List.ofFn x).getD C.output false := by
    intro x
    rw [← hev x]
    unfold Circuit.eval Circuit.wires
    rw [hg]
    rfl
  by_cases hj : C.output < m
  · right
    refine ⟨⟨C.output, hj⟩, fun x => ?_⟩
    rw [hw x, List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  · left
    intro x
    rw [hw x, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hj)]

theorem Hc_false_pos {n : ℕ} (X : (Fin n → Bool) → Bool) (yt yf : Fin n → Bool)
    (ht : X yt = true) (hf : X yf = false) (s' : ℕ)
    (h : HasCircuitSize (n + 1) (Hc X false) s') : ∃ t : ℕ, s' = t + 1 := by
  cases s' with
  | succ t => exact ⟨t, rfl⟩
  | zero =>
    exfalso
    rcases size_zero h with h0 | ⟨j, hj⟩
    · have h1 := h0 (Fin.snoc yt true : Fin (n + 1) → Bool)
      rw [Hc_snoc, ht] at h1
      revert h1
      decide
    · have h1 := hj (Fin.snoc yt true : Fin (n + 1) → Bool)
      have h2 := hj (Fin.snoc yt false : Fin (n + 1) → Bool)
      have h3 := hj (Fin.snoc yf true : Fin (n + 1) → Bool)
      rw [Hc_snoc, ht] at h1 h2
      rw [Hc_snoc, hf] at h3
      rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
      · simp at h1 h2
        exact absurd (h1.symm.trans h2) (by decide)
      · simp at h3

theorem lower (n s : ℕ) (X : (Fin n → Bool) → Bool) (yt yf : Fin n → Bool)
    (ht : X yt = true) (hf : X yf = false)
    (h : HasCircuitSize (n + 2) (maj n X) s) : ∃ c : ℕ, HasCircuitSize n X c ∧ c + 4 ≤ s := by
  have hD : DeepHyp (maj n X) ({pa n, pb n} : Finset (Fin (n + 2))) := deep n X yt yf ht hf
  have hne : ({pa n, pb n} : Finset (Fin (n + 2))).Nonempty := ⟨pa n, by simp⟩
  have hS : StmtML := stmtML_final
  unfold StmtML at hS
  obtain ⟨y, hy, hcase⟩ := hS (n + 1) (maj n X) {pa n, pb n} s hD hne h
  have hy2 : y = pa n ∨ y = pb n := by simpa using hy
  have red : ∀ (c : Bool) (s' : ℕ),
      HasCircuitSize (n + 2) (fun x => maj n X (Function.update x y c)) s' →
      HasCircuitSize (n + 1) (Hc X c) s' := by
    intro c s' hs'
    have hr := relabel_size (pi2 n) (fun x => maj n X (Function.update x y c)) s' hs'
    have e : Hc X c = fun x : Fin (n + 1) → Bool => maj n X (Function.update (x ∘ pi2 n) y c) := by
      funext x
      rcases hy2 with rfl | rfl
      · exact (relab_a n X c x).symm
      · exact (relab_b n X c x).symm
    rw [e]
    exact hr
  rcases hcase with ⟨s', hs', hc⟩ | ⟨s', hs', hc⟩
  · obtain ⟨t, rfl⟩ := Hc_false_pos X yt yf ht hf s' (red false s' hc)
    exact ⟨t, drop_last X yt yf ht hf false t (red false (t + 1) hc), by omega⟩
  · have h1 : HasCircuitSize (n + 1) (Hc X true) (s' + 1) :=
      Up.weaken (red true s' hc) (Nat.le_succ s')
    exact ⟨s', drop_last X yt yf ht hf true s' h1, hs'⟩

theorem upper (n s : ℕ) (X : (Fin n → Bool) → Bool) (yt : Fin n → Bool) (ht : X yt = true)
    (c : ℕ) (hc : HasCircuitSize n X c) (hs : c + 4 ≤ s) :
    HasCircuitSize (n + 2) (maj n X) s := by
  have hX : HasCircuitSize (n + 2)
      (fun x : Fin (n + 2) → Bool => X (fun i : Fin n => x i.castSucc.castSucc)) c :=
    relabel_size (fun i : Fin n => i.castSucc.castSucc) X c hc
  have ia : HasCircuitSize (n + 2) (fun x : Fin (n + 2) → Bool => x (Fin.last n).castSucc) 0 :=
    Up.input _
  have ib : HasCircuitSize (n + 2) (fun x : Fin (n + 2) → Bool => x (Fin.last (n + 1))) 0 :=
    Up.input _
  have hor := Up.orSize ia ib
  have hand := Up.andLive ia ib ⟨fun _ => true, rfl⟩ ⟨fun _ => true, rfl⟩
  have lX : ∃ x : Fin (n + 2) → Bool, X (fun i : Fin n => x i.castSucc.castSucc) = true := by
    refine ⟨lift yt true true, ?_⟩
    show X (pre (lift yt true true)) = true
    rw [pre_lift]
    exact ht
  have h1 := Up.andLive hX hor lX ⟨fun _ => true, rfl⟩
  have h2 := Up.orSize h1 hand
  exact Up.weaken h2 (by omega)

theorem main (n s : ℕ) (X : (Fin n → Bool) → Bool) (hX : ∃ y y' : Fin n → Bool, X y ≠ X y') :
    HasCircuitSize (n + 2) (maj n X) s ↔ ∃ c : ℕ, HasCircuitSize n X c ∧ c + 4 ≤ s := by
  obtain ⟨yt, yf, ht, hf⟩ : ∃ yt yf : Fin n → Bool, X yt = true ∧ X yf = false := by
    obtain ⟨y, y', hne⟩ := hX
    cases h1 : X y <;> cases h2 : X y'
    · exact absurd (h1.trans h2.symm) hne
    · exact ⟨y', y, h2, h1⟩
    · exact ⟨y, y', h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne
  constructor
  · exact lower n s X yt yf ht hf
  · rintro ⟨c, hc, hs⟩
    exact upper n s X yt ht c hc hs

end Tail

end LMeta567

theorem PEqualNP.Outside.L_meta_567 : ∀ (n s : ℕ) (X : (Fin n → Bool) → Bool), (∃ y y' : Fin n → Bool, X y ≠ X y') → (PEqualNP.MetaComplexity.HasCircuitSize (n + 2) (fun x : Fin (n + 2) → Bool => (X (fun i : Fin n => x i.castSucc.castSucc) && (x (Fin.last n).castSucc || x (Fin.last (n + 1)))) || (x (Fin.last n).castSucc && x (Fin.last (n + 1)))) s ↔ ∃ c : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n X c ∧ c + 4 ≤ s) :=
  fun n s X hX => LMeta567.Tail.main n s X hX
