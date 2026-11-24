import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3588_aux

-- The elimination of one gate below is the checked L-meta-2535, carried into this file.


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

def sval (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def svalid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
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

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
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
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, svalid w.length s) :
    svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (sval w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, svalid, sval, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, svalid, sval, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, svalid, sval, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, svalid, sval, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, svalid, sval, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, svalid, sval, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, svalid, sval, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, svalid, sval, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
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

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
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

theorem svalid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Bool ⊕ ℕ, svalid m s → svalid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem sval_append (w t : List Bool) : ∀ s : Bool ⊕ ℕ, svalid w.length s →
    sval (w ++ t) s = sval w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    svalid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    sval (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
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
    have hvals : ins.map (sval w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show svalid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      sval (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨svalid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, sval_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


theorem elim_count1 (n k : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length →
    acc.1.getD k (Sum.inl false) = Sum.inl false →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hlen hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have hl : (elimStep n acc g).1.length = acc.1.length + 1 := by simp [elimStep]
    have hk' : (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl false := by
      simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hk
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by omega) hk'
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hg : k ∈ g.inputs
    · have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨false, List.mem_map.2 ⟨k, hg, hk⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hg, decide_true, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hg, decide_false, Bool.false_eq_true, ite_false]
      omega

theorem agree_off (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool, w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    (∀ g ∈ gs, k ∉ g.inputs) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ h _ j hj; exact h j hj
  | cons g gs ih =>
    intro w w' hl hag hgs
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact hag a (fun e => hgs g List.mem_cons_self (e ▸ ha))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (by simp [hl]) _ (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = w.length
    · subst hjl
      rw [getD_snoc_eq, hl, getD_snoc_eq, hv]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact hag j hj

theorem getD_ofFn_lt {α : Type} {n : ℕ} (x : Fin n → α) (d : α) (j : ℕ) (h : j < n) :
    (List.ofFn x).getD j d = x ⟨j, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_ofFn_ge {α : Type} {n : ℕ} (x : Fin n → α) (d : α) (j : ℕ) (h : n ≤ j) :
    (List.ofFn x).getD j d = d :=
  List.getD_eq_default _ _ (by simp; omega)

def initStats (n : ℕ) (i : Fin n) : List (Bool ⊕ ℕ) :=
  List.ofFn (fun j : Fin n => if j = i then (Sum.inl false : Bool ⊕ ℕ) else Sum.inr j.val)

theorem inv_init1 (n : ℕ) (i : Fin n) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y i false)) (initStats n i, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro j
  by_cases hj : j < n
  · show svalid (n + 0) ((initStats n i).getD j (Sum.inl false)) ∧
      sval (wiresFrom [] (List.ofFn y)) ((initStats n i).getD j (Sum.inl false)) = _
    rw [initStats, getD_ofFn_lt _ _ _ hj, getD_ofFn_lt _ _ _ hj]
    by_cases hji : (⟨j, hj⟩ : Fin n) = i
    · rw [if_pos hji, ← hji, Function.update_self]
      exact ⟨trivial, rfl⟩
    · rw [if_neg hji, Function.update_of_ne hji]
      refine ⟨show j < n + 0 by omega, ?_⟩
      show (wiresFrom [] (List.ofFn y)).getD j false = y ⟨j, hj⟩
      exact getD_ofFn_lt _ _ _ hj
  · show svalid (n + 0) ((initStats n i).getD j (Sum.inl false)) ∧
      sval (wiresFrom [] (List.ofFn y)) ((initStats n i).getD j (Sum.inl false)) = _
    rw [initStats, getD_ofFn_ge _ _ _ (by omega), getD_ofFn_ge _ _ _ (by omega)]
    exact ⟨trivial, rfl⟩

theorem main (n s : ℕ) (f : (Fin n → Bool) → Bool) (i : Fin n) (h : HasCircuitSize n f s)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))
    (hnc : ∃ x y : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update y i false)) :
    HasCircuitSize n (fun z => f (Function.update z i false)) (s - 1) := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hfan g0 hg0)
  have hevg : ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]
    rfl
  have hout : C.output ≠ i.val := by
    intro ho
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hevg, ← hevg, ho, getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp),
      getD_ofFn_lt _ _ _ i.isLt, getD_ofFn_lt _ _ _ i.isLt]
    simp
  have hread : ∃ g ∈ gs, i.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    obtain ⟨x, hx⟩ := hdep
    apply hx
    rw [← hevg, ← hevg]
    refine agree_off i.val gs _ _ (by simp) ?_ hno C.output hout
    intro j hj
    by_cases hjn : j < n
    · rw [getD_ofFn_lt _ _ _ hjn, getD_ofFn_lt _ _ _ hjn]
      have hne : (⟨j, hjn⟩ : Fin n) ≠ i := fun e => hj (by rw [← e])
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · rw [getD_ofFn_ge _ _ _ (by omega), getD_ofFn_ge _ _ _ (by omega)]
  obtain ⟨g, hg, hgi⟩ := hread
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Function.update y i false)))
        (elim n gs (initStats n i, [])) := fun y =>
    inv_elim n (List.ofFn y) (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init1 n i y)
  set acc := elim n gs (initStats n i, []) with hacc
  have hval : ∀ y : Fin n → Bool,
      sval (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Function.update y i false) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hk : (initStats n i).getD i.val (Sum.inl false) = Sum.inl false := by
    rw [initStats, getD_ofFn_lt _ _ _ i.isLt]
    simp
  have hcount := elim_count1 n i.val gs (initStats n i, []) hnok (by simp [initStats]) hk
  rw [← hacc] at hcount
  have hpos : 0 < gs.countP (fun g => decide (i.val ∈ g.inputs)) :=
    List.countP_pos_iff.2 ⟨g, hg, by simpa using hgi⟩
  have hlen : gs.length = C.size := by
    rw [hgs, List.length_map]; rfl
  have hsz' : C.size ≤ s := hsz
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hval x, ← hval y, hs]
    rfl
  | inr j =>
    refine ⟨⟨acc.2, j⟩, fun g hg => elim_ok n gs _ (by simp) g hg, ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      simp only [List.length_nil, zero_add] at hcount
      omega
    · intro y
      have e := hval y
      rw [hs] at e
      exact e


-- Relabelling the inputs of a circuit: each of the m old inputs becomes one of the k new
-- inputs or the constant false, read from a wire that never exists.

def optVal {k : ℕ} (z : Fin k → Bool) : Option (Fin k) → Bool
  | none => false
  | some t => z t

def rho (m k N : ℕ) (σ : Fin m → Option (Fin k)) (j : ℕ) : ℕ :=
  if h : j < m then
    (match σ ⟨j, h⟩ with
      | none => N
      | some t => t.val)
  else j - m + k

def rgate (m k N : ℕ) (σ : Fin m → Option (Fin k)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rho m k N σ)⟩

def relabel (m k : ℕ) (σ : Fin m → Option (Fin k)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rgate m k (k + C.gates.length) σ), rho m k (k + C.gates.length) σ C.output⟩

theorem rho_ne (m k N p : ℕ) (σ : Fin m → Option (Fin k)) (hN : k + p < N) (j : ℕ)
    (hj : j ≠ m + p) : rho m k N σ j ≠ k + p := by
  unfold rho
  split_ifs with h
  · cases hs : σ ⟨j, h⟩ with
    | none => simp only []; omega
    | some t => simp only []; have := t.isLt; omega
  · omega

theorem rho_top (m k N p : ℕ) (σ : Fin m → Option (Fin k)) :
    rho m k N σ (m + p) = k + p := by
  unfold rho
  rw [dif_neg (by omega)]
  omega

theorem relabel_inv (m k N : ℕ) (σ : Fin m → Option (Fin k)) :
    ∀ (gs : List Gate) (p : ℕ) (W W' : List Bool), W.length = m + p → W'.length = k + p →
      k + p + gs.length ≤ N →
      (∀ j, W'.getD (rho m k N σ j) false = W.getD j false) →
      ∀ j, (wiresFrom (gs.map (rgate m k N σ)) W').getD (rho m k N σ j) false
        = (wiresFrom gs W).getD j false := by
  intro gs
  induction gs with
  | nil => intro p W W' _ _ _ hinv; exact hinv
  | cons g gs ih =>
    intro p W W' hW hW' hN hinv
    have hval : (rgate m k N σ g).op.eval
          ((rgate m k N σ g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [rgate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hinv i
    have e1 : wiresFrom ((g :: gs).map (rgate m k N σ)) W'
        = wiresFrom (gs.map (rgate m k N σ))
            (W' ++ [(rgate m k N σ g).op.eval
              ((rgate m k N σ g).inputs.map fun i => W'.getD i false)]) := rfl
    have e2 : wiresFrom (g :: gs) W
        = wiresFrom gs (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    rw [e1, e2, hval]
    apply ih (p + 1)
    · simp [hW]; omega
    · simp [hW']; omega
    · simp at hN; omega
    · intro j
      by_cases hj : j = m + p
      · subst hj
        rw [rho_top, ← hW', ← hW, getD_snoc_eq, getD_snoc_eq]
      · have hne := rho_ne m k N p σ (by simp at hN; omega) j hj
        rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
        exact hinv j

theorem relabel_eval (m k : ℕ) (σ : Fin m → Option (Fin k)) (C : Circuit) (z : Fin k → Bool) :
    (relabel m k σ C).eval (List.ofFn z) = C.eval (List.ofFn fun j => optVal z (σ j)) := by
  show (wiresFrom (C.gates.map (rgate m k (k + C.gates.length) σ)) (List.ofFn z)).getD
      (rho m k (k + C.gates.length) σ C.output) false
    = (wiresFrom C.gates (List.ofFn fun j => optVal z (σ j))).getD C.output false
  apply relabel_inv m k (k + C.gates.length) σ C.gates 0 _ _ (by simp) (by simp) (by omega)
  intro j
  unfold rho
  split_ifs with h
  · rw [getD_ofFn_lt _ _ _ h]
    cases hs : σ ⟨j, h⟩ with
    | none =>
      simp only []
      rw [getD_ofFn_ge _ _ _ (by omega)]
      rfl
    | some t =>
      simp only []
      rw [getD_ofFn_lt _ _ _ t.isLt]
      rfl
  · rw [getD_ofFn_ge _ _ _ (by omega), getD_ofFn_ge _ _ _ (by omega)]

theorem relabel_size (m k : ℕ) (σ : Fin m → Option (Fin k)) (C : Circuit) :
    (relabel m k σ C).size = C.size := by
  simp [relabel, Circuit.size]

theorem relabel_fan (m k : ℕ) (σ : Fin m → Option (Fin k)) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (relabel m k σ C) := by
  intro g hg
  simp only [relabel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨hop, hlen⟩ := h g0 hg0
  exact ⟨hop, by simpa [rgate] using hlen⟩

-- The inputs of this step: nine inputs, the wire x0 OR x4, and a copy of wire x2.

def lst (x2 : Fin 11) (x5 : Fin 9 → Bool) : List Bool :=
  (List.ofFn x5 ++ [x5 0 || x5 4]) ++ [(List.ofFn x5 ++ [x5 0 || x5 4]).getD x2 false]

def emb (x2 : Fin 11) (x5 : Fin 9 → Bool) : Fin 11 → Bool :=
  fun k => (lst x2 x5).getD k false

theorem ofFn_emb (x2 : Fin 11) (x5 : Fin 9 → Bool) : List.ofFn (emb x2 x5) = lst x2 x5 := by
  apply List.ext_getElem
  · simp [lst]
  · intro j h1 h2
    simp only [List.getElem_ofFn, emb]
    rw [List.getD_eq_getElem _ _ h2]

def expand (z : Fin 8 → Bool) : Fin 9 → Bool :=
  ![z 0, z 1, z 2, z 3, false, z 4, z 5, z 6, z 7]

def sig0 : Fin 10 → Option (Fin 8) :=
  ![some 0, some 1, some 2, some 3, none, some 4, some 5, some 6, some 7, some 0]

def sig (x2 : Fin 11) (k : Fin 11) : Option (Fin 8) :=
  if h : k.val < 10 then sig0 ⟨k.val, h⟩
  else if h2 : x2.val < 10 then sig0 ⟨x2.val, h2⟩ else none

theorem emb_expand (x2 : Fin 11) (z : Fin 8 → Bool) (k : Fin 11) :
    emb x2 (expand z) k = optVal z (sig x2 k) := by
  fin_cases x2 <;> fin_cases k <;> first | rfl | simp [emb, lst, expand, sig, sig0, optVal]

theorem emb_four (x2 : Fin 11) (x5 : Fin 9 → Bool) : emb x2 x5 4 = x5 4 := by
  fin_cases x2 <;> rfl

theorem emb_ten (x5 : Fin 9 → Bool) : emb 4 x5 10 = x5 4 := rfl

theorem emb_agree (x2 : Fin 11) (x6 : Fin 9 → Bool) (h0 : x6 0 = true) (k : Fin 11)
    (hk : k ≠ 4) (hk' : k ≠ 10 ∨ x2 ≠ 4) :
    emb x2 x6 k = emb x2 (Function.update x6 4 true) k := by
  fin_cases x2 <;> fin_cases k <;> simp_all [emb, lst, Function.update_apply]

theorem upd_self {n : ℕ} (y : Fin n → Bool) (i : Fin n) (b : Bool) (h : y i = b) :
    Function.update y i b = y := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [h]
  · simp [Function.update_of_ne hk]

theorem final (C : Circuit) (x2 : Fin 11) (f : (Fin 9 → Bool) → Bool) (hfan : FanInTwo C)
    (hev : ∀ x5 : Fin 9 → Bool, C.eval (lst x2 x5) = f x5)
    (hdep : ∃ x6 : Fin 9 → Bool, x6 0 = true ∧ x6 4 = false ∧
      f x6 ≠ f (Function.update x6 4 true))
    (hnc : ∃ u v : Fin 8 → Bool, f (expand u) ≠ f (expand v)) :
    HasCircuitSize 8 (fun z => f (expand z)) (C.size - 1) := by
  let F : (Fin 11 → Bool) → Bool := fun y => C.eval (List.ofFn y)
  have hF : ∀ x5, F (emb x2 x5) = f x5 := by
    intro x5
    show C.eval (List.ofFn (emb x2 x5)) = f x5
    rw [ofFn_emb]
    exact hev x5
  have hq : ∀ z : Fin 8 → Bool, F (fun k => optVal z (sig x2 k)) = f (expand z) := by
    intro z
    have e : (fun k => optVal z (sig x2 k)) = emb x2 (expand z) :=
      funext fun k => (emb_expand x2 z k).symm
    rw [e, hF]
  have key : ∃ i : Fin 11, (∀ z : Fin 8 → Bool, optVal z (sig x2 i) = false) ∧
      ∃ y, F (Function.update y i false) ≠ F (Function.update y i true) := by
    obtain ⟨x6, h0, h4, hne⟩ := hdep
    have ha4 : emb x2 x6 4 = false := by rw [emb_four]; exact h4
    have hFne : F (emb x2 x6) ≠ F (emb x2 (Function.update x6 4 true)) := by
      rw [hF, hF]; exact hne
    by_cases hx : x2 = 4
    · subst hx
      let c := Function.update (emb 4 x6) 4 true
      by_cases hac : F (emb 4 x6) = F c
      · refine ⟨10, fun z => rfl, c, ?_⟩
        have hc10 : c 10 = false := by
          show Function.update (emb 4 x6) 4 true 10 = false
          rw [Function.update_of_ne (by decide), emb_ten]; exact h4
        rw [upd_self c 10 false hc10]
        have hb : Function.update c 10 true = emb 4 (Function.update x6 4 true) := by
          funext k
          simp only [c]
          by_cases k10 : k = 10
          · subst k10
            rw [Function.update_self, emb_ten, Function.update_self]
          · rw [Function.update_of_ne k10]
            by_cases k4 : k = 4
            · subst k4
              rw [Function.update_self, emb_four, Function.update_self]
            · rw [Function.update_of_ne k4]
              exact emb_agree 4 x6 h0 k k4 (Or.inl k10)
        rw [hb, ← hac]
        exact hFne
      · refine ⟨4, fun z => rfl, emb 4 x6, ?_⟩
        rw [upd_self _ 4 false ha4]
        exact hac
    · refine ⟨4, fun z => by fin_cases x2 <;> rfl, emb x2 x6, ?_⟩
      rw [upd_self _ 4 false ha4]
      have hb : Function.update (emb x2 x6) 4 true = emb x2 (Function.update x6 4 true) := by
        funext k
        by_cases k4 : k = 4
        · subst k4
          rw [Function.update_self, emb_four, Function.update_self]
        · rw [Function.update_of_ne k4]
          exact emb_agree x2 x6 h0 k k4 (Or.inr hx)
      rw [hb]
      exact hFne
  obtain ⟨i, hi0, hdepF⟩ := key
  have hfix : ∀ z : Fin 8 → Bool,
      Function.update (fun k => optVal z (sig x2 k)) i false = fun k => optVal z (sig x2 k) :=
    fun z => upd_self _ i false (hi0 z)
  have hncF : ∃ a b : Fin 11 → Bool,
      F (Function.update a i false) ≠ F (Function.update b i false) := by
    obtain ⟨u, v, huv⟩ := hnc
    refine ⟨fun k => optVal u (sig x2 k), fun k => optVal v (sig x2 k), ?_⟩
    rw [hfix, hfix, hq, hq]
    exact huv
  have hC : HasCircuitSize 11 F C.size := ⟨C, hfan, le_refl _, fun y => rfl⟩
  obtain ⟨D, hfanD, hszD, hevD⟩ := main 11 C.size F i hC hdepF hncF
  refine ⟨relabel 11 8 (sig x2) D, relabel_fan _ _ _ _ hfanD, ?_, ?_⟩
  · rw [relabel_size]; exact hszD
  · intro z
    rw [relabel_eval, hevD]
    show F (Function.update (fun k => optVal z (sig x2 k)) i false) = f (expand z)
    rw [hfix, hq]

end PEqualNP.Outside.L_meta_3588_aux

theorem PEqualNP.Outside.L_meta_3588 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (11 : ℕ)) (x3 : (Fin (9 : ℕ) → Bool) → Bool),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x5 : Fin (9 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))];         x1.eval (x6 ++ [x6.getD (↑x2) Bool.false]) = x3 x5) →       (∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.true ∧ x6 (4 : Fin (9 : ℕ)) = Bool.false ∧ x3 x6 ≠ x3 (Function.update x6 (4 : Fin (9 : ℕ)) Bool.true)) →         have x7 : (Fin (8 : ℕ) → Bool) → Bool := fun (x7 : Fin (8 : ℕ) → Bool) => x3 ![x7 (0 : Fin (8 : ℕ)), x7 (1 : Fin (8 : ℕ)), x7 (2 : Fin (8 : ℕ)), x7 (3 : Fin (8 : ℕ)), Bool.false, x7 (4 : Fin (8 : ℕ)), x7 (5 : Fin (8 : ℕ)), x7 (6 : Fin (8 : ℕ)), x7 (7 : Fin (8 : ℕ))];         (∃ (x8 : Fin (8 : ℕ) → Bool) (x9 : Fin (8 : ℕ) → Bool), x7 x8 ≠ x7 x9) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x7 (x1.size - (1 : ℕ)) := by
  intro C x2 f hfan hev hdep x7 hnc
  exact PEqualNP.Outside.L_meta_3588_aux.final C x2 f hfan hev hdep hnc
