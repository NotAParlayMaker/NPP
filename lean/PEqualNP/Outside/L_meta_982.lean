import Mathlib
import PEqualNP.Defs

-- Based in part on sanchan's L-meta-927 circuit proofs, Apache-2.0.
-- Row numbers follow the order of the 31 conjuncts, starting at zero.
-- A row projection commutes with each Boolean gate. Several search branches
-- can therefore use the same six-input lower bound. A lookup proposes a
-- target board, and the checker compares the projected wires up to permutation
-- before it uses the lower bound for that board.
namespace PEqualNP.Outside.L_meta_982_aux

abbrev restrictMap0 := (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | 5 => (0 : Fin 3) | _ => (0 : Fin 3))
abbrev restrictMap1 := (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6))
abbrev restrictMap2 := (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6))
abbrev restrictMap3 := (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | 3 => (0 : Fin 3) | 4 => (0 : Fin 3) | _ => (0 : Fin 3))
abbrev restrictMap4 := (fun i : Fin 5 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | _ => (0 : Fin 5))
abbrev restrictMap5 := (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 6) | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 4 => (4 : Fin 6) | 5 => (5 : Fin 6) | _ => (0 : Fin 6))
abbrev restrictMap6 := (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | 5 => (0 : Fin 5) | _ => (0 : Fin 5))
abbrev restrictMap7 := (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 4 => (4 : Fin 5) | _ => (0 : Fin 5))
abbrev eS0 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (1, 2)]
abbrev eS1 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]
abbrev eS2 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 3), (1, 2)]
abbrev eS3 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]
abbrev eS4 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]
abbrev eS5 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]
abbrev eS6 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 4), (1, 2), (4, 6)]
abbrev eS7 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (1, 2), (1, 4), (4, 6)]
abbrev eS8 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 6), (3, 4)]
abbrev eS9 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]
abbrev eS10 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]
abbrev eS11 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]
abbrev eS12 {n : Nat} [NeZero n] : List (Fin n × Fin n) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]
abbrev gF0 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))
abbrev gF1 := (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2))
abbrev gF2 := (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4))
abbrev gF3 := (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4))
abbrev gF4 := (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4))
abbrev gF5 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5))
abbrev gF6 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5))
abbrev gF7 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5))
abbrev gF8 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5))
abbrev gF9 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5))
abbrev gF10 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))
abbrev gF11 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4))
abbrev gF12 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4))
abbrev gF13 := (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5))
abbrev gF14 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6))
abbrev gF15 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6))
abbrev gF16 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6))
abbrev gF17 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6))
abbrev gF18 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6))
abbrev gF19 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6))
abbrev gF20 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5))
abbrev gF21 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4))
abbrev gF22 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4))
abbrev gF23 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6))
abbrev gF24 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4))
abbrev gF25 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6))
abbrev gF26 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6))
abbrev gF27 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6))
abbrev gF28 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6))
abbrev gF29 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6))
abbrev gF30 := (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6))



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool



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

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
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

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

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

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
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

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
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
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
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

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
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

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
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
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
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
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
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
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

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
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
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
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
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
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
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
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
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
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

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

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
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
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
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
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
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



def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

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
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
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
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
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
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
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
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
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
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k+k by omega, show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
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
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
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
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
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

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
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
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih => simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | (grw [← Nat.add_assoc, ← hand]; exact ih')
            | (grw [← Nat.add_assoc, ← hor]; exact ih')

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
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

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem spOK {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem sj {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
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
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
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

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

def StGen (k : Nat) (xs : List Nat) (PT : Nat → Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => xs
  | d + 1, s, j =>
    let e := fld (PT s) 18 j
    mv (mask k) (e % 4096) (StGen k xs PT d (s + 1) (e / 4096))

def Sgen (k cap : Nat) (xs : List Nat) (PT : Nat → Nat) (s j : Nat) : List Nat :=
  StGen k xs PT (cap - s) s j

def idxGen (NN HT : Nat → Nat) (s : Nat) (zs : List Nat) : Nat :=
  bsr (HT s) 32 (hk zs) 10 0 (NN s)

theorem prove_base (n k cap : ℕ) (f : BFn n) (rows xs pool : List ℕ)
    (NN HT PT : ℕ → ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hNcap : 0 < NN cap)
    (hchk : ∀ s ≤ cap, ∀ i < NN s,
      bar k (Sgen k cap xs PT) NN (idxGen NN HT) id pool s i = true) :
    ∀ s : ℕ, HasCircuitSize n f s → cap + 1 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hmask : mask k = 2 ^ rows.length - 1 := by rw [hlen]; rfl
  have hr : NatRun (mask k) (encL f rows) s' (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hsub' : (ws.map fun a => encL a rows).Sublist xs := by
    rw [← hxs]; exact hsub.map _
  by_cases he : (ws.map fun a => encL a rows) = xs
  · rw [he] at hr
    cases hxs_nil : xs with
    | nil =>
      rw [hxs_nil] at hr
      have hc := required hr
      have hne : cov k [] = 0 := rfl
      rw [hne] at hc
      have hlo : lo k ≠ 0 := by
        cases k with
        | zero =>
          simp [goal, lo] at hgoal
          obtain ⟨y, y', hne'⟩ := hnc
          have h0 : rows.length = 0 := hlen
          have hnil : rows = [] := List.eq_nil_of_length_eq_zero h0
          rw [hnil] at hxs
          have hxs0 : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun _ => 0) = [] := by
            simpa [encL, hxs_nil] using hxs
          have hn0 : n = 0 := by simpa using congrArg List.length hxs0
          subst hn0
          exact absurd (Subsingleton.elim y y') (fun e => hne' (e ▸ rfl))
        | succ k' =>
          simp only [lo]
          have : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
          rw [pow_succ]; omega
      simp at hc
      exact hlo hc.symm
    | cons a r =>
      rw [hxs_nil] at hr
      have hcap : NatRun (mask k) (goal k) cap (a :: r) := extend_run hr (by omega)
      rw [← hxs_nil] at hcap
      have hS0 : Sgen k cap xs PT cap 0 = xs := by simp [Sgen, StGen]
      rw [← hS0] at hcap
      exact bar_all (fun h => h) hchk cap le_rfl 0 hNcap hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)



-- Base case K3 (n=3, cap=3, k=9, states=1, pool=1)
def f_K3 : BFn 3 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)
def rows_K3 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 3, 5, 6, 3, 5, 6, 3, 5, 6]
def xs_K3 : List ℕ := [0x1b607, 0x2da38, 0x36dc0]
def pool_K3 : List ℕ := [0xc000180b02809]
def NN_K3 : ℕ → ℕ
  | 3 => 1
  | _ => 0
def HT_K3 : ℕ → ℕ
  | 3 => 0xc03a13c3
  | _ => 0
def PT_K3 : ℕ → ℕ
  | _ => 0
def Z_K3 (s : ℕ) := bar 9 (Sgen 9 3 xs_K3 PT_K3) NN_K3 (idxGen NN_K3 HT_K3) id pool_K3 s
theorem z_K3_0 : span (Z_K3 0) 0 0 = true := rfl
theorem z_K3_1 : span (Z_K3 1) 0 0 = true := rfl
theorem z_K3_2 : span (Z_K3 2) 0 0 = true := rfl
theorem h_K3_3_0 : span (Z_K3 3) 1 0 = true := by decide +kernel
theorem z_K3_3 : span (Z_K3 3) 1 0 = true := h_K3_3_0
theorem base_K3 : ∀ s : ℕ, HasCircuitSize 3 f_K3 s → 4 ≤ s := by
  refine prove_base 3 9 3 f_K3 rows_K3 xs_K3 pool_K3 NN_K3 HT_K3 PT_K3
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_K3_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3_3 i (Nat.zero_le i) hi
    )

-- Base case C5 (n=5, cap=6, k=50, states=7, pool=5)
def f_C5 : BFn 5 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)
def rows_C5 : List ℕ := [1, 1, 2, 2, 4, 4, 6, 6, 6, 6, 6, 6, 6, 6, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 3, 5, 3, 10, 5, 20, 3, 5, 7, 10, 14, 20, 22, 24, 10, 24, 3, 5, 10, 11, 13, 20, 24, 25, 3, 5, 10, 13, 14, 20, 24, 28, 20, 24, 3, 5, 10, 19, 20, 21, 24, 25, 3, 5, 10, 19, 20, 22, 24, 26]
def xs_C5 : List ℕ := [0xbab02e6c075c03fc00ff0003, 0xad0d054355d37fc0000003fcc, 0x32326e8c876c80000ff003ff0, 0xc4c4b737398200000ffffc000, 0xf8f8f8382e083ffff00000000]
def pool_C5 : List ℕ := [0x18000a8370c833, 0x38020883f0c835, 0x80040403f0cc37, 0x800060350cc32, 0x800e018370d43f]
def NN_C5 : ℕ → ℕ
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT_C5 : ℕ → ℕ
  | 5 => 0xc6e3b2e569d2916d684aef2d399569702839ea7a276164fc
  | 6 => 0x2839ea7a
  | _ => 0
def PT_C5 : ℕ → ℕ
  | 5 => 0x40c0104004040100000000102
  | _ => 0
def Z_C5 (s : ℕ) := bar 50 (Sgen 50 6 xs_C5 PT_C5) NN_C5 (idxGen NN_C5 HT_C5) id pool_C5 s
theorem z_C5_0 : span (Z_C5 0) 0 0 = true := rfl
theorem z_C5_1 : span (Z_C5 1) 0 0 = true := rfl
theorem z_C5_2 : span (Z_C5 2) 0 0 = true := rfl
theorem z_C5_3 : span (Z_C5 3) 0 0 = true := rfl
theorem z_C5_4 : span (Z_C5 4) 0 0 = true := rfl
theorem h_C5_5_0 : span (Z_C5 5) 6 0 = true := by decide +kernel
theorem z_C5_5 : span (Z_C5 5) 6 0 = true := h_C5_5_0
theorem h_C5_6_0 : span (Z_C5 6) 1 0 = true := by decide +kernel
theorem z_C5_6 : span (Z_C5 6) 1 0 = true := h_C5_6_0
theorem base_C5 : ∀ s : ℕ, HasCircuitSize 5 f_C5 s → 7 ≤ s := by
  refine prove_base 5 50 6 f_C5 rows_C5 xs_C5 pool_C5 NN_C5 HT_C5 PT_C5
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_C5_6 i (Nat.zero_le i) hi
    )

-- Base case BOWTIE (n=5, cap=7, k=50, states=79, pool=10)
def f_BOWTIE : BFn 5 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)
def rows_BOWTIE : List ℕ := [1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 3, 5, 6, 9, 17, 24, 3, 6, 5, 6, 9, 24, 3, 5, 6, 9, 11, 14, 17, 24, 26, 3, 5, 6, 9, 13, 14, 17, 24, 28, 17, 24, 3, 5, 6, 9, 17, 19, 22, 24, 26, 3, 5, 6, 9, 17, 21, 22, 24, 28]
def xs_BOWTIE : List ℕ := [0x1d8ed2d96d56c00000000003f, 0x22d9412cd4b1401ff001ff0c0, 0xb31189b098e1bfe003fe00300, 0xc4622dc6e30a000003ffffc00, 0xf87c3e07020c3ffffc0000000]
def pool_BOWTIE : List ℕ := [0x80000a4340cc32, 0x780a000360d437, 0x5400030340c833, 0x8000030370c836, 0x3000080370c835, 0x54000a4370cc35, 0xa400054370cc36, 0xa400080340c833, 0x3000054340cc32, 0x2006000330c834]
def NN_BOWTIE : ℕ → ℕ
  | 4 => 2
  | 5 => 40
  | 6 => 36
  | 7 => 1
  | _ => 0
def HT_BOWTIE : ℕ → ℕ
  | 4 => 0xe69f9bc42160bc5f
  | 5 => 0xf742a3d0f3d6a6caf2c4f573e8b66066e180f3e4dc87be0edbeab3c2d93b4845d6c8153bd3b86897cf20682cc92e1222c36e694fc2da43cfb73fc6f7b64bf507b61f6228b3b81b1bb2c6c34ba8357aafa51ea19ca01014059f6d175f992962fa933e75078d7ecc3487246ed6697d7a4456dfe4dc558d03dd549ad51f4869b93243677bab3e0dcfd73c0e3e7f28b49293203432401c85f03b16c64768158068a1
  | 6 => 0xf8103679f7ee878cf2c4f573f084fb7be4e1031be2a67339d9ce2dd4d311441ec7bfd293c7633531c6b10786bd88bbf8b2c6c34bae58d960ad239bdb9f6d175f99876a0897388465933e7507917398168d7ecc348aee859b83a2b2267f1563cf7cb80320792278b673133ce4697d7a4463f740d054f0553f4b2540302c47248c231776e01a45f6430cea2d5a081c1522
  | 7 => 0x697d7a44
  | _ => 0
def PT_BOWTIE : ℕ → ℕ
  | 4 => 0xc847302
  | 5 => 0x70d40420520409410188cc1110170d0003213c406234000d4111023c409f3033c410a3406cd0152032040052306ccc1b35020404034020410810364940031028d42235028cc1c33030885f3055c40941027cc1111033c40c0303
  | 6 => 0x38c80e100040804040390c0f41010000e3003900050103cc00503004000f3203c8001010100c0e420041004010040c0e31010080f4303c840e2003cc40000039040f4203c400f40014000504014080e21
  | _ => 0
def Z_BOWTIE (s : ℕ) := bar 50 (Sgen 50 7 xs_BOWTIE PT_BOWTIE) NN_BOWTIE (idxGen NN_BOWTIE HT_BOWTIE) id pool_BOWTIE s
theorem z_BOWTIE_0 : span (Z_BOWTIE 0) 0 0 = true := rfl
theorem z_BOWTIE_1 : span (Z_BOWTIE 1) 0 0 = true := rfl
theorem z_BOWTIE_2 : span (Z_BOWTIE 2) 0 0 = true := rfl
theorem z_BOWTIE_3 : span (Z_BOWTIE 3) 0 0 = true := rfl
theorem h_BOWTIE_4_0 : span (Z_BOWTIE 4) 2 0 = true := by decide +kernel
theorem z_BOWTIE_4 : span (Z_BOWTIE 4) 2 0 = true := h_BOWTIE_4_0
theorem h_BOWTIE_5_0 : span (Z_BOWTIE 5) 12 0 = true := by decide +kernel
theorem h_BOWTIE_5_12 : span (Z_BOWTIE 5) 12 12 = true := by decide +kernel
theorem h_BOWTIE_5_24 : span (Z_BOWTIE 5) 12 24 = true := by decide +kernel
theorem h_BOWTIE_5_36 : span (Z_BOWTIE 5) 4 36 = true := by decide +kernel
theorem z_BOWTIE_5 : span (Z_BOWTIE 5) 40 0 = true := by with_reducible exact (sj (sj h_BOWTIE_5_0 h_BOWTIE_5_12) (sj h_BOWTIE_5_24 h_BOWTIE_5_36))
theorem h_BOWTIE_6_0 : span (Z_BOWTIE 6) 12 0 = true := by decide +kernel
theorem h_BOWTIE_6_12 : span (Z_BOWTIE 6) 12 12 = true := by decide +kernel
theorem h_BOWTIE_6_24 : span (Z_BOWTIE 6) 12 24 = true := by decide +kernel
theorem z_BOWTIE_6 : span (Z_BOWTIE 6) 36 0 = true := by with_reducible exact (sj h_BOWTIE_6_0 (sj h_BOWTIE_6_12 h_BOWTIE_6_24))
theorem h_BOWTIE_7_0 : span (Z_BOWTIE 7) 1 0 = true := by decide +kernel
theorem z_BOWTIE_7 : span (Z_BOWTIE 7) 1 0 = true := h_BOWTIE_7_0
theorem base_BOWTIE : ∀ s : ℕ, HasCircuitSize 5 f_BOWTIE s → 8 ≤ s := by
  refine prove_base 5 50 7 f_BOWTIE rows_BOWTIE xs_BOWTIE pool_BOWTIE NN_BOWTIE HT_BOWTIE PT_BOWTIE
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_BOWTIE_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_3 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_4 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_5 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_6 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_BOWTIE_7 i (Nat.zero_le i) hi
    )

-- Base case NET (n=6, cap=7, k=72, states=26, pool=9)
def f_TwoK3 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_TwoK3 : List ℕ := [1, 1, 2, 2, 4, 4, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 3, 6, 5, 6, 24, 40, 3, 5, 6, 11, 13, 24, 25, 40, 41, 48, 3, 5, 6, 11, 14, 24, 26, 40, 42, 48, 3, 5, 6, 13, 14, 24, 28, 40, 44, 48, 24, 48, 3, 5, 6, 19, 21, 24, 25, 40, 48, 49, 3, 5, 6, 19, 22, 24, 26, 40, 48, 50, 3, 5, 6, 21, 22, 24, 28, 40, 48, 52, 40, 48, 3, 5, 6, 24, 35, 37, 40, 41, 48, 49, 3, 5, 6, 24, 35, 38, 40, 42, 48, 50, 3, 5, 6, 24, 37, 38, 40, 44, 48, 52]
def xs_TwoK3 : List ℕ := [0x4c13acc02c0b96c02c0b56c5c00003ff000003ff000003ff03, 0x96b50540565d0340555d034b400ffc00000ffc00000ffc000c, 0xad8260989781605857816058ebff000003ff000003ff0000030, 0x320c8321380e03817e1f87e3000000000000000003fffffffc0, 0xc2308c22de378de3982609810000000003fffffffc000000000, 0xfc3f0fc3e0380e02e0380e0203fffffffc00000000000000000]
def pool_TwoK3 : List ℕ := [0xc8280f06919c66, 0x9806118771b46c, 0x48080706919c66, 0x10020006719869, 0x10000086919867]
def NN_TwoK3 : ℕ → ℕ
  | 4 => 2
  | 5 => 12
  | 6 => 58
  | 7 => 49
  | 8 => 1
  | _ => 0
def HT_TwoK3 : ℕ → ℕ
  | 4 => 0x4d8c177f15c49257
  | 5 => 0xf0e5633ee7484b31a8d065f8979d3f4793f63bc08671bd54863d7f2181afece53dbda1882359e6cf198b67e50853723f
  | 6 => 0xfff2feb1fbb42ec1f805c600f741e864f4956378f1569e11edfc6b6de33c240fde836f10ddbefff4d6536b5ed4908d11cfe8ef31cdab9dedccacded6cbc2310ec568bed5ba4ccae7ba49c705b387ff19b114f671ae607e3ca911d87ca7a10ad8a32309d196921a7d95b4c51295798f3993292937929c19388caa887f8a7b658488976d8f868eb994859c9f8d807d69288041d1617e30b21078e2632b77386d21729f95276e1d55396b13cd37690c11976636a31c53d68f2d49c3ea2044353bb331b2062a31897ba42cb2ed7d28204f2e24d3f01c20c002c41f2967b51d792b3f1c8bb31a0e1442b5
  | 7 => 0xf805c600f35b4616e5e0c18ae59fd215e4eeedf8ddbefff4da55ffa0cddc75e9cbb17652ca742a1bc87d2041c780807ac4cd528ec4852d77c0d065f9b72faa58b33f4aeba911d87ca32712718b7dca57859c9f8d83d6d5dc839707388036fa067963bc88788c92f66f6896bd6edcc4e06e513d8b6cfc2284600dbbaa4eac3ae54ab8d6c54a3175144723967344353bb343db4bcc39a4161334e138ec345fccb131897ba42eb8073529c048df29a9ef5c26bc3c25229404c81f2967b5108017bc05304534
  | 8 => 0xa911d87c
  | _ => 0
def PT_TwoK3 : ℕ → ℕ
  | 4 => 0xc404301
  | 5 => 0x38885422160d441321c8c86f32148885820504880f32164c499202
  | 6 => 0x6480c21057c404e32130c84e350a8d00c30630c15f10438d81c10200d00335020406a36078d802101704143303a8d42020600c40210300d40336078d40e34034405a22130c0de3040cc85e32170000810200cc1d20634411a20378c0c2102a8cc1626020410210438cc0d000048c08000ac408c3040cd00d10508000036000c848105
  | 7 => 0x101039080e5003d440f40004100e20038c00f5203cc40f3001404050003d4005020140c0f53000000e5303d500105039440f2003c840f23010040f43039040504039480e23039000402010140e43004000e54010100f42038c401030100c0f4101000050503884010203c400e10
  | _ => 0
def Z_TwoK3 (s : ℕ) := bar 102 (Sgen 102 8 xs_TwoK3 PT_TwoK3) NN_TwoK3 (idxGen NN_TwoK3 HT_TwoK3) id pool_TwoK3 s
theorem z_TwoK3_0 : span (Z_TwoK3 0) 0 0 = true := rfl
theorem z_TwoK3_1 : span (Z_TwoK3 1) 0 0 = true := rfl
theorem z_TwoK3_2 : span (Z_TwoK3 2) 0 0 = true := rfl
theorem z_TwoK3_3 : span (Z_TwoK3 3) 0 0 = true := rfl
theorem h_TwoK3_4_0 : span (Z_TwoK3 4) 2 0 = true := by decide +kernel
theorem z_TwoK3_4 : span (Z_TwoK3 4) 2 0 = true := h_TwoK3_4_0
theorem h_TwoK3_5_0 : span (Z_TwoK3 5) 12 0 = true := by decide +kernel
theorem z_TwoK3_5 : span (Z_TwoK3 5) 12 0 = true := h_TwoK3_5_0
theorem h_TwoK3_6_0 : span (Z_TwoK3 6) 12 0 = true := by decide +kernel
theorem h_TwoK3_6_12 : span (Z_TwoK3 6) 12 12 = true := by decide +kernel
theorem h_TwoK3_6_24 : span (Z_TwoK3 6) 12 24 = true := by decide +kernel
theorem h_TwoK3_6_36 : span (Z_TwoK3 6) 12 36 = true := by decide +kernel
theorem h_TwoK3_6_48 : span (Z_TwoK3 6) 10 48 = true := by decide +kernel
theorem z_TwoK3_6 : span (Z_TwoK3 6) 58 0 = true := by with_reducible exact (sj (sj h_TwoK3_6_0 h_TwoK3_6_12) (sj h_TwoK3_6_24 (sj h_TwoK3_6_36 h_TwoK3_6_48)))
theorem h_TwoK3_7_0 : span (Z_TwoK3 7) 12 0 = true := by decide +kernel
theorem h_TwoK3_7_12 : span (Z_TwoK3 7) 12 12 = true := by decide +kernel
theorem h_TwoK3_7_24 : span (Z_TwoK3 7) 12 24 = true := by decide +kernel
theorem h_TwoK3_7_36 : span (Z_TwoK3 7) 12 36 = true := by decide +kernel
theorem h_TwoK3_7_48 : span (Z_TwoK3 7) 1 48 = true := by decide +kernel
theorem z_TwoK3_7 : span (Z_TwoK3 7) 49 0 = true := by with_reducible exact (sj (sj h_TwoK3_7_0 h_TwoK3_7_12) (sj h_TwoK3_7_24 (sj h_TwoK3_7_36 h_TwoK3_7_48)))
theorem h_TwoK3_8_0 : span (Z_TwoK3 8) 1 0 = true := by decide +kernel
theorem z_TwoK3_8 : span (Z_TwoK3 8) 1 0 = true := h_TwoK3_8_0
theorem base_TwoK3 : ∀ s : ℕ, HasCircuitSize 6 f_TwoK3 s → 9 ≤ s := by
  refine prove_base 6 102 8 f_TwoK3 rows_TwoK3 xs_TwoK3 pool_TwoK3 NN_TwoK3 HT_TwoK3 PT_TwoK3
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_TwoK3_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_3 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_4 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_5 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_6 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_7 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_TwoK3_8 i (Nat.zero_le i) hi
    )

-- Base case K3C5 (n=6, cap=8, k=88, states=111, pool=5)
def f_K3C5 : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def rows_K3C5 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 9, 3, 6, 18, 5, 6, 9, 40, 3, 5, 6, 9, 11, 14, 18, 26, 40, 42, 48, 13, 14, 44, 18, 48, 3, 5, 6, 9, 18, 19, 21, 25, 40, 48, 49, 21, 22, 52, 25, 26, 56, 3, 5, 6, 9, 18, 29, 30, 40, 48, 60, 40, 48, 3, 5, 6, 9, 18, 35, 37, 40, 41, 48, 49, 3, 5, 6, 9, 18, 35, 38, 40, 42, 48, 50, 3, 5, 6, 9, 18, 37, 38, 40, 44, 48, 52]
def xs_K3C5 : List ℕ := [0x560aeb5815933ac206d4f000003ff80001ffc000007, 0xab5d41a82aa40d54bd4b9001ffc00000000001ffc38, 0xacc118231330e118e098d2ffe000001ff8e000e000c0, 0x310620c437470620eee304000000001fff0000ffff00, 0xc21843085b87fbc3130020000000001fffffff000000, 0xfc1f83f07c049c029c0200ffffffffe0000000000000]
def pool_K3C5 : List ℕ := [0x108371345c16458, 0xd418028611746c, 0xd4080686c16861, 0x1803000591605c, 0x180000c5c16059]
def NN_K3C5 : ℕ → ℕ
  | 5 => 2
  | 6 => 59
  | 7 => 49
  | 8 => 1
  | _ => 0
def HT_K3C5 : ℕ → ℕ
  | 5 => 0xaf7f705075df09eb
  | 6 => 0xff05e072f727b177f3068765eaa33932db11b933d8cc5b6dcd35058ccc15227dca2f76a5c83ad31bc7250273c15a0367b4a0336cb10a8789afa7431baca18245a8900a13a2695142a1496e339ff66ae49c594e299b4c90679920e7e69912aafc9669f83595b74714954a15269059f51c8b53f7cd85bd41f47c32030e752ab69a72c697296f78934d6d024dd56a88734369689034692b5d8d653017b36252b02e43fac3934359dbb44239f8a53d49d89b37e19f5a2dcc7be728df8ae4233bb3a41f61f4541e1edb431b5f2e0917711a07161b410c15acbf2f11a788f510e7b25a08bdd900062edfb000979a5e
  | 7 => 0xfad5aba9f2eecca3e97ae7ace6bcb686e3778b7fe03ffe4fd963b263d4da459cd3c109c0d32c8367cea5d07ecbb58782cb9bad62c03ecc65bd3d402baec4164fab8da282aa9335c4a77738ef9ff66ae49a72143c980ef4d38d5b9238853ae9e8813088c1801c66e67c90fda2795c361d752ab69a692b5d8d652373366061f0715bb0fd5d57c5b116504f73f14825eea6435ca5264359dbb44239f8a53d49d89b38731eb53663a28d345f23502a623341161b410c13fb51330a946a4a0112919d00f8fd3a
  | 8 => 0x161b410c
  | _ => 0
def PT_K3C5 : ℕ → ℕ
  | 5 => 0x1cc848302
  | 6 => 0x141013cd413101bcc0d533040d80b10128406f3604c410910144c12c23054d01130554d42e3402c410a10510400910444c181321a8814b10384818a10324409634070d41635010411536028411a3052440c910510409035058d82e3031040c410510404135004d01033040d02f30404d80c22104cc01310b8d81130358cc2f35064982e350
  | 7 => 0xe510394c0e210100c0f10014100f50010140e40014080501038c40f54014000f4103d440f4003cc00401004000e2303cc40e4203d0c0404010080e10039040104004080e50039500e300390c0f53039480f210040c0105004040f20010000f4203d4800000140c0f23038800505
  | _ => 0
def Z_K3C5 (s : ℕ) := bar 88 (Sgen 88 8 xs_K3C5 PT_K3C5) NN_K3C5 (idxGen NN_K3C5 HT_K3C5) id pool_K3C5 s
theorem z_K3C5_0 : span (Z_K3C5 0) 0 0 = true := rfl
theorem z_K3C5_1 : span (Z_K3C5 1) 0 0 = true := rfl
theorem z_K3C5_2 : span (Z_K3C5 2) 0 0 = true := rfl
theorem z_K3C5_3 : span (Z_K3C5 3) 0 0 = true := rfl
theorem z_K3C5_4 : span (Z_K3C5 4) 0 0 = true := rfl
theorem h_K3C5_5_0 : span (Z_K3C5 5) 2 0 = true := by decide +kernel
theorem z_K3C5_5 : span (Z_K3C5 5) 2 0 = true := h_K3C5_5_0
theorem h_K3C5_6_0 : span (Z_K3C5 6) 12 0 = true := by decide +kernel
theorem h_K3C5_6_12 : span (Z_K3C5 6) 12 12 = true := by decide +kernel
theorem h_K3C5_6_24 : span (Z_K3C5 6) 12 24 = true := by decide +kernel
theorem h_K3C5_6_36 : span (Z_K3C5 6) 12 36 = true := by decide +kernel
theorem h_K3C5_6_48 : span (Z_K3C5 6) 11 48 = true := by decide +kernel
theorem z_K3C5_6 : span (Z_K3C5 6) 59 0 = true := by with_reducible exact (sj (sj h_K3C5_6_0 h_K3C5_6_12) (sj h_K3C5_6_24 (sj h_K3C5_6_36 h_K3C5_6_48)))
theorem h_K3C5_7_0 : span (Z_K3C5 7) 12 0 = true := by decide +kernel
theorem h_K3C5_7_12 : span (Z_K3C5 7) 12 12 = true := by decide +kernel
theorem h_K3C5_7_24 : span (Z_K3C5 7) 12 24 = true := by decide +kernel
theorem h_K3C5_7_36 : span (Z_K3C5 7) 12 36 = true := by decide +kernel
theorem h_K3C5_7_48 : span (Z_K3C5 7) 1 48 = true := by decide +kernel
theorem z_K3C5_7 : span (Z_K3C5 7) 49 0 = true := by with_reducible exact (sj (sj h_K3C5_7_0 h_K3C5_7_12) (sj h_K3C5_7_24 (sj h_K3C5_7_36 h_K3C5_7_48)))
theorem h_K3C5_8_0 : span (Z_K3C5 8) 1 0 = true := by decide +kernel
theorem z_K3C5_8 : span (Z_K3C5 8) 1 0 = true := h_K3C5_8_0
theorem base_K3C5 : ∀ s : ℕ, HasCircuitSize 6 f_K3C5 s → 9 ≤ s := by
  refine prove_base 6 88 8 f_K3C5 rows_K3C5 xs_K3C5 pool_K3C5 NN_K3C5 HT_K3C5 PT_K3C5
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => spOK z_K3C5_0 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_1 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_2 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_3 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_4 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_5 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_6 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_7 i (Nat.zero_le i) hi
      · exact fun i hi => spOK z_K3C5_8 i (Nat.zero_le i) hi
    )




def gfn {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) : BFn n :=
  fun x => A.any (fun a => x a) || E.any (fun e => x e.1 && x e.2)

def Eb_K3 : List (Fin 3 × Fin 3) := [(0,1),(0,2),(1,2)]
def Eb_C5 : List (Fin 5 × Fin 5) := [(0,1),(0,2),(1,3),(2,4),(3,4)]
def Eb_BOWTIE : List (Fin 5 × Fin 5) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)]
def Eb_TwoK3 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(1,2),(3,4),(3,5),(4,5)]
def Eb_K3C5 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5)]

theorem base_K3_gfn : ∀ s, HasCircuitSize 3 (gfn [] Eb_K3) s → 4 ≤ s := by
  have : gfn [] Eb_K3 = f_K3 := by funext x; simp [gfn, Eb_K3, f_K3, Bool.or_assoc]
  rw [this]; exact base_K3

theorem base_C5_gfn : ∀ s, HasCircuitSize 5 (gfn [] Eb_C5) s → 7 ≤ s := by
  have : gfn [] Eb_C5 = f_C5 := by funext x; simp [gfn, Eb_C5, f_C5, Bool.or_assoc]
  rw [this]; exact base_C5

theorem base_BOWTIE_gfn : ∀ s, HasCircuitSize 5 (gfn [] Eb_BOWTIE) s → 8 ≤ s := by
  have : gfn [] Eb_BOWTIE = f_BOWTIE := by funext x; simp [gfn, Eb_BOWTIE, f_BOWTIE, Bool.or_assoc]
  rw [this]; exact base_BOWTIE

theorem base_TwoK3_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_TwoK3) s → 9 ≤ s := by
  have : gfn [] Eb_TwoK3 = f_TwoK3 := by funext x; simp [gfn, Eb_TwoK3, f_TwoK3, Bool.or_assoc]
  rw [this]; exact base_TwoK3

theorem base_K3C5_gfn : ∀ s, HasCircuitSize 6 (gfn [] Eb_K3C5) s → 9 ≤ s := by
  have : gfn [] Eb_K3C5 = f_K3C5 := by funext x; simp [gfn, Eb_K3C5, f_K3C5, Bool.or_assoc]
  rw [this]; exact base_K3C5

def dedupAux {α : Type} [BEq α] : List α → List α → List α
  | [], acc => acc.reverse
  | a :: t, acc => if acc.contains a then dedupAux t acc else dedupAux t (a :: acc)

def dedup {α : Type} [BEq α] (l : List α) : List α := dedupAux l []

theorem mem_dedupAux {α : Type} [DecidableEq α] : ∀ (l acc : List α) (x : α),
    x ∈ dedupAux l acc ↔ x ∈ l ∨ x ∈ acc
  | [], acc, x => by simp [dedupAux]
  | a :: t, acc, x => by
    simp only [dedupAux]
    by_cases h : acc.contains a = true
    · simp only [h, ↓reduceIte, mem_dedupAux, List.mem_cons]
      have ha : a ∈ acc := by simpa using h
      constructor
      · rintro (ht | hacc)
        · exact Or.inl (Or.inr ht)
        · exact Or.inr hacc
      · rintro ((rfl | ht) | hacc)
        · exact Or.inr ha
        · exact Or.inl ht
        · exact Or.inr hacc
    · simp only [h, Bool.false_eq_true, ↓reduceIte, mem_dedupAux, List.mem_cons]
      tauto

theorem mem_dedup {α : Type} [DecidableEq α] (l : List α) (x : α) :
    x ∈ dedup l ↔ x ∈ l := by
  simpa [dedup] using mem_dedupAux l [] x

def fix0A {n : ℕ} (A : List (Fin n)) (p : Fin n) : List (Fin n) :=
  A.filter (· != p)

def fix0E {n : ℕ} (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n × Fin n) :=
  E.filter (fun e => e.1 != p && e.2 != p)

def nbrs {n : ℕ} (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n) :=
  E.filterMap (fun e => if e.1 == p then some e.2 else if e.2 == p then some e.1 else none)

def fix1A {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n) :=
  dedup (A ++ nbrs E p)

def fix1E {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) : List (Fin n × Fin n) :=
  let A1 := fix1A A E p
  E.filter (fun e => e.1 != p && e.2 != p && !A1.contains e.1 && !A1.contains e.2)

def depCheck {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) : Bool :=
  A.contains p ||
    (E.all (fun e => e.1 != e.2) &&
      E.any (fun e => (e.1 == p && !A.contains e.2) || (e.2 == p && !A.contains e.1)))

def isoCheck {n k : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k)) (π : Fin n → Fin k) : Bool :=
  E.all (fun e => Eb.any (fun e' => (π e.1 == e'.1 && π e.2 == e'.2) || (π e.1 == e'.2 && π e.2 == e'.1))) &&
  Eb.all (fun e' => E.any (fun e => (π e.1 == e'.1 && π e.2 == e'.2) || (π e.1 == e'.2 && π e.2 == e'.1)))

theorem gfn_nc {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n))
    (h : (!A.isEmpty || !E.isEmpty) = true) :
    ∃ x y : Fin n → Bool, gfn A E x ≠ gfn A E y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have h0 : gfn A E (fun _ => false) = false := by simp [gfn]
  have h1 : gfn A E (fun _ => true) = true := by
    cases A with
    | cons a t => simp [gfn]
    | nil =>
      cases E with
      | nil => simp at h
      | cons e t => simp [gfn]
  rw [h0, h1]; decide

theorem gfn_dep {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n)
    (h : depCheck A E p = true) :
    ∃ x : Fin n → Bool, gfn A E (Function.update x p (!x p)) ≠ gfn A E x := by
  simp only [depCheck, Bool.or_eq_true, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true, bne_iff_ne, beq_iff_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  rcases h with hpA | ⟨hloop, ⟨e, heE, ⟨rfl, hqA⟩ | ⟨rfl, hqA⟩⟩⟩
  · refine ⟨fun _ => false, ?_⟩
    have h0 : gfn A E (fun _ => false) = false := by simp [gfn]
    have h1 : gfn A E (Function.update (fun _ => false) p true) = true := by
      simp only [gfn, Bool.or_eq_true, List.any_eq_true]
      exact Or.inl ⟨p, hpA, by simp⟩
    simpa [h0, h1]
  · have hne : e.1 ≠ e.2 := hloop e heE
    refine ⟨fun i => decide (i = e.2), ?_⟩
    have h0 : gfn A E (fun i => decide (i = e.2)) = false := by
      simp only [gfn, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq, Bool.and_eq_true]
      refine ⟨fun a ha hEq => hqA (hEq ▸ ha), fun e' he' => ?_⟩
      intro ⟨h1, h2⟩
      exact hloop e' he' (h1.trans h2.symm)
    have h1 : gfn A E (Function.update (fun i => decide (i = e.2)) e.1 (!decide (e.1 = e.2))) = true := by
      simp only [gfn, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      refine Or.inr ⟨e, heE, ?_, ?_⟩
      · simp [hne]
      · simp [Function.update_of_ne (Ne.symm hne)]
    rw [h0, h1]; decide
  · have hne : e.1 ≠ e.2 := hloop e heE
    refine ⟨fun i => decide (i = e.1), ?_⟩
    have h0 : gfn A E (fun i => decide (i = e.1)) = false := by
      simp only [gfn, Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq, Bool.and_eq_true]
      refine ⟨fun a ha hEq => hqA (hEq ▸ ha), fun e' he' => ?_⟩
      intro ⟨h1, h2⟩
      exact hloop e' he' (h1.trans h2.symm)
    have h1 : gfn A E (Function.update (fun i => decide (i = e.1)) e.2 (!decide (e.2 = e.1))) = true := by
      simp only [gfn, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      refine Or.inr ⟨e, heE, ?_, ?_⟩
      · simp [Function.update_of_ne hne]
      · simp [Ne.symm hne]
    rw [h0, h1]; decide

theorem gfn_restrict_false {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n) :
    (fun x => gfn A E (Function.update x p false)) = gfn (fix0A A p) (fix0E E p) := by
  funext x
  apply Bool.eq_iff_iff.2
  simp only [gfn, fix0A, fix0E, Bool.or_eq_true, List.any_eq_true, List.mem_filter,
    Bool.and_eq_true, bne_iff_ne]
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨e, he, h1, h2⟩)
    · by_cases hap : a = p
      · subst hap; simp at hxa
      · exact Or.inl ⟨a, ⟨ha, hap⟩, by simpa [Function.update_of_ne hap] using hxa⟩
    · by_cases h1p : e.1 = p
      · rw [h1p, Function.update_self] at h1; cases h1
      · by_cases h2p : e.2 = p
        · rw [h2p, Function.update_self] at h2; cases h2
        · exact Or.inr ⟨e, ⟨he, h1p, h2p⟩,
            by simpa [Function.update_of_ne h1p] using h1,
            by simpa [Function.update_of_ne h2p] using h2⟩
  · rintro (⟨a, ⟨ha, hap⟩, hxa⟩ | ⟨e, ⟨he, h1p, h2p⟩, h1, h2⟩)
    · exact Or.inl ⟨a, ha, by simpa [Function.update_of_ne hap] using hxa⟩
    · exact Or.inr ⟨e, he,
        by simpa [Function.update_of_ne h1p] using h1,
        by simpa [Function.update_of_ne h2p] using h2⟩

theorem mem_nbrs {n : ℕ} (E : List (Fin n × Fin n)) (p q : Fin n) :
    q ∈ nbrs E p ↔ ∃ e ∈ E, (e.1 = p ∧ e.2 = q) ∨ (e.1 ≠ p ∧ e.2 = p ∧ e.1 = q) := by
  simp only [nbrs, List.mem_filterMap, beq_iff_eq]
  constructor
  · rintro ⟨e, he, h⟩
    split_ifs at h with h1 h2
    · cases h; exact ⟨e, he, Or.inl ⟨h1, rfl⟩⟩
    · cases h; exact ⟨e, he, Or.inr ⟨h1, h2, rfl⟩⟩
  · rintro ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2, h3⟩⟩
    · exact ⟨e, he, by rw [if_pos h1, h2]⟩
    · exact ⟨e, he, by rw [if_neg h1, if_pos h2, h3]⟩

theorem gfn_restrict_true {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (p : Fin n)
    (hpA : !A.contains p = true) (hloop : E.all (fun e => e.1 != e.2) = true) :
    (fun x => gfn A E (Function.update x p true)) = gfn (fix1A A E p) (fix1E A E p) := by
  have hpnot : p ∉ A := by simpa [List.contains_eq_mem] using hpA
  have hne : ∀ e ∈ E, e.1 ≠ e.2 := by simpa [List.all_eq_true, bne_iff_ne] using hloop
  funext x
  apply Bool.eq_iff_iff.2
  simp only [gfn, fix1E, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, List.mem_filter,
    bne_iff_ne, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨e, he, h1, h2⟩)
    · have hap : a ≠ p := fun h => hpnot (h ▸ ha)
      refine Or.inl ⟨a, ?_, by simpa [Function.update_of_ne hap] using hxa⟩
      rw [fix1A, mem_dedup]; exact List.mem_append_left _ ha
    · by_cases h1p : e.1 = p
      · have h2p : e.2 ≠ p := fun h => hne e he (h1p.trans h.symm)
        refine Or.inl ⟨e.2, ?_, by simpa [Function.update_of_ne h2p] using h2⟩
        rw [fix1A, mem_dedup]; exact List.mem_append_right _ ((mem_nbrs E p e.2).2 ⟨e, he, Or.inl ⟨h1p, rfl⟩⟩)
      · by_cases h2p : e.2 = p
        · refine Or.inl ⟨e.1, ?_, by simpa [Function.update_of_ne h1p] using h1⟩
          rw [fix1A, mem_dedup]; exact List.mem_append_right _ ((mem_nbrs E p e.1).2 ⟨e, he, Or.inr ⟨h1p, h2p, rfl⟩⟩)
        · have hx1 : x e.1 = true := by simpa [Function.update_of_ne h1p] using h1
          have hx2 : x e.2 = true := by simpa [Function.update_of_ne h2p] using h2
          by_cases m1 : e.1 ∈ fix1A A E p
          · exact Or.inl ⟨e.1, m1, hx1⟩
          · by_cases m2 : e.2 ∈ fix1A A E p
            · exact Or.inl ⟨e.2, m2, hx2⟩
            · exact Or.inr ⟨e, ⟨he, ⟨⟨h1p, h2p⟩, m1⟩, m2⟩, hx1, hx2⟩
  · rintro (⟨a, ha, hxa⟩ | ⟨e, ⟨he, ⟨⟨h1p, h2p⟩, _⟩, _⟩, hx1, hx2⟩)
    · rw [fix1A, mem_dedup, List.mem_append] at ha
      rcases ha with haA | han
      · have hap : a ≠ p := fun h => hpnot (h ▸ haA)
        exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne hap] using hxa⟩
      · obtain ⟨e, he, ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩⟩ := (mem_nbrs E p a).1 han
        · have h2p : e.2 ≠ p := fun h => hne e he (h1.trans h.symm)
          exact Or.inr ⟨e, he, by simp [h1], by simpa [Function.update_of_ne h2p] using hxa⟩
        · exact Or.inr ⟨e, he, by simpa [Function.update_of_ne h1] using hxa, by simp [h2]⟩
    · exact Or.inr ⟨e, he,
        by simpa [Function.update_of_ne h1p] using hx1,
        by simpa [Function.update_of_ne h2p] using hx2⟩

theorem gfn_fix0 {n : ℕ} (A : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1)) (A' : List (Fin (n + 1))) (E' : List (Fin (n + 1) × Fin (n + 1))) (k : ℕ)
    (hdep : depCheck A E p = true)
    (hA : A' = fix0A A p) (hE : E' = fix0E E p)
    (hnc : (!A'.isEmpty || !E'.isEmpty) = true)
    (ih : ∀ s, HasCircuitSize (n + 1) (gfn A' E') s → k ≤ s) :
    ∀ s, HasCircuitSize (n + 1) (gfn A E) s → k + 1 ≤ s := by
  intro s h
  have hres : (fun x => gfn A E (Function.update x p false)) = gfn A' E' := by
    rw [hA, hE]; exact gfn_restrict_false A E p
  have hnc' : ∃ x y, gfn A E (Function.update x p false) ≠ gfn A E (Function.update y p false) := by
    obtain ⟨x, y, hxy⟩ := gfn_nc A' E' hnc
    exact ⟨x, y, by simpa [congrFun hres] using hxy⟩
  obtain ⟨s', hs', h'⟩ := one_gate_at n (gfn A E) p false s (gfn_dep A E p hdep) hnc' h
  rw [hres] at h'
  have := ih s' h'
  omega

theorem gfn_fix1 {n : ℕ} (A : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1)) (A' : List (Fin (n + 1))) (E' : List (Fin (n + 1) × Fin (n + 1))) (k : ℕ)
    (hdep : depCheck A E p = true)
    (hpA : !A.contains p = true) (hloop : E.all (fun e => e.1 != e.2) = true)
    (hA : A' = fix1A A E p) (hE : E' = fix1E A E p)
    (hnc : (!A'.isEmpty || !E'.isEmpty) = true)
    (ih : ∀ s, HasCircuitSize (n + 1) (gfn A' E') s → k ≤ s) :
    ∀ s, HasCircuitSize (n + 1) (gfn A E) s → k + 1 ≤ s := by
  intro s h
  have hres : (fun x => gfn A E (Function.update x p true)) = gfn A' E' := by
    rw [hA, hE]; exact gfn_restrict_true A E p hpA hloop
  have hnc' : ∃ x y, gfn A E (Function.update x p true) ≠ gfn A E (Function.update y p true) := by
    obtain ⟨x, y, hxy⟩ := gfn_nc A' E' hnc
    exact ⟨x, y, by simpa [congrFun hres] using hxy⟩
  obtain ⟨s', hs', h'⟩ := one_gate_at n (gfn A E) p true s (gfn_dep A E p hdep) hnc' h
  rw [hres] at h'
  have := ih s' h'
  omega

theorem gfn_branch2 {n : ℕ} (A : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (p : Fin (n + 1))
    (A0 : List (Fin (n + 1))) (E0 : List (Fin (n + 1) × Fin (n + 1)))
    (A1 : List (Fin (n + 1))) (E1 : List (Fin (n + 1) × Fin (n + 1))) (k : ℕ)
    (hdep : depCheck A E p = true)
    (hpA : !A.contains p = true) (hloop : E.all (fun e => e.1 != e.2) = true)
    (hA0 : A0 = fix0A A p) (hE0 : E0 = fix0E E p)
    (hA1 : A1 = fix1A A E p) (hE1 : E1 = fix1E A E p)
    (hnc0 : (!A0.isEmpty || !E0.isEmpty) = true)
    (hnc1 : (!A1.isEmpty || !E1.isEmpty) = true)
    (ih0 : ∀ s, HasCircuitSize (n + 1) (gfn A0 E0) s → k ≤ s)
    (ih1 : ∀ s, HasCircuitSize (n + 1) (gfn A1 E1) s → k ≤ s) :
    ∀ s, HasCircuitSize (n + 1) (gfn A E) s → k + 2 ≤ s := by
  intro s h
  have hres0 : (fun x => gfn A E (Function.update x p false)) = gfn A0 E0 := by
    rw [hA0, hE0]; exact gfn_restrict_false A E p
  have hres1 : (fun x => gfn A E (Function.update x p true)) = gfn A1 E1 := by
    rw [hA1, hE1]; exact gfn_restrict_true A E p hpA hloop
  have hnc : ∀ b : Bool, ∃ x y, gfn A E (Function.update x p b) ≠ gfn A E (Function.update y p b) := by
    intro b
    cases b with
    | false =>
      obtain ⟨x, y, hxy⟩ := gfn_nc A0 E0 hnc0
      exact ⟨x, y, by simpa [congrFun hres0] using hxy⟩
    | true =>
      obtain ⟨x, y, hxy⟩ := gfn_nc A1 E1 hnc1
      exact ⟨x, y, by simpa [congrFun hres1] using hxy⟩
  obtain ⟨b, s', hs', h'⟩ := gate_elim_at n (gfn A E) p s (gfn_dep A E p hdep) hnc h
  cases b with
  | false => rw [hres0] at h'; have := ih0 s' h'; omega
  | true => rw [hres1] at h'; have := ih1 s' h'; omega

theorem gfn_iso {n k : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k))
    (π : Fin n → Fin k) (hiso : isoCheck E Eb π = true) :
    (fun y : Fin k → Bool => gfn [] E (y ∘ π)) = gfn [] Eb := by
  simp only [isoCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, beq_iff_eq] at hiso
  obtain ⟨h1, h2⟩ := hiso
  funext y
  apply Bool.eq_iff_iff.2
  simp only [gfn, List.any_nil, Bool.false_or, List.any_eq_true, Bool.and_eq_true, Function.comp_apply]
  constructor
  · rintro ⟨e, he, hy1, hy2⟩
    obtain ⟨e', he', ⟨a, b⟩ | ⟨a, b⟩⟩ := h1 e he
    · exact ⟨e', he', a ▸ hy1, b ▸ hy2⟩
    · exact ⟨e', he', b ▸ hy2, a ▸ hy1⟩
  · rintro ⟨e', he', hy1, hy2⟩
    obtain ⟨e, he, ⟨a, b⟩ | ⟨a, b⟩⟩ := h2 e' he'
    · exact ⟨e, he, a.symm ▸ hy1, b.symm ▸ hy2⟩
    · exact ⟨e, he, a.symm ▸ hy2, b.symm ▸ hy1⟩

theorem gfn_base {n k val : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k))
    (π : Fin n → Fin k) (hiso : isoCheck E Eb π = true)
    (hb : ∀ s : ℕ, HasCircuitSize k (gfn [] Eb) s → val ≤ s) :
    ∀ s : ℕ, HasCircuitSize n (gfn [] E) s → val ≤ s := by
  intro s h
  have h' := relabel_size π (gfn [] E) s h
  rw [gfn_iso E Eb π hiso] at h'
  exact hb s h'

theorem conj_2 : ∀ t : ℕ, HasCircuitSize 3 gF1 t → 4 ≤ t := by
  have heq : gF1 = gfn (n := 3) [] [(0, 1), (0, 2), (1, 2)] := by
    funext x; simp [gF1, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := eS0) (Eb := Eb_K3) (fun i : Fin 3 => match i.val with | 0 => (0 : Fin 3) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | _ => (0 : Fin 3)) (by decide) base_K3_gfn

theorem conj_14 : ∀ t : ℕ, HasCircuitSize 5 gF2 t → 7 ≤ t := by
  have heq : gF2 = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)] := by
    funext x; simp [gF2, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_branch2 (A := []) (E := eS5) (p := (4 : Fin 5)) (A0 := []) (E0 := eS2) (A1 := [3]) (E1 := eS0) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := eS2) (p := (3 : Fin 5)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap3 (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := eS0) (p := (3 : Fin 5)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap3 (by decide) base_K3_gfn))

theorem conj_15 : ∀ t : ℕ, HasCircuitSize 5 gF3 t → 7 ≤ t := by
  have heq : gF3 = gfn (n := 5) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)] := by
    funext x; simp [gF3, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) (Eb := Eb_C5) restrictMap4 (by decide) base_C5_gfn

theorem conj_16 : ∀ t : ℕ, HasCircuitSize 5 gF4 t → 8 ≤ t := by
  have heq : gF4 = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)] := by
    funext x; simp [gF4, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := eS1) (Eb := Eb_BOWTIE) restrictMap4 (by decide) base_BOWTIE_gfn

theorem conj_31 : ∀ t : ℕ, HasCircuitSize 6 gF5 t → 8 ≤ t := by
  have heq : gF5 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)] := by
    funext x; simp [gF5, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := eS3) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := eS3) (p := (5 : Fin 6)) (A0 := []) (E0 := eS2) (A1 := [3]) (E1 := eS0) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := eS2) (p := (3 : Fin 6)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap0 (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := eS0) (p := (3 : Fin 6)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap0 (by decide) base_K3_gfn)))

theorem conj_33 : ∀ t : ℕ, HasCircuitSize 6 gF6 t → 8 ≤ t := by
  have heq : gF6 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)] := by
    funext x; simp [gF6, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := eS3) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := eS3) (p := (5 : Fin 6)) (A0 := []) (E0 := eS2) (A1 := [3]) (E1 := eS0) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := eS2) (p := (3 : Fin 6)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap0 (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := eS0) (p := (3 : Fin 6)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap0 (by decide) base_K3_gfn)))

theorem conj_34 : ∀ t : ℕ, HasCircuitSize 6 gF7 t → 8 ≤ t := by
  have heq : gF7 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)] := by
    funext x; simp [gF7, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) (p := (4 : Fin 6)) (A' := []) (E' := eS3) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := eS3) (p := (5 : Fin 6)) (A0 := []) (E0 := eS2) (A1 := [3]) (E1 := eS0) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := eS2) (p := (3 : Fin 6)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap0 (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := eS0) (p := (3 : Fin 6)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap0 (by decide) base_K3_gfn)))

theorem conj_35 : ∀ t : ℕ, HasCircuitSize 6 gF8 t → 8 ≤ t := by
  have heq : gF8 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)] := by
    funext x; simp [gF8, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) (p := (5 : Fin 6)) (A' := []) (E' := eS5) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_branch2 (A := []) (E := eS5) (p := (4 : Fin 6)) (A0 := []) (E0 := eS2) (A1 := [3]) (E1 := eS0) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_fix0 (A := []) (E := eS2) (p := (3 : Fin 6)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap0 (by decide) base_K3_gfn)) (gfn_fix0 (A := [3]) (E := eS0) (p := (3 : Fin 6)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := Eb_K3) restrictMap0 (by decide) base_K3_gfn)))

theorem conj_36 : ∀ t : ℕ, HasCircuitSize 6 gF9 t → 8 ≤ t := by
  have heq : gF9 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)] := by
    funext x; simp [gF9, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) (p := (3 : Fin 6)) (A' := []) (E' := eS4) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS4) (Eb := Eb_C5) (fun i : Fin 6 => match i.val with | 0 => (0 : Fin 5) | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (0 : Fin 5) | 4 => (3 : Fin 5) | 5 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base_C5_gfn)

theorem conj_37 : ∀ t : ℕ, HasCircuitSize 6 gF10 t → 9 ≤ t := by
  have heq : gF10 = gfn (n := 6) [] [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] := by
    funext x; simp [gF10, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]) (Eb := Eb_TwoK3) restrictMap5 (by decide) base_TwoK3_gfn

theorem conj_39 : ∀ t : ℕ, HasCircuitSize 6 gF11 t → 9 ≤ t := by
  have heq : gF11 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)] := by
    funext x; simp [gF11, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := eS10) (p := (5 : Fin 6)) (A' := []) (E' := eS1) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS1) (Eb := Eb_BOWTIE) restrictMap6 (by decide) base_BOWTIE_gfn)

theorem conj_40 : ∀ t : ℕ, HasCircuitSize 6 gF12 t → 9 ≤ t := by
  have heq : gF12 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)] := by
    funext x; simp [gF12, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_fix0 (A := []) (E := eS11) (p := (5 : Fin 6)) (A' := []) (E' := eS1) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS1) (Eb := Eb_BOWTIE) restrictMap6 (by decide) base_BOWTIE_gfn)

theorem conj_41 : ∀ t : ℕ, HasCircuitSize 6 gF13 t → 9 ≤ t := by
  have heq : gF13 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)] := by
    funext x; simp [gF13, gfn, Bool.or_assoc]
  rw [heq]
  exact gfn_base (E := eS12) (Eb := Eb_K3C5) restrictMap5 (by decide) base_K3C5_gfn



namespace Reduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem base2 : ∀ s, HasCircuitSize 3 (gfn [] [(0, 1), (0, 2), (1, 2)]) s → 4 ≤ s := by
  have heq : gF1 = gfn (n := 3) [] [(0, 1), (0, 2), (1, 2)] := by
    funext x
    simp [gF1, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_2

theorem base14 : ∀ s, HasCircuitSize 5 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) s → 7 ≤ s := by
  have heq : gF2 = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)] := by
    funext x
    simp [gF2, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_14

theorem base15 : ∀ s, HasCircuitSize 5 (gfn [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) s → 7 ≤ s := by
  have heq : gF3 = gfn (n := 5) [] [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)] := by
    funext x
    simp [gF3, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_15

theorem base16 : ∀ s, HasCircuitSize 5 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) s → 8 ≤ s := by
  have heq : gF4 = gfn (n := 5) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)] := by
    funext x
    simp [gF4, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_16

theorem base31 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)]) s → 8 ≤ s := by
  have heq : gF5 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)] := by
    funext x
    simp [gF5, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_31

theorem base33 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)]) s → 8 ≤ s := by
  have heq : gF6 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)] := by
    funext x
    simp [gF6, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_33

theorem base34 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) s → 8 ≤ s := by
  have heq : gF7 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)] := by
    funext x
    simp [gF7, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_34

theorem base35 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) s → 8 ≤ s := by
  have heq : gF8 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)] := by
    funext x
    simp [gF8, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_35

theorem base36 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) s → 8 ≤ s := by
  have heq : gF9 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)] := by
    funext x
    simp [gF9, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_36

theorem base37 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]) s → 9 ≤ s := by
  have heq : gF10 = gfn (n := 6) [] [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] := by
    funext x
    simp [gF10, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_37

theorem base39 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) s → 9 ≤ s := by
  have heq : gF11 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)] := by
    funext x
    simp [gF11, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_39

theorem base40 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) s → 9 ≤ s := by
  have heq : gF12 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)] := by
    funext x
    simp [gF12, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_40

theorem base41 : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) s → 9 ≤ s := by
  have heq : gF13 = gfn (n := 6) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)] := by
    funext x
    simp [gF13, gfn, Bool.or_assoc]
  rw [← heq]
  exact conj_41

theorem node1 : ∀ s, HasCircuitSize 7 (gfn [6] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) s → 9 ≤ s := by
  exact gfn_fix0 (A := [6]) (E := eS1) (p := (6 : Fin 7)) (A' := []) (E' := eS1) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS1) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) restrictMap7 (by decide) base16)

theorem node2 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix1 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (5, 6)]) (p := (5 : Fin 7)) (A' := [6]) (E' := eS1) (k := 9) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) node1

theorem node3 : ∀ s, HasCircuitSize 7 (gfn [3] [(0, 1), (0, 2), (0, 4), (1, 2), (4, 6)]) s → 8 ≤ s := by
  exact gfn_fix0 (A := [3]) (E := eS6) (p := (3 : Fin 7)) (A' := []) (E' := eS6) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS6) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 4 => (3 : Fin 5) | 6 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base14)

theorem node4 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (4, 6)]) (A1 := [3]) (E1 := eS6) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (4, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (4 : Fin 6) | 4 => (3 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base31) node3

theorem node5 : ∀ s, HasCircuitSize 7 (gfn [3] [(0, 1), (0, 2), (1, 2), (1, 4), (4, 6)]) s → 8 ≤ s := by
  exact gfn_fix0 (A := [3]) (E := eS7) (p := (3 : Fin 7)) (A' := []) (E' := eS7) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS7) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 0 => (1 : Fin 5) | 2 => (2 : Fin 5) | 4 => (3 : Fin 5) | 6 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base14)

theorem node6 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6)]) (p := (5 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (4, 6)]) (A1 := [3]) (E1 := eS7) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (4, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)]) (fun i : Fin 7 => match i.val with | 0 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (4 : Fin 6) | 4 => (3 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base33) node5

theorem node7 : ∀ s, HasCircuitSize 7 (gfn [4] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5)]) s → 8 ≤ s := by
  exact gfn_fix0 (A := [4]) (E := eS3) (p := (4 : Fin 7)) (A' := []) (E' := eS3) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS3) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 3 => (3 : Fin 5) | 5 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base14)

theorem node8 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) (A1 := [4]) (E1 := eS3) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)]) restrictMap1 (by decide) base34) node7

theorem node9 : ∀ s, HasCircuitSize 7 (gfn [5] [(0, 1), (0, 2), (1, 2)]) s → 5 ≤ s := by
  exact gfn_fix0 (A := [5]) (E := eS0) (p := (5 : Fin 7)) (A' := []) (E' := eS0) (k := 4) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS0) (Eb := [(0, 1), (0, 2), (1, 2)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 3) | 2 => (2 : Fin 3) | _ => (0 : Fin 3)) (by decide) base2)

theorem node10 : ∀ s, HasCircuitSize 7 (gfn [5] [(0, 1), (0, 2), (0, 3), (1, 2)]) s → 6 ≤ s := by
  exact gfn_fix0 (A := [5]) (E := eS2) (p := (3 : Fin 7)) (A' := [5]) (E' := eS0) (k := 5) (by decide) (by decide) (by decide) (by decide) node9

theorem node11 : ∀ s, HasCircuitSize 7 (gfn [5, 3] [(0, 1), (0, 2), (1, 2)]) s → 6 ≤ s := by
  exact gfn_fix0 (A := [5, 3]) (E := eS0) (p := (3 : Fin 7)) (A' := [5]) (E' := eS0) (k := 5) (by decide) (by decide) (by decide) (by decide) node9

theorem node12 : ∀ s, HasCircuitSize 7 (gfn [5] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]) s → 8 ≤ s := by
  exact gfn_branch2 (A := [5]) (E := eS5) (p := (4 : Fin 7)) (A0 := [5]) (E0 := eS2) (A1 := [5, 3]) (E1 := eS0) (k := 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) node10 node11

theorem node13 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (5, 6)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (5, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) (A1 := [5]) (E1 := eS5) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]) restrictMap1 (by decide) base35) node12

theorem node14 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6), (5, 6)]) (p := (3 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (1, 2), (4, 5), (4, 6), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (1, 2), (4, 5), (4, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 4 => (3 : Fin 6) | 5 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base37)

theorem node15 : ∀ s, HasCircuitSize 7 (gfn [3] [(0, 1), (0, 2), (1, 4), (2, 5), (4, 5)]) s → 8 ≤ s := by
  exact gfn_fix0 (A := [3]) (E := eS4) (p := (3 : Fin 7)) (A' := []) (E' := eS4) (k := 7) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS4) (Eb := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 5) | 2 => (2 : Fin 5) | 4 => (3 : Fin 5) | 5 => (4 : Fin 5) | _ => (0 : Fin 5)) (by decide) base15)

theorem node16 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5)]) s → 10 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5)]) (p := (6 : Fin 7)) (A0 := []) (E0 := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) (A1 := [3]) (E1 := eS4) (k := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 5)]) restrictMap1 (by decide) base36) node15

theorem node18 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (3, 4)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (3, 4)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) restrictMap2 (by decide) base39)

theorem node19 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6), (3, 4)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6), (3, 4)]) (p := (5 : Fin 7)) (A' := []) (E' := eS8) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS8) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) restrictMap2 (by decide) base40)

theorem node20 : ∀ s, HasCircuitSize 7 (gfn [5] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) s → 9 ≤ s := by
  exact gfn_fix0 (A := [5]) (E := eS1) (p := (5 : Fin 7)) (A' := []) (E' := eS1) (k := 8) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS1) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4)]) restrictMap7 (by decide) base16)

theorem node21 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4), (5, 6)]) s → 11 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4), (5, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := eS10) (A1 := [5]) (E1 := eS1) (k := 9) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS10) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4)]) restrictMap1 (by decide) base39) node20

theorem node22 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4)]) (p := (5 : Fin 7)) (A' := []) (E' := eS8) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS8) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) restrictMap2 (by decide) base40)

theorem node24 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)]) (p := (5 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (3, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (3, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) (fun i : Fin 7 => match i.val with | 1 => (3 : Fin 6) | 2 => (4 : Fin 6) | 3 => (1 : Fin 6) | 4 => (2 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base40)

theorem node25 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)]) s → 11 ≤ s := by
  exact gfn_branch2 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)]) (p := (6 : Fin 7)) (A0 := []) (E0 := eS11) (A1 := [5]) (E1 := eS1) (k := 9) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS11) (Eb := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4)]) restrictMap1 (by decide) base40) node20

theorem node26 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)]) (p := (4 : Fin 7)) (A' := []) (E' := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 5), (3, 6), (5, 6)]) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 5), (3, 6), (5, 6)]) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) (fun i : Fin 7 => match i.val with | 1 => (1 : Fin 6) | 2 => (2 : Fin 6) | 3 => (3 : Fin 6) | 5 => (4 : Fin 6) | 6 => (5 : Fin 6) | _ => (0 : Fin 6)) (by decide) base41)

theorem node34 : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)]) s → 10 ≤ s := by
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)]) (p := (6 : Fin 7)) (A' := []) (E' := eS12) (k := 9) (by decide) (by decide) (by decide) (by decide) (gfn_base (E := eS12) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5)]) restrictMap1 (by decide) base41)

theorem shard01 : ∀ t : ℕ, HasCircuitSize 7 gF14 t → 10 ≤ t := by
  have heq : gF14 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (5, 6)] := by
    funext x
    simp [gF14, gfn, Bool.or_assoc]
  rw [heq]
  exact node2

theorem shard02 : ∀ t : ℕ, HasCircuitSize 7 gF15 t → 10 ≤ t := by
  have heq : gF15 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6)] := by
    funext x
    simp [gF15, gfn, Bool.or_assoc]
  rw [heq]
  exact node4

theorem shard03 : ∀ t : ℕ, HasCircuitSize 7 gF16 t → 10 ≤ t := by
  have heq : gF16 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6)] := by
    funext x
    simp [gF16, gfn, Bool.or_assoc]
  rw [heq]
  exact node6

theorem shard04 : ∀ t : ℕ, HasCircuitSize 7 gF17 t → 10 ≤ t := by
  have heq : gF17 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6)] := by
    funext x
    simp [gF17, gfn, Bool.or_assoc]
  rw [heq]
  exact node8

theorem shard05 : ∀ t : ℕ, HasCircuitSize 7 gF18 t → 10 ≤ t := by
  have heq : gF18 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (5, 6)] := by
    funext x
    simp [gF18, gfn, Bool.or_assoc]
  rw [heq]
  exact node13

theorem shard06 : ∀ t : ℕ, HasCircuitSize 7 gF19 t → 10 ≤ t := by
  have heq : gF19 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6), (5, 6)] := by
    funext x
    simp [gF19, gfn, Bool.or_assoc]
  rw [heq]
  exact node14

theorem shard07 : ∀ t : ℕ, HasCircuitSize 7 gF20 t → 10 ≤ t := by
  have heq : gF20 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5)] := by
    funext x
    simp [gF20, gfn, Bool.or_assoc]
  rw [heq]
  exact node16

theorem shard09 : ∀ t : ℕ, HasCircuitSize 7 gF21 t → 10 ≤ t := by
  have heq : gF21 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4)] := by
    funext x
    simp [gF21, gfn, Bool.or_assoc]
  rw [heq]
  exact node18

theorem shard10 : ∀ t : ℕ, HasCircuitSize 7 gF22 t → 10 ≤ t := by
  have heq : gF22 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6), (3, 4)] := by
    funext x
    simp [gF22, gfn, Bool.or_assoc]
  rw [heq]
  exact node19

theorem shard11 : ∀ t : ℕ, HasCircuitSize 7 gF23 t → 11 ≤ t := by
  have heq : gF23 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4), (5, 6)] := by
    funext x
    simp [gF23, gfn, Bool.or_assoc]
  rw [heq]
  exact node21

theorem shard12 : ∀ t : ℕ, HasCircuitSize 7 gF24 t → 10 ≤ t := by
  have heq : gF24 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4)] := by
    funext x
    simp [gF24, gfn, Bool.or_assoc]
  rw [heq]
  exact node22

theorem shard14 : ∀ t : ℕ, HasCircuitSize 7 gF25 t → 10 ≤ t := by
  have heq : gF25 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)] := by
    funext x
    simp [gF25, gfn, Bool.or_assoc]
  rw [heq]
  exact node24

theorem shard15 : ∀ t : ℕ, HasCircuitSize 7 gF26 t → 11 ≤ t := by
  have heq : gF26 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)] := by
    funext x
    simp [gF26, gfn, Bool.or_assoc]
  rw [heq]
  exact node25

theorem shard16 : ∀ t : ℕ, HasCircuitSize 7 gF27 t → 10 ≤ t := by
  have heq : gF27 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)] := by
    funext x
    simp [gF27, gfn, Bool.or_assoc]
  rw [heq]
  exact node26

theorem shard22 : ∀ t : ℕ, HasCircuitSize 7 gF28 t → 10 ≤ t := by
  have heq : gF28 = gfn (n := 7) [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)] := by
    funext x
    simp [gF28, gfn, Bool.or_assoc]
  rw [heq]
  exact node34

end Reduction

namespace Reduction
open PEqualNP.MetaComplexity 

theorem row17_of_row0 (base : ∀ s, HasCircuitSize 6 gF0 s → 10 ≤ s) :
    ∀ s, HasCircuitSize 7 gF29 s → 11 ≤ s := by
  have base' : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]) s → 10 ≤ s := by
    have he : gF0 = gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)] := by
      funext x
      simp [gF0, gfn, Bool.or_assoc]
    rw [← he]
    exact base
  have child : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) s → 10 ≤ s :=
    gfn_base (E := eS9) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)])
      (fun i : Fin 7 => match i.val with
        | 1 => (1 : Fin 6) | 2 => 2 | 3 => 3 | 5 => 4 | 6 => 5 | _ => 0) (by decide) base'
  have he : gF29 = gfn [] [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6), (5, 6)] := by
    funext x
    simp [gF29, gfn, Bool.or_assoc]
  rw [he]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6), (5, 6)]) (p := (4 : Fin 7))
    (A' := []) (E' := eS9) (k := 10) (by decide) (by decide)
    (by decide) (by decide) child

theorem row21_of_row0 (base : ∀ s, HasCircuitSize 6 gF0 s → 10 ≤ s) :
    ∀ s, HasCircuitSize 7 gF30 s → 11 ≤ s := by
  have base' : ∀ s, HasCircuitSize 6 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]) s → 10 ≤ s := by
    have he : gF0 = gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)] := by
      funext x
      simp [gF0, gfn, Bool.or_assoc]
    rw [← he]
    exact base
  have child : ∀ s, HasCircuitSize 7 (gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (3, 5), (3, 6), (5, 6)]) s → 10 ≤ s :=
    gfn_base (E := eS9) (Eb := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)])
      (fun i : Fin 7 => match i.val with
        | 1 => (1 : Fin 6) | 2 => 2 | 3 => 3 | 5 => 4 | 6 => 5 | _ => 0) (by decide) base'
  have he : gF30 = gfn [] [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (5, 6)] := by
    funext x
    simp [gF30, gfn, Bool.or_assoc]
  rw [he]
  exact gfn_fix0 (A := []) (E := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (5, 6)]) (p := (4 : Fin 7))
    (A' := []) (E' := eS9) (k := 10) (by decide) (by decide)
    (by decide) (by decide) child

end Reduction

theorem proveAtCap (n k cap : ℕ) (f : BFn n) (rows xs : List ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (bad : ¬ NatRun (mask k) (goal k) cap xs) :
    ∀ s : ℕ, HasCircuitSize n f s → cap + 1 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hmask : mask k = 2 ^ rows.length - 1 := by rw [hlen]; rfl
  have hr : NatRun (mask k) (encL f rows) s' (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hsub' : (ws.map fun a => encL a rows).Sublist xs := by
    rw [← hxs]; exact hsub.map _
  by_cases he : (ws.map fun a => encL a rows) = xs
  · rw [he] at hr
    cases hxs_nil : xs with
    | nil =>
      rw [hxs_nil] at hr
      have hc := required hr
      have hne : cov k [] = 0 := rfl
      rw [hne] at hc
      have hlo : lo k ≠ 0 := by
        cases k with
        | zero =>
          simp [goal, lo] at hgoal
          obtain ⟨y, y', hne'⟩ := hnc
          have h0 : rows.length = 0 := hlen
          have hnil : rows = [] := List.eq_nil_of_length_eq_zero h0
          rw [hnil] at hxs
          have hxs0 : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun _ => 0) = [] := by
            simpa [encL, hxs_nil] using hxs
          have hn0 : n = 0 := by simpa using congrArg List.length hxs0
          subst hn0
          exact absurd (Subsingleton.elim y y') (fun e => hne' (e ▸ rfl))
        | succ k' =>
          simp only [lo]
          have : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
          rw [pow_succ]; omega
      simp at hc
      exact hlo hc.symm
    | cons a r =>
      rw [hxs_nil] at hr
      have hcap : NatRun (mask k) (goal k) cap (a :: r) := extend_run hr (by omega)
      rw [← hxs_nil] at hcap
      exact bad hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)


def covDelta (k : Nat) (up : Bool) (w : Nat) : Nat :=
  if up then diffUp k w else diff k w

def covFold (k : Nat) (up : Bool) (ws : List Nat) : Nat :=
  if up then covUp k ws else cov k ws

theorem covFold_cons (k : Nat) (up : Bool) (a : Nat) (r : List Nat) :
    covFold k up (a::r) = covDelta k up a ||| covFold k up r := by
  cases up <;> rfl

def coveredNew (k : Nat) (up : Bool) (a rest : Nat) : Bool :=
  ((covDelta k up a ||| rest) &&& lo k) == lo k

theorem covers_cons_opt (k s w : Nat) (r : List Nat) :
    covers k s (w :: r) =
      coveredNew k (r.length + 1 == s+1) w (covFold k (r.length+1 == s+1) r) := by
  by_cases hb : r.length = s <;>
    simp [covers, covUp, cov, coveredNew, covDelta, covFold, hb]

def nextCovered (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  let slack := s+2-ws.length
  let m := mask k
  ws.any fun a =>
    let ra := ws.erase a
    let la := ra.length
    let ua := (la+1 == s+1)
    let ub := (la+1+1 == s+1)
    let ca := covFold k ua ra
    let cb := covDelta k ub a ||| covFold k ub ra
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      (coveredNew k ua w ca && f (tagU ws a neg false) (w :: ra)) ||
        (slack ≥ 2 && (coveredNew k ub w cb && f (tagU ws a neg true) (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        let l := r.length
        let u0 := (l+1 == s+1)
        let u1 := (l+1+1 == s+1)
        let u2 := (l+1+1+1 == s+1)
        let c0 := covFold k u0 r
        let c1 := covFold k u1 r
        let c1a := covDelta k u1 a ||| c1
        let c1b := covDelta k u1 b ||| c1
        let c2ab := covDelta k u2 a ||| (covDelta k u2 b ||| covFold k u2 r)
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          (coveredNew k u0 w c0 && f (tagB ws a b conj false false) (w :: r)) ||
          (slack ≥ 1 &&
            ((coveredNew k u1 w c1a && f (tagB ws a b conj true false) (w :: a :: r)) ||
             (coveredNew k u1 w c1b && f (tagB ws a b conj false true) (w :: b :: r)))) ||
          (slack ≥ 2 &&
            (coveredNew k u2 w c2ab && f (tagB ws a b conj true true) (w :: a :: b :: r))))

theorem nextCovered_eq (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) :
    nextCovered k s ws f =
      next (mask k) (s+2-ws.length) ws (fun t zs => covers k s zs && f t zs) := by
  unfold nextCovered next
  simp only [covers_cons_opt, List.length_cons, covFold_cons]

def maskCount (k : Nat) (up : Bool) (i : Nat) (ws : List Nat) : Nat :=
  (ws.map (fun w => ((covDelta k up w).testBit i).toNat)).sum

def coverCount (k : Nat) (up : Bool) : List Nat → Nat × Nat × Nat
  | [] => (0,0,0)
  | a :: r =>
    let v := covDelta k up a
    let z := coverCount k up r
    (v ||| z.1, z.2.1 ||| (z.1 &&& v), z.2.2 ||| (z.2.1 &&& v))

theorem coverCount_bits (k : Nat) (up : Bool) (i : Nat) (ws : List Nat) :
    (coverCount k up ws).1.testBit i = decide (1 ≤ maskCount k up i ws) ∧
    (coverCount k up ws).2.1.testBit i = decide (2 ≤ maskCount k up i ws) ∧
    (coverCount k up ws).2.2.testBit i = decide (3 ≤ maskCount k up i ws) := by
  induction ws with
  | nil => simp [coverCount,maskCount]
  | cons a r ih =>
    have e : maskCount k up i (a::r) =
        ((covDelta k up a).testBit i).toNat + maskCount k up i r := by simp [maskCount]
    simp only [coverCount, Nat.testBit_or, Nat.testBit_and, ih.1, ih.2.1, ih.2.2, e]
    generalize (covDelta k up a).testBit i = b
    generalize maskCount k up i r = n
    cases b <;> refine ⟨?_,?_,?_⟩ <;> apply Bool.eq_iff_iff.2 <;> simp <;> omega

theorem covFold_matches (k : Nat) (up : Bool) (ws : List Nat) :
    (coverCount k up ws).1 = covFold k up ws := by
  induction ws with
  | nil => cases up <;> rfl
  | cons a r ih => simp only [coverCount,covFold_cons,ih]

theorem covFold_bits (k : Nat) (up : Bool) (i : Nat) (ws : List Nat) :
    (covFold k up ws).testBit i = decide (1 ≤ maskCount k up i ws) := by
  rw [←covFold_matches k up ws]
  exact (coverCount_bits k up i ws).1

def coverHoles (k : Nat) (up : Bool) (ws : List Nat) : Nat × Nat × Nat :=
  let x := coverCount k up ws
  let l := lo k
  (l ^^^ (l &&& x.1),l ^^^ (l &&& x.2.1),l ^^^ (l &&& x.2.2))

def missing2 (z : Nat × Nat × Nat) (a b : Nat) : Nat :=
  z.1 ||| (z.2.1 &&& (a ||| b)) ||| (z.2.2 &&& a &&& b)

def todoMask (k : Nat) (up : Bool) (r : List Nat) : Nat :=
  lo k ^^^ (lo k &&& covFold k up r)

theorem maskRemoveBits (l a b : Bool) (n : Nat) :
    (((Bool.xor l (l && decide (1 ≤ a.toNat+b.toNat+n))) ||
      ((Bool.xor l (l && decide (2 ≤ a.toNat+b.toNat+n))) && (a || b)) ||
      ((Bool.xor l (l && decide (3 ≤ a.toNat+b.toNat+n))) && a && b)) =
      (Bool.xor l (l && decide (1 ≤ n)))) := by
  cases l <;> cases a <;> cases b <;>
    first | rfl | (apply Bool.eq_iff_iff.2; simp <;> omega)

theorem missing2_bits (k : Nat) (up : Bool) (ws r : List Nat) (a b : Nat)
    (h : ∀ i, maskCount k up i ws =
      (a.testBit i).toNat+(b.testBit i).toNat+maskCount k up i r) :
    missing2 (coverHoles k up ws) a b = todoMask k up r := by
  apply Nat.eq_of_testBit_eq
  intro i
  obtain ⟨h1,h2,h3⟩ := coverCount_bits k up i ws
  simpa only [missing2,coverHoles,todoMask,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,
    h1,h2,h3,h i,covFold_bits] using
    maskRemoveBits ((lo k).testBit i) (a.testBit i) (b.testBit i) (maskCount k up i r)

theorem missing0_eq (k : Nat) (up : Bool) {ws r : List Nat} (p : ws.Perm r) :
    missing2 (coverHoles k up ws) 0 0 = todoMask k up r := by
  apply missing2_bits; intro i
  simpa [maskCount] using (p.map (fun w => ((covDelta k up w).testBit i).toNat)).sum_eq

theorem missing1_eq (k : Nat) (up : Bool) {ws r : List Nat} (a : Nat) (p : ws.Perm (a::r)) :
    missing2 (coverHoles k up ws) (covDelta k up a) 0 = todoMask k up r := by
  apply missing2_bits; intro i
  simpa [maskCount] using (p.map (fun w => ((covDelta k up w).testBit i).toNat)).sum_eq

theorem missingAB_eq (k : Nat) (up : Bool) {ws r : List Nat} (a b : Nat) (p : ws.Perm (a::b::r)) :
    missing2 (coverHoles k up ws) (covDelta k up a) (covDelta k up b) = todoMask k up r := by
  apply missing2_bits; intro i
  simpa [maskCount,Nat.add_assoc] using (p.map (fun w => ((covDelta k up w).testBit i).toNat)).sum_eq

def passesMissing (k : Nat) (up : Bool) (w z : Nat) : Bool := (covDelta k up w &&& z) == z

theorem covers_missing (k : Nat) (up : Bool) (w : Nat) (r : List Nat) :
    passesMissing k up w (todoMask k up r) = coveredNew k up w (covFold k up r) := by
  unfold passesMissing coveredNew todoMask
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  constructor <;> intro h <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    have e := congrArg (fun t : Nat => t.testBit i) h <;>
    simp only [Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor] at e ⊢ <;>
    cases h₁ : (lo k).testBit i <;> cases h₂ : (covFold k up r).testBit i <;>
    cases h₃ : (covDelta k up w).testBit i <;> simp_all
theorem anyAgree {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x,hx,hh⟩
    exact ⟨x,hx,(h x hx).symm.trans hh⟩
  · rintro ⟨x,hx,hh⟩
    exact ⟨x,hx,(h x hx).trans hh⟩

def nextTallied (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  let n := ws.length
  let slack := s+2-n
  let m := mask k
  let u0 := (n-1 == s+1)
  let u1 := (n == s+1)
  let u2 := (n+1 == s+1)
  let z0 := coverHoles k u0 ws
  let z1 := coverHoles k u1 ws
  let z2 := coverHoles k u2 ws
  let h2 := missing2 z2 0 0
  ws.any fun a =>
    let ra := ws.erase a
    let ha := missing2 z1 (covDelta k u1 a) 0
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      (passesMissing k u1 w ha && f (tagU ws a neg false) (w :: ra)) ||
        (slack ≥ 2 && (passesMissing k u2 w h2 && f (tagU ws a neg true) (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        let hb := missing2 z1 (covDelta k u1 b) 0
        let hab := missing2 z0 (covDelta k u0 a) (covDelta k u0 b)
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          (passesMissing k u0 w hab && f (tagB ws a b conj false false) (w :: r)) ||
          (slack ≥ 1 &&
            ((passesMissing k u1 w hb && f (tagB ws a b conj true false) (w :: a :: r)) ||
             (passesMissing k u1 w ha && f (tagB ws a b conj false true) (w :: b :: r)))) ||
          (slack ≥ 2 &&
            (passesMissing k u2 w h2 && f (tagB ws a b conj true true) (w :: a :: b :: r))))

theorem nextTallied_eq (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) :
    nextTallied k s ws f = nextCovered k s ws f := by
  unfold nextTallied nextCovered
  refine anyAgree _ _ _ ?_
  intro a ha
  have p := List.perm_cons_erase ha
  have H0 (up : Bool) := missing0_eq k up p
  have H1 (up : Bool) := missing1_eq k up a p
  have ln : ws.length = (ws.erase a).length+1 := by simpa using p.length_eq
  apply congrArg₂ (· || ·)
  · simp only [H0,H1,covers_missing,covFold_cons,ln]
  · refine anyAgree _ _ _ ?_
    intro b hb
    have q := List.perm_cons_erase hb
    have p2 := p.trans (List.Perm.cons a q)
    have p3 : ws.Perm (b::a::((ws.erase a).erase b)) := p2.trans (.swap _ _ _)
    have both (up : Bool) := missingAB_eq k up a b p2
    have noA (up : Bool) := missing1_eq k up a p2
    have noB (up : Bool) := missing1_eq k up b p3
    have none (up : Bool) := missing0_eq k up p2
    have ln2 : ws.length = ((ws.erase a).erase b).length+1+1 := by simpa using p2.length_eq
    simp only [both,noA,noB,none,covers_missing,covFold_cons,ln2,Nat.add_sub_cancel]

def keepRunTag (t : Nat) : Bool := t == 0 || decide (48 ≤ t) || t % 4 != 0

theorem keepRunTag_neg (ws : List Nat) (a : Nat) (save : Bool) :
    keepRunTag (tagU ws a true save) = true := by
  cases save <;> simp [keepRunTag,tagU,Bool.toNat,Nat.add_mod,Nat.mul_mod]

theorem keepRunTag_save (ws : List Nat) (a : Nat) (neg : Bool) :
    keepRunTag (tagU ws a neg true) = true := by
  cases neg <;> simp [keepRunTag,tagU,Bool.toNat,Nat.add_mod,Nat.mul_mod]

theorem keepRunTag_two (ws : List Nat) (a b : Nat) (q ka kb : Bool) :
    keepRunTag (tagB ws a b q ka kb) = true := by
  have ht : 48 ≤ tagB ws a b q ka kb := by dsimp [tagB]; omega
  simp [keepRunTag,ht]
theorem nextKeepOne {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws (fun t ys => keepRunTag t && f t ys) = true := by
  by_cases idle : neg = false ∧ save = false
  · obtain ⟨rfl,rfl⟩ := idle
    have onws : NatRun (mask k) (goal k) s ws := Run.perm p (by simpa [kept] using h)
    cases ws with
    | nil => have hl := p.length_eq; simp at hl
    | cons z zs =>
      have hl := run_len onws
      have sl : 1 ≤ s+2-(z::zs).length := by omega
      apply List.any_eq_true.2 ⟨z, by simp, ?_⟩
      rw [Bool.or_eq_true]; left
      rw [Bool.and_eq_true]; refine ⟨decide_eq_true sl,?_⟩
      apply List.any_eq_true.2 ⟨false, by simp, ?_⟩
      rw [Bool.or_eq_true]; left
      simpa [tagU,keepRunTag] using hf 0 (z::zs) onws
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false =>
    have hn : neg = true := by cases neg <;> simp_all
    subst neg
    simp [kept] at ht
    simp [ht, keepRunTag_neg]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2, keepRunTag_save]

theorem nextKeepSorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws (fun t ys => keepRunTag t && f t ys) = true := by
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
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, keepRunTag_two, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem nextKeepTwo {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws (fun t ys => keepRunTag t && f t ys) = true := by
  rcases le_total a b with hab | hba
  · exact nextKeepSorted hab p h f hf
  · apply nextKeepSorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem nextKeepComplete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs (fun t ys => keepRunTag t && f t ys) = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact nextKeepOne p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact nextKeepTwo p h f hf

theorem uniqueAny (xs : List Nat) (f : Nat → Bool) : xs.eraseDups.any f = xs.any f := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true,List.mem_eraseDups]

def nextDistinct (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  let n := ws.length
  let slack := s+2-n
  let m := mask k
  let u0 := (n-1 == s+1)
  let u1 := (n == s+1)
  let u2 := (n+1 == s+1)
  let z0 := coverHoles k u0 ws
  let z1 := coverHoles k u1 ws
  let z2 := coverHoles k u2 ws
  let h2 := missing2 z2 0 0
  ws.eraseDups.any fun a =>
    let ra := ws.erase a
    let ha := missing2 z1 (covDelta k u1 a) 0
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      (passesMissing k u1 w ha && f (tagU ws a neg false) (w :: ra)) ||
        (slack ≥ 2 && (passesMissing k u2 w h2 && f (tagU ws a neg true) (w :: a :: ra))))) ||
    ra.eraseDups.any fun b =>
      a ≤ b && (let r := ra.erase b
        let hb := missing2 z1 (covDelta k u1 b) 0
        let hab := missing2 z0 (covDelta k u0 a) (covDelta k u0 b)
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          (passesMissing k u0 w hab && f (tagB ws a b conj false false) (w :: r)) ||
          (slack ≥ 1 &&
            ((passesMissing k u1 w hb && f (tagB ws a b conj true false) (w :: a :: r)) ||
             (passesMissing k u1 w ha && f (tagB ws a b conj false true) (w :: b :: r)))) ||
          (slack ≥ 2 &&
            (passesMissing k u2 w h2 && f (tagB ws a b conj true true) (w :: a :: b :: r))))

theorem nextDistinct_eq (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) :
    nextDistinct k s ws f = nextTallied k s ws f := by
  unfold nextDistinct nextTallied
  simp only [uniqueAny]

def nextKept (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  nextDistinct k s ws (fun t ys => keepRunTag t && f t ys)

theorem nextKept_complete {k s ws} (h : NatRun (mask k) (goal k) (s+1) ws)
    (f : Nat → List Nat → Bool)
    (hf : ∀ t ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    nextKept k s ws f = true := by
  rw [nextKept,nextDistinct_eq,nextTallied_eq,nextCovered_eq]
  have hbase := nextKeepComplete h s rfl ws (List.Perm.refl ws)
    (fun t ys => covers k s ys && f t ys) (fun t ys hy => by simp [covers_ok hy, hf t ys hy])
  convert hbase using 2
  funext t ys
  cases covers k s ys <;> cases keepRunTag t <;> simp

def nextDirect (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  let n := ws.length
  let slack := s+2-n
  let m := mask k
  let u0 := (n-1 == s+1)
  let u1 := (n == s+1)
  let u2 := (n+1 == s+1)
  let z0 := coverHoles k u0 ws
  let z1 := coverHoles k u1 ws
  let z2 := coverHoles k u2 ws
  let h2 := missing2 z2 0 0
  ws.eraseDups.any fun a =>
    let ra := ws.erase a
    let ha := missing2 z1 (covDelta k u1 a) 0
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      (passesMissing k u1 w ha && ((neg || keepRunTag (tagU ws a false false)) && f (tagU ws a neg false) (w :: ra))) ||
        (slack ≥ 2 && (passesMissing k u2 w h2 && f (tagU ws a neg true) (w :: a :: ra))))) ||
    ra.eraseDups.any fun b =>
      a ≤ b && (let r := ra.erase b
        let hb := missing2 z1 (covDelta k u1 b) 0
        let hab := missing2 z0 (covDelta k u0 a) (covDelta k u0 b)
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          (passesMissing k u0 w hab && f (tagB ws a b conj false false) (w :: r)) ||
          (slack ≥ 1 &&
            ((passesMissing k u1 w hb && f (tagB ws a b conj true false) (w :: a :: r)) ||
             (passesMissing k u1 w ha && f (tagB ws a b conj false true) (w :: b :: r)))) ||
          (slack ≥ 2 &&
            (passesMissing k u2 w h2 && f (tagB ws a b conj true true) (w :: a :: b :: r))))

theorem nextDirect_eq (k s : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) :
    nextDirect k s ws f = nextKept k s ws f := by
  unfold nextDirect nextKept nextDistinct
  simp only [List.any_cons,List.any_nil,keepRunTag_neg,keepRunTag_save,keepRunTag_two,
    Bool.false_or,Bool.true_or,Bool.true_and]

def checkD (k : Nat) (scs : List Nat) : Nat → List Nat → Bool
  | 0, ws => !(ws == [goal k])
  | s+1, ws => !(nextDirect k s ws (fun _ zs =>
      !(scr k s scs zs) && !(checkD k scs s zs)))

theorem checkD_sound {k s ws scs} (ok : checkD k scs s ws = true) :
    ¬NatRun (mask k) (goal k) s ws := by
  intro h
  induction s generalizing ws with
  | zero => simp [checkD, zero_done h rfl] at ok
  | succ s ih =>
    let F (_ : Nat) (zs : List Nat) : Bool := !(scr k s scs zs) && !(checkD k scs s zs)
    have all : ∀ t ys, NatRun (mask k) (goal k) s ys → F t ys = true := by
      intro t ys hy
      have bad : checkD k scs s ys = false := by
        cases he : checkD k scs s ys
        · rfl
        · exact False.elim (ih he hy)
      simp [F, covers_ok hy, scr_no scs hy, bad]
    have hit := nextKept_complete h F all
    rw [checkD,nextDirect_eq] at ok
    rw [hit] at ok
    contradiction

def insertWord (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: rest => if a ≤ b then a :: b :: rest else b :: insertWord a rest

def sortWords : List Nat → List Nat
  | [] => []
  | a :: rest => insertWord a (sortWords rest)

def cpBoard (m : Nat) (xs : List Nat) : Nat → Nat → List Nat
  | 0, _ => sortWords xs
  | d+1, c => sortWords (mv m (c % 4096) (cpBoard m xs d (c / 4096)))

def checkpointHit (count : Nat → Nat) (board : Nat → Nat → List Nat)
    (lookup : Nat → List Nat → Option Nat) (s : Nat) (ws : List Nat) : Bool :=
  match lookup s ws with
  | none => false
  | some i => decide (i < count s) && ws.isPerm (board s i)

def pickRows (r : List Nat) (w : Nat) : Nat :=
  match r with
  | [] => 0
  | i :: is => Nat.bit (w.testBit i) (pickRows is w)

theorem pickRows_bit (w : Nat) : ∀ (r : List Nat) (t : Nat),
    (pickRows r w).testBit t = (r.map (fun i => w.testBit i)).getD t false
  | [], t => by simp [pickRows]
  | i :: is, 0 => by simp [pickRows,Nat.testBit_bit_zero]
  | i :: is, t+1 => by simp [pickRows,Nat.testBit_bit_succ,pickRows_bit w is t]

theorem pickRows_xor (r : List Nat) (a b : Nat) :
    pickRows r (a ^^^ b) = pickRows r a ^^^ pickRows r b := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_xor, pickRows_bit, pickRows_bit, pickRows_bit]
  by_cases h : t < r.length
  · simp [h,Nat.testBit_xor]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem pickRows_and (r : List Nat) (a b : Nat) :
    pickRows r (a &&& b) = pickRows r a &&& pickRows r b := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and, pickRows_bit, pickRows_bit, pickRows_bit]
  by_cases h : t < r.length
  · simp [h,Nat.testBit_and]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem pickRows_or (r : List Nat) (a b : Nat) :
    pickRows r (a ||| b) = pickRows r a ||| pickRows r b := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_or, pickRows_bit, pickRows_bit, pickRows_bit]
  by_cases h : t < r.length
  · simp [h,Nat.testBit_or]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    rfl


theorem transport {m y s : Nat} {ws : List Nat} (h : NatRun m y s ws) (r : List Nat) :
    NatRun (pickRows r m) (pickRows r y) s (ws.map (pickRows r)) := by
  exact Run.map (pickRows r) (fun a => pickRows_xor r a m)
    (pickRows_and r) (pickRows_or r) h


def orbitMix (x : Nat) : Nat :=
  let x := ((x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9) % 0x10000000000000000
  let x := ((x ^^^ (x >>> 27)) * 0x94d049bb133111eb) % 0x10000000000000000
  x ^^^ (x >>> 31)

def orbitLookup (tab : Nat → Nat) (seed m h : Nat) : Nat :=
  let v := h + 3*seed
  tab (orbitMix (v+1) % m) ^^^ tab (m + orbitMix (v+2) % m) ^^^ tab (2*m + orbitMix (v+3) % m)

def orbitLabel (p v : Nat) : Nat :=
  (((v >>> (fld p 3 0)) &&& 1) <<< 0) ||| (((v >>> (fld p 3 1)) &&& 1) <<< 1) ||| (((v >>> (fld p 3 2)) &&& 1) <<< 2) ||| (((v >>> (fld p 3 3)) &&& 1) <<< 3) ||| (((v >>> (fld p 3 4)) &&& 1) <<< 4) ||| (((v >>> (fld p 3 5)) &&& 1) <<< 5) ||| (((v >>> (fld p 3 6)) &&& 1) <<< 6)

def rowOrient (k : Nat) (sel : List Nat → List Nat) (ys : List Nat) : List Nat :=
  let r := sel ys
  if pickRows r (mask k) = mask k ∧ pickRows r (goal k) = goal k then ys.map (pickRows r) else ys

theorem ori_ok {k u ys} (sel : List Nat → List Nat) (h : NatRun (mask k) (goal k) u ys) :
    NatRun (mask k) (goal k) u (rowOrient k sel ys) := by
  unfold rowOrient
  dsimp only
  split
  next e =>
    have tr := transport h (sel ys)
    rw [e.1, e.2] at tr
    exact tr
  next => exact h
def cutN (s n u : Nat) := if u = s then n else 0

def cutB (s : Nat) (xs : List Nat) (board : Nat → List Nat) (u i : Nat) :=
  if u = s then board i else xs

theorem symCutRoot {k s n : Nat} {xs pool : List Nat}
    {board : Nat → List Nat} {idx : List Nat → Nat}
    {ori : List Nat → List Nat}
    (perm : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (cover : bar k (cutB s xs board) (cutN s n) (fun _ => idx) ori pool (s+1) 0 = true)
    (dead : ∀ i, i < n → ¬NatRun (mask k) (goal k) s (board i)) :
    ¬NatRun (mask k) (goal k) (s+1) xs := by
  intro h
  have hr : NatRun (mask k) (goal k) (s+1) (cutB s xs board (s+1) 0) := by
    simpa [cutB] using h
  obtain ⟨q, _, j, hj, hq⟩ := bar_sound cover perm hr
  by_cases e : q = s
  · subst q
    exact dead j (by simpa [cutN] using hj) (by simpa [cutB] using hq)
  · simp [cutN, e] at hj

def exprA (m : Nat) (x : Fin 8 → Nat) (c : Nat) : Nat :=
  let a := x ⟨c % 8,by omega⟩
  let b := x ⟨c/8 % 8,by omega⟩
  let op := c/64 % 4
  if op=0 then a else if op=1 then a ^^^ m else if op=2 then a ||| b else a &&& b

def exprB (m : Nat) (x : Fin 8 → Nat) (c : Nat) : Nat :=
  let a := exprA m x (c % 256)
  let q := c/256
  if q=0 then a else if q=1 then a ^^^ m else
    let b := x ⟨(q-2)%8,by omega⟩
    if q<10 then a ||| b else a &&& b

def quickWord (m : Nat) (x y : Fin 8 → Nat) (rows : List Nat) (book : Nat → Nat) (w : Nat) :=
  let c := book w
  if exprB m x c = w then exprB m y c else pickRows rows w

def quickOri (k bound : Nat) (xs : List Nat) (choose : List Nat → Nat)
    (row : Nat → List Nat) (word : Nat → Fin 8 → Nat) (book : Nat → Nat) (ws : List Nat) :=
  let a := choose ws
  if a=0 ∨ bound≤a then ws else
    ws.map (quickWord (mask k) (fun i => xs.getD i 0) (word a) (row a) book)

theorem exprA_map (r : List Nat) (m : Nat) (x : Fin 8 → Nat) (c : Nat) :
    pickRows r (exprA m x c) = exprA (pickRows r m) (fun i => pickRows r (x i)) c := by
  unfold exprA
  dsimp only
  by_cases a : c/64 % 4 = 0 <;> by_cases b : c/64 % 4 = 1 <;> by_cases d : c/64 % 4 = 2 <;>
    simp [a,b,d,pickRows_xor,pickRows_and,pickRows_or]

theorem exprB_map (r : List Nat) (m : Nat) (x : Fin 8 → Nat) (c : Nat) :
    pickRows r (exprB m x c) = exprB (pickRows r m) (fun i => pickRows r (x i)) c := by
  unfold exprB
  dsimp only
  by_cases a : c/256 = 0 <;> by_cases b : c/256 = 1 <;> by_cases d : c/256 < 10 <;>
    simp [a,b,d,pickRows_xor,pickRows_and,pickRows_or,exprA_map]

abbrev validQuick (k : Nat) (xs r : List Nat) (y : Fin 8 → Nat) :=
  pickRows r (mask k) = mask k ∧ pickRows r (goal k) = goal k ∧ ∀ i : Fin 8, pickRows r (xs.getD i 0) = y i

theorem quick_safe {k bound xs choose row word book u ws}
    (ok : ∀ i : Fin bound, i.val = 0 ∨ validQuick k xs (row i) (word i))
    (h : NatRun (mask k) (goal k) u ws) :
    NatRun (mask k) (goal k) u (quickOri k bound xs choose row word book ws) := by
  unfold quickOri
  dsimp only
  split
  · exact h
  next he =>
    let a := choose ws
    obtain ⟨hm,hy,hx⟩ := (ok ⟨a,by dsimp [a];omega⟩).resolve_left (by dsimp [a];omega)
    have e : quickWord (mask k) (fun i => xs.getD i 0) (word a) (row a) book = pickRows (row a) := by
      funext w
      unfold quickWord
      dsimp only
      split
      next hh =>
        calc
          exprB (mask k) (word a) (book w) = exprB (pickRows (row a) (mask k)) (fun i => pickRows (row a) (xs.getD i 0)) (book w) := by rw [hm,funext hx]
          _ = pickRows (row a) (exprB (mask k) (fun i => xs.getD i 0) (book w)) := (exprB_map _ _ _ _).symm
          _ = pickRows (row a) w := congrArg _ hh
      next => rfl
    rw [e]
    have tr := transport h (row a)
    rwa [hm,hy] at tr

def sampleColumn (xs : List Nat) (i : Nat) : Nat :=
  xs.foldr (fun w acc => (acc <<< 1) ||| ((w >>> i) &&& 1)) 0

def sampleTable (xs : List Nat) (size : Nat) : List Nat :=
  (List.range size).map (sampleColumn xs)

namespace Row0
def inputs : List ℕ := [0x560aeb5806c0dcbb00d81b2bc00000ffe000001ffc00000007,0x8b5941280965a815012ab5164007ff000000ffe000001ffc18,0xacc1182312d81302615b0261cbff8000007ff000000ffe00060,0x330660cc2720e41c85fc3f8e1000000000000000000ffffff80,0xc21843085bc3786f0e604c0400000000007ffffffff00000000,0xfc1f83f07c0380700b80700803ffffffff80000000000000000]
def vals := sampleTable inputs 204
def scs : List ℕ := [0x1141516c6f19c68,0xe02d088671986a,0x1402d0286f1b87a,0x88151147a1a06e,0xe0220b46a19867,0x1404516c6a19c66,0x1140a1406f19868,0x880a0e06e19c68,0x1140a0887a1b86f,0x1140a054681a866,0x880a0b46e19868]
def target : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def qBook (w : Nat) : Nat :=
  let d := fld 0x4a648404137690 3 (w % 21)
  fld 0x438d8c0002a545d583cc8b010000849ddc81c2d49cc34185e5c442820095ca058a034494c1cb00004093cd04ddd3c5 8 (((w >>> 17) + d) % 47)

def qPerm (i : Nat) : Nat := fld 0x6444af142c791163d2b28695a2358ca000000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0xa8009d927a000000840079b36f00bcb15bb05045430000008200778f6e00988d388c2d222000757f15740a6807006a670566030000 8 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x1ac688 3 (fld 0xc2442484a9320293200f4a0006d822688000 3 (bsr 0xf7831134f4fedb03ef42530ceeb6ca99dd448942d75a4f37d12435e6ceeaee09cdfdf8d5c84b49c4c0a8f783b5e46551b359a4deb279c2a1b0edf685b0147856aee40560ae8440cba181a3399de14f0f9b4f693095865b2993b4971e9375f304880f16b08715b59f73aa60ef6f5f01b26e5e2e6b6decb162639a36156375fee9527a8cb85157812a493de4eb4577ef263b056ff32e79e25f2c0f0be325862c5321a9d46920ee1b271e6cd2651774472c1683bb1211c516140dd37f0e0aa5544e073f6720 32 (hk ys) 6 0 49))
def qOri0 := quickOri 102 7 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 7, i.val = 0 ∨ validQuick 102 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 102) (fld 0xe21e30e41105505f41503f31f30000f10400e40401f21103e10 12 i) inputs
def I (ys : List Nat) := bsr 0xf7831134ef42530cd12435e6ae8440cba181a339880f16b08715b59f639a36156375fee9527a8cb85157812a2c0f0be31683bb1211c516140dd37f0e0aa5544e073f6720 32 (hk ys) 5 0 17
def test (i : Nat) := checkD 102 scs 8 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 102 (cutB 8 inputs B) (cutN 8 17) (fun _ => I) qOri0 scs 9 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 4 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 4 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 2 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z14 : span test 3 14 = true := by decide +kernel
lemma regionOK : span test 17 0 = true := by with_reducible exact (sj (sj z0 z4) (sj z8 (sj z12 z14)))
theorem finChk : ¬NatRun (mask 102) (goal 102) 9 inputs :=
  symCutRoot (quick_safe (k:=102) (bound:=7) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 6 target t → 10 ≤ t := by
  refine proveAtCap 6 102 9 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row0

namespace Row8
def inputs : List ℕ := [0x4758c02323e0239c600989f15980f07857001ffc00001e000ffe00000f3ff80703803,0x8a094d651e24e504a26a87100a8f908bcd0000007ff1e07ff0003ff870000078001cc,0xad412856ae0404a09466d7820151127d1f2ffe0007ffe000000003fff800000003c1f0,0xae95d385404009412883212457a7a03fe88ffffff8000000000000000003fff803fe00,0x310621188488de8bd1cc42001dc7ffd01200000000000007fffffc000003fffffc0000,0xc218426109116f0de1f787ffe60200224000000000000007fffffffffffc0000000000,0xfc1f83fe0ffff00e01380448b8044480000ffffffffffff80000000000000000000000]
def vals := sampleTable inputs 280
def scs : List ℕ := [0x1d8682048f2348c,0x1d84507c9f258b5,0x1a0500dcb52449f,0xdc1f114962308f,0xdc1f140912308d,0x1d8371a0b523c96,0x1a01f1d89f23491]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def qBook (w : Nat) : Nat :=
  let d := fld 0x3830c9540986602340000289021 6 (w % 19)
  fld 0xc10144d3d5008e00c5cb8a81cddec49ce6c64285049302c3824103a58c8ddcd6dd960043469dee8b94c2a60584e58340ce00ae869e45d495ca06cc 8 (((w >>> 5) + d) % 59)

def qPerm (i : Nat) : Nat := fld 0x463d66543243566d2a60c5852ee70a058ab4421cea831aebc60400000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0x399b6d00000001170000219010033400c2002f976b50000001150000168aa003f000f200299449f003ea108183bb8ec737c9a1d46574984ba5b0000000000038d64a900329aec16b1408a4200324009d002f53296638dd72335c0c0582a00001609c57a943e1b0025142915005c28120024d300e4ba3c1609490191a04460080000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0xa9876543210 4 (fld 0x390316102385a747615795325321322065498800498870526050420542332101 4 (bsr 0xffb93cdefabd6fedf7423f9ff582b9f1f3eea8d9f1d7b75be9e8d5bae5792811e114fcb2df5d4d4adc65c784da702df4d622589bcfb96cf1cec4936bca9679c0c7c1e596c27abfbebd935c50b84dff99b6afeed9b5124aadb06b5123abf9511da91b880da8bfc72fa3016442a219af959d6d03769cd84ac39b5f3f3a969bfb69910afed88cf5763a8579a19a804750dd7e6767d87d7567f679c1958678a4f16178a3812770f9676d6a3fff10689e704a676cd73d647d8899587d0c395843e1385545aa6351ec39f451744c1d4a197648498a981d3dcd5e1a391e942f367f10d32e65260a29ce9e4826bdf0a919042b95183e48a70fd8f69e0644477e063cd20e 32 (hk ys) 7 0 64))
def qOri0 := quickOri 140 11 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 11, i.val = 0 ∨ validQuick 140 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 140) (fld 0xe10f41506e54000400f40f10106e41 12 i) inputs
def I (ys : List Nat) := bsr 0xf7423f9fe5792811969bfb6979c1958678a4f161647d889951ec39f44a197648391e942f0644477e 32 (hk ys) 4 0 10
def test (i : Nat) := checkD 140 scs 8 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 140 (cutB 8 inputs B) (cutN 8 10) (fun _ => I) qOri0 scs 9 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 2 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 3 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 2 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z7 : span test 3 7 = true := by decide +kernel
lemma regionOK : span test 10 0 = true := by with_reducible exact (sj (sj z0 z2) (sj z5 z7))
theorem finChk : ¬NatRun (mask 140) (goal 140) 9 inputs :=
  symCutRoot (quick_safe (k:=140) (bound:=11) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 10 ≤ t := by
  refine proveAtCap 7 140 9 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row8

def seedRaw : Nat → List Nat → List Nat
  | _, [] => []
  | b, x :: xs => if b % 2 = 1 then x :: seedRaw (b / 2) xs else seedRaw (b / 2) xs

def seedWords (word : Nat → Nat) (width : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, c => if c = 0 then [] else word (c % (2^width)) :: seedWords word width n (c / (2^width))

def seedW (raw : List Nat) (word : Nat → Nat) (width c : Nat) : List Nat :=
  seedWords word width 9 (c / 64) ++ seedRaw (c % 64) raw
def mixCheck (k cut : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → List Nat → Nat) (pool : List Nat) (s i : Nat) : Bool :=
  if s ≤ cut then checkD k pool s (S s i) else bar k S N idx id pool s i

theorem mixAll {k cut S N idx pool cap}
    (hc : ∀ s ≤ cap, ∀ i < N s, mixCheck k cut S N idx pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi run
    have yes := hc s hs i hi
    by_cases small : s ≤ cut
    · exact checkD_sound (by simpa [mixCheck,small] using yes) run
    · have b : bar k S N idx id pool s i = true := by simpa [mixCheck,small] using yes
      obtain ⟨q,hq,j,hj,h⟩ := bar_sound b (fun hr => hr) run
      exact ih q hq (by omega) j hj h
def seedAtom (xs : List Nat) (m a : Nat) :=
  if a=0 then 0 else if a=7 then m else xs.getD (a-1) 0

def seedGate (m op x y : Nat) :=
  if op=0 then x else if op=1 then x ^^^ m else if op=2 then x &&& y else x ||| y

def seedExpr (xs : List Nat) (m c : Nat) :=
  let x := seedGate m (fld c 2 3) (seedAtom xs m (c &&& 7)) (seedAtom xs m ((c >>> 3) &&& 7))
  seedGate m ((c >>> 11) &&& 3) x (seedAtom xs m ((c >>> 8) &&& 7))



namespace Fixed39

def raw : List Nat := [0x36cdb4db36d59292adb000000000000000007f,0x41785105e14b2e2e585003ff000ffc30e0e180,0xe1906386418e7474706ffc003ff000c7070600,0x8a228ba8ea30497f828000003fffff0007f800,0xec3b0e308c207fc9030fffffc0000007f80000,0xf03c0fc0f03f8000040ffffffffffff8000000]

def pool : List Nat := [0xb000108511404f,0x88000b04e1344c,0x108000e0521384d,0xe0220005013c51,0xe0000885214450,0xb0220004d1304e,0xe000108521384c,0x108000b05214450,0x108000884f1384d,0x88000b04f1384c,0xe0000885113050]

def word (i : Nat) := seedExpr raw (mask 76) (fld 0x1c1d20f5d7a03d01e3af307983c800c0ea00283680060e202083840080d102269180052d904d02c80020b102181151d80460488288000000 13 i)

def unpack (c : Nat) : List Nat := seedW raw word 6 c

def first (i : Nat) := fld 0x228bf0008bf02267f02237f02227f89307e8a207f02207f89d07f89a07f89907f65907f01907f00007f89607f89407f89307f89007f88d07f64d07f00d07f54d07f44d07f34d07f88907f64907f00907f34907f24907f88606f88607f88405f88407f88207f4c107e68105f88107f74107f68107f64107f00107f58107f50107f4c107f40107f34107f2c107f28107f24107f20107f18106f18107f10107f10105f0c107f08107f04107f 24 i

def S9 (i : Nat) := unpack (first i)

def second (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x22241fc000907f014241fc04c907f000201fc000805f8892017c024805f0082017e24c606e022181bc064606f000181bc000607f017181fc044606f88f1819c034606f009181be21c606b006181bc088507f89310178088405f022101fc064407f000101fc000405f00d101fc034405f009101fc024405f8861013c010407f0041017c000307f000081fda4c105e013041fa180104f858041bc07c105f01c0417c068105f000041fc038105f00c041f562c10796cb0416da28105d74804179320105e0080417d318106e6860413c018106f3c60419c718106b4c404178010107f0040417c610104f403041f14081075
    | 1 => 0x2289a7c00228bf000022fc002277f00089afc002267f000019fc000003f000896fc002253f000893fc002243f00088dfc001537f00088bfc00222bf000889fc001927f000009fc088d27f000349fc002223f0222487c08a21af000886bc08991af000886fc08911af022346bc08891af022186bc08a211f0008847c002213f0223447c088911f0221047c00220ff000882fc089307e0194c1f8001307e0134c1f804cd07e0226817c001a05f000881fc001d07f000681fc001907f000001fc001607f000501fc001307f022401fc001007f01e3417c06cd05f01a3417c000d07f012341fc000b07f000281fc068905f
    | 2 => 0x8a24fe000893f808994fe0224d3f8089337e
    | _ => 0
  fld w 30 (i % 64)

def D (i : Nat) := unpack (second i)

def N : Nat → Nat
  | 6 => 347
  | 7 => 572
  | 8 => 412
  | 9 => 57
  | _ => 0

def c8 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0xdf94d0210a0e0747750edc99107d6982b765c0c429b301840c721004d92b50361e1c410012cc107756c4037f53cc414c2526edc3310301b3e7b70cddc6bf54c440d5b40789c64b605ac82a25412e01ef4542d4161006ed01868318418235264c4183106ecc2be637a9856b60d28c15b7066d44527019dd74f63d4dc16b70d5dd43b70208431774a8e067281d3d92a310
    | 1 => 0xc040501046441831076ed8156231ca0341047bd91910555c9c02af544015b300ecc1221075e18c210d9815d310d59c90b406cc404210d6d81b7767a9071b6076d8023726d9c4018f12d804786afcd19b1018411eb60b2d80d210ad4133310184173774d690023430ed03877532dd0a323d2d03510461e156775d9c16b763d2d82f2845ad43377666d42b10284c435a70
    | 2 => 0x34e09db720ed4a23103c840a354df8d03b42ac410236241dd84683e19c9010330a09e1006440ebe54404173b30a4e058784d29c2bb50584103a326ec403b607a9475774088406b4034a0dc3103ce0b510056d82be65a4c40138212ccb7764d441467745cc435776cddcf7e5412d41bb5066d876104ced816210644116b4014a0a410092dc0a3627ad44310031e1ce763
    | 3 => 0x2484331003acc19b70008416105d09c36604c4400a21011e158b30d9c19b10468e1e331059dc8cb70e040c734275e1d3210e1dd34f4508e0b410511e1deb505441432100d409b673d7d4b02839cc40610024e116103e1dd83b5028e115b50dc40c5210d8416bf53d298167767ad07410390c41b10588e09eb70d19c381047ad846b3041dd0d230b2c418b409ce104b20
    | 4 => 0xed88b3826c40c736278c43377554410b2101ad83477319ddabe6478412cb400c41803cfd5dc37763dc40b3b50dd4124a615441873720047d9b71dc4133b7054840621000ffc31057ad037765d1dd1810062dc1d281afd906b70e04177503cec406672a0c427251b04031b50dfd519b40d1ddabb60b2d42be536c419a28156c83177562e003b20d9c10039f6ddd64104
    | 5 => 0xaf8d15502aecc0735266d07660659dd1b77462d427b7428dc8667368c40c38479dd8e2100127d5f6362cc731041ac82410576dc297630484272439de1c6b5066cc2028138e096b3011e124b618ce095102dfcd33b40acc40037fbcc41c281c44104b700c413877300c7eb76490405e77591dd83103ac40173644c40abb40d840ec10442d8187860c0031b40005fd8b60
    | 6 => 0xafd8d9a311ce0d010014e1d8b10b040f4a4028e09db615440f1776ac40f110566d817381afd96c10542dc34a50a0a0f4b5028e15e1057840c4b4079dd19100
    | _ => 0
  fld w 18 (i % 64)

def S8 (x : Nat) := let c := c8 x; if c % 16 = 15 then D (c/16) else mv (mask 76) (c % 4096) (S9 (c/4096))

def i8 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x103437285001092d000a002d002710160f1b0007071b01152002001e14142e00020b023f02013500000a0201010829001212000c19480f090304010540020001
    | 1 => 0xa0010272a0030600631817060003b72e4e6837201d04040d0c251678181d0324080141250e0f00160b171c00001319000200070573430a003f64061937180f02
    | 2 => 0x3813c252f6a137e006027
    | _ => 0
  fld w 8 (i % 64)

def c7 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x96880cb4408702085130207989aa1814fa60296a6192118614cd25aec90710084980d204116f6824d3711e382ab8d825a420a876096bb18648c06e200f9b40541b00988c1e8604ae304c7b300e88c1666c118302c41a050084012c25256601b9392a040c90c06a23326a13895cdc728680487053b9c02498d0626057c271c39a8259881a444221750549a8160dc6916817f370509b0da0e0ce56c0f837104b0a8e4dc04c70b22662
    | 1 => 0xa4381828902926033b26024080e6cc0a5acc04e3438eb1b959d8d96ec70f2218fdb03e4cc078e0c653704f9a852198a146e0a850623180d41402e86c00f2201f9b8018c0cf46c17c3016090160c9c8d66e0a82101b908514843106270d202299b042c9c950c0426305109a020c982442085022076083e3dd9470c064830265980ae4dc150ec8b7b010f98114cdc06a602023017a1403e4d40ae4e0a230255b018e0401be646b7660
    | 2 => 0x490842c84070202c7207511091d8c070e680b7763ab1a012040c226e0832134e1082a8c0822626f32717cd98344d81526818d2309708047cdc1064e038b3224383450dc150ecb1a3506d1808ccc0412c04f63128f28020cdc4a4602ae371ca1a8410c08ac4209c2704c929a58401502052d6107c9b007cdc2c46c009103649b013484e5a2080a38024389a5cc09266e14810510ba053880c43680f42309e083d14dc106e2805271
    | 3 => 0x9518a304948122046624004880e3dd8c7a602f9730ab1b00b08856e2091d2027c8804eec8078460b71034c1809048402c6021e30154530121c11c06a1943602c139084d82a020065302549b0668c089c6e6a8105c41b01acd812446139301be8803e584d6e6039b3031c5a9344d02cc680953217c882c10841444618230292bb2a348c0a66a0a8763701b82ccd403c608c7206689a8114840acec993301240834b8415a060562370
    | 4 => 0x8f08048c405206c1227632b309ca8dc28e643563705bb3110c8c180605472208eb1b5cc9c10e6c0b6301543824d0c8412e0aaf230395b9194d01d668656612c51109cad8a504e23a301c39b8050840064a8a8703a43b28c89c16f6422110096881c8ad002a4212d614219814488809a4084d22096b09b2880ae86a021b6004b832e4c86c2c0696705571b84acdc576620f97507cb085dce01a26e061302be083c7c9c81e6c065350
    | 5 => 0xb59814a0c04784044276459910060dc150208096142b3b0628c052a44048104a11103e8c06804600222060108044d02ac6a1943702011066c408e4e6c09613599a01c0c4070c2c9650004d21a8cdc0426612210522981355d95d44e58f30196b3147ddda906c0f91042699018ce0182c6e0f370bd9182a4dc22c6e3853050c1a8618981f36a140380329b028cd03106a072340401c266c88490a0056104545b0130c84916a47a370
    | 6 => 0x109a8490841c06c03c312c69082ccdc08c460312402f181060e02564e0ae3218fb82e34c0992681013027c1104148c0c26e0a3350a73835ac9c1dc60aa80001c58115840df26818fb21b910198cc0c42ec04d207a3110cb5849ec6c2a87050c9081808dd9644247371359a83e5d8322602113604b082c7ddd70c4e0d131348182a0cc0a90c058f103239032f4c0a914818f7647b18827cdc2346e148760179401f48c25a20af9740
    | 7 => 0x4b08198c099e40f853017cdb019c8528c60260210089a8086cc0120004c22010da862c884ca6267a350240803b0c04027014f27057182aa04196eeca0f340928821c88c0eaea96235004882e1cc05502009e2702b3b2922c4950cc58f662543812a180f0e6c015b60a40802a181012209273744f1085dc8c0ea60489230649a81249c48e40e2c37029981b9cc06784e2f9106879b8122c08e4e6f3430321330488c425a20d72253
    | 8 => 0x1c383024402c646108360bd9810244184c700cf20404b994b94023cc2c9233253980b24dc176486df382bf990b7c9013e6c1743708918083cd43106e19a2309e180b30c06346c0d62052c18852180efaec89f34094083958419ec6a32d7658b13816cc06e66ed22b20c7d80885cc0a468609500c11c0114dc070a00a33603b118240c1196604c1707859905ac840306c048105481b8355981be70656105
    | _ => 0
  fld w 21 (i % 64)

def S7 (x : Nat) := let c := c7 x; mv (mask 76) (c % 4096) (S8 (c/4096))

def i7 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x184400020380052081200000070e030060200820700f0003c060400000020e0101802050981c220200060121a0b07806210988c0a0d0480c060a000a8102802838260b038000601
    | 1 => 0x3c06892335b000809b02070000d0005822041c0049e1a1304c08001681c48364b8940e1a00020540c0281818200289800000d8e8d2590081000032c02808020e8300e5e000d81405
    | 2 => 0x6b7a1bb4b1f2a9ed641c06c504c748b490bc02aa0001b726b2d1119e0500084fa01c4839061079014ac00163fc1468040e001330984430150680d3600650002228048140c0d
    | _ => 0
  fld w 9 (i % 64)

def c6 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x640d45313015d8985ff1005f4d417e3012b488169202444c085050033488050101218d4046613118840466125c8c0593230114d801d7257a08800c3418cd8da0234035cc81da321010881cc6347e498633240571d50d03705844018e71309c40439220090c85c33404c8d401d33039ac84f0302090d88af2201ac88072105744c08501004248c978204768d81dc340454881ac302114c08a1360638981a130208cc097f2105b4c047d301774d40c9362
    | 1 => 0x414880c43016dcc08501047a0c4d2422011840d5030156cd80b43507f88c1c2103400c0987350398c054e361140415ea3101c88401f2203d88820323012084205302274cc9ec3401b4c0cd9103774c81c43217e0c422522039ad44e2220260d01953015e890115361144d001d7265b488629301420d048e2203e0d84571036008818b22015cc05f33021848c2272101e4d00d9650774d807210024c41449301628c09b5360600c05373401c8411c0302
    | 2 => 0x7ccc046e3405f48815f210788d81bf103709d48982107c4cc47210336594471240814901c122011840a26220090c0c9a210365d50e31011d4c0c742206a0841f52101bcc0633726184cc8f4360830c09cd220098c11642306b48c19022024c410863405fc9805d3511418094f24086888044214394c08276028c4c11b1220571d4a3b221228c098e3617084123a210709945a1341284d415b3407f4c097e1061d0d85082204d48404737014040994302
    | 3 => 0x398400403602109c04f23114040e173406f4c08e6b015b8c08e6b41788d00363027e08982f203600d45a1351798d8078302144d815c651214c08123404dcd40b92308ecc0c5135072cc4ce610331c88086360284d00e13023d0d0046610410d80ef30122c810e433017c984507041c8404571004e480594313365d48a33011e48818630185c881d174372c880003505f89851e340170d00ad10187cd81cb363238cc0a2301270c0c193603e0880e3321
    | 4 => 0x600d85a8360158d85f030214184c46105784981012202e8880e130424c40027500074881803417748c94e2203d0d418c30213cc043d303370c0554220684d857d3400bcc8d0e2208c48c18b3615f4d80507034fc880643010448c1dc3501184109c314390d81dd34012cd801db502e4c04d8102064d01eb303070d80e435034cd443a35015ec04466148dc881b2220170d405c3601d4c90193506944011c30121cd44e61041388c1672200d48c09d301
    | 5 => 0x4610008cd01e635038c882163011b8d4072610420d848b3036789818e2121c984d97230304c083830472cd862f30187c984d8302398415bf1008a0c088734157cd810a2202c088074303
    | _ => 0
  fld w 22 (i % 64)

def S6 (x : Nat) := let c := c6 x; mv (mask 76) (c % 4096) (S7 (c/4096))

def i6 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x140024000004421180085e03018144047020c8ec05090a804121413000070d8003a02060381c3b09058200400000683d0100c00080002400000081c160b0000426080181c0c00
    | 1 => 0x23cae0266a78000000accc200044c06ad56b18a6a00a62e620063b8000600148002e09249583ceb6301d180f0028c040c010891445089004001
    | _ => 0
  fld w 9 (i % 64)

def S : Nat → Nat → List Nat
  | 6 => S6
  | 7 => S7
  | 8 => S8
  | 9 => S9
  | _ => fun _ => []

def I : Nat → List Nat → Nat
  | 6, z => let h := hk z; (h/115 + i6 (h % 115)) % 347
  | 7, z => let h := hk z; (h/190 + i7 (h % 190)) % 572
  | 8, z => let h := hk z; (h/140 + i8 (h % 140)) % 412
  | _, _ => 0

def chk := mixCheck 76 6 S N I pool

theorem h0 : span (chk 0) 0 0 = true := rfl

theorem h1 : span (chk 1) 0 0 = true := rfl

theorem h2 : span (chk 2) 0 0 = true := rfl

theorem h3 : span (chk 3) 0 0 = true := rfl

theorem h4 : span (chk 4) 0 0 = true := rfl

theorem h5 : span (chk 5) 0 0 = true := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h6_0 : span (chk 6) 256 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h6_256 : span (chk 6) 91 256 = true := by decide +kernel

theorem h6 : span (chk 6) 347 0 = true := by with_reducible exact (sj h6_0 h6_256)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_0 : span (chk 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_256 : span (chk 7) 256 256 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_512 : span (chk 7) 60 512 = true := by decide +kernel

theorem h7 : span (chk 7) 572 0 = true := by with_reducible exact (sj h7_0 (sj h7_256 h7_512))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_0 : span (chk 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_256 : span (chk 8) 156 256 = true := by decide +kernel

theorem h8 : span (chk 8) 412 0 = true := by with_reducible exact (sj h8_0 h8_256)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h9_0 : span (chk 9) 57 0 = true := by decide +kernel

theorem h9 : span (chk 9) 57 0 = true := by with_reducible exact h9_0

theorem allChecks : ∀ s ≤ 9, ∀ i < N s, mixCheck 76 6 S N I pool s i = true := by
  intro s hs
  interval_cases s
  · exact fun i hi => spOK h0 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h1 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h2 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h3 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h4 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h5 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h6 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h7 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h8 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h9 i (Nat.zero_le i) hi

theorem dead8 (i : Nat) (hi : i < 412) : ¬NatRun (mask 76) (goal 76) 8 (S8 i) :=
  mixAll allChecks 8 (by decide) i hi

theorem dead9 (i : Nat) (hi : i < 57) : ¬NatRun (mask 76) (goal 76) 9 (S9 i) :=
  mixAll allChecks 9 (by decide) i hi

def index9 (i : Nat) := fld 0x97e9c00369d084000d0382403f100a62fbc0a5661e2d22ea4c388e8c080e28f500947a9202d0300390343ea01a2485b599a89a0b3ae7 6 i
def index (s : Nat) (zs : List Nat) := if s = 9 then orbitLookup index9 5 24 (hk zs) else I s zs
theorem atDepth (s i : Nat) (hs : s=8 ∨ s=9) (hi : i < N s) : ¬NatRun (mask 76) (goal 76) s (S s i) := by
  rcases hs with rfl | rfl
  · exact dead8 i hi
  · exact dead9 i hi

end Fixed39


namespace Fixed40

def raw : List Nat := [0x9b24d97cd883b485b53e0000001ffc000000000f,0x1454a2a862d76517352e200000000003ff83ff870,0x3861c30c8338463826345ff8ffc6001c001c00180,0x2289d471142188bdb8c08000fff80000001fffe00,0x3b0f1842183df0e1c0811fff0000001fffe000000,0x3c0fe07fe046000600081fffffffffe0000000000]

def pool : List Nat := [0x11c2a0e85b14c54,0xe80b0a85214456,0xa80b06c5b14453,0xa81b11c5715051,0x11c2a06c5415852,0x11c0b0a85414c5b,0xe82a02c5315852,0xa80b0e85315851,0xe82a06c5b14853]

def word (i : Nat) := seedExpr raw (mask 81) (fld 0x3f9081d40f4078fa841b40f30797a4400c0e90767687b2200506e0367743b9100183880820e102100129d20ac05a02701a20449e8ea840040b204d00041320b1021a36408a8ec02323c81432460488288000000 13 i)

def unpack (c : Nat) : List Nat := seedW raw word 6 c

def first (i : Nat) :=
  let w := match i/64 with
    | 0 => 0xcd507fcd107fa5107f7d107f69107f45107fcce07fa4e07f7ce07f68e07f44e07f38e07fccb07bcc906fcc907fcc705fcc707fcc507fcc307fcc207f74107e6c107dcc107fc0107fbc107fb4107fb0107fac107fa4107f9c107f8c107f88107f7c107f78107f74107f70107f6c107f68107f60107f5c107f54107f44107f40107f38107f30107f2c107b24106f24107f1c107f1c105f14107f0c107f08107f04107f02907f02407f01a07f01f07f01107f00e07f000cff03307f00107f00007f
    | 1 => 0x33cff033a7f0337ff0336bf03347f0333bfcdd07ecdb07dcf307fcf007fcef07fced07fcec07fceb07fce907fa6907fce707fce307fce207fcdf07fa5f07fcde07fcdd07fcdc07fcdb07fcda07fa5a07f91a07f7da07f69a07f
    | _ => 0
  fld w 24 (i % 64)

def S9 (i : Nat) := unpack (first i)

def second (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x291c1fc000707f0001c17c07c707f01a1c1fc068705f0111c1fc044705f00e1c1fc038705fccb1c16f324704f0071c1fc01c705f033181fc000507f0000c1fc000207f75b041f2f74105e01d041faf54105ec9b04176f6c105db1b0417406c107d795041f4048107db230416e388107b021041ec080107bc68041bc098106f025041bc0c8105f02f0417c0b8105f02c0417c0a8105f000041fef8c105fbde0417ec70105f019041dc04c107b0100417dd2c107a6cb041e6f2c105b00b041edd24106e6c9041b4024106f5090419cb24106b74704179b1c105d007041fc01c105f2c70416c91c104f0040417de081075
    | 1 => 0xa41fc000007f0009c1fc002307f000881fc001f07f033781fc001e07f000741fc0cdc07f000701fc001b07f02c6817c001a07f000601fc001707f000581fc0cd507f000541fc069507f02f4417c001107f01c441fc001007f0004017c045005f0104017c000f07f01b381f40bce05f02c3817c000e07f023381fc078e07f000341fc000c07fcdd2c1eb36cb0790332c1ec0a4b07b0002c1ec068b07b0112c1ec044b07f00e2c1ec0cca07fcdd241bb36c906d033241bc0a4906f000241bc000907f024241fc068906fcd42419c044906f00e241bf32c906b009241bc0cc807fcdd1c17b36c705d0331c17c0cc707f
    | 2 => 0xccffc0cdb3bd000ccefc001a3bf00044efc003337f000cccfc0cf32fb033a4bec0cda2fb03344bec0cce2fb033cc9bc003326f033a49bc003327f0337c9bc0cda26f033449bc0cce26f033249bc0cf31df000cc77c00331ff0337c77c0cda1df0334477c0cce1df0331c77c003317f000cc3fc00330bfcdd6c1f00cdd07e029741f8001d07e01f741f8075d07e01d681fb3bd507e01d441f80cdb07d0296c1f4001b07d01f6c1f406db07d01b681f40cd207d033841ec0ce007b033981bc0ce506f000bc17c0cee05f000b017f3beb05f033a817c003307f000c01fc0cef07f000bc1fc002d07f000b01fc002b07f
    | 3 => 0x33cddf8003377e033a5df80cdf77e03375df80cdd6be033751f80cf36fd000cdbf40ce96fd0337dbf40cdb6fd0336daf40cf3bdf033cec7c0033cff000033fc0033c3f000ceffc0033b7f000cecfc0033aff000000fc00339ff000ce3fc00338bf000cdefc003377f000cdcfc00336ff000cdafc00006bf000cd8fc00335ff000cd6fc003357f000cd1fc002947f000011fc001147f000cd0fc0cd141f
    | _ => 0
  fld w 30 (i % 64)

def D (i : Nat) := unpack (second i)

def N : Nat → Nat
  | 6 => 218
  | 7 => 443
  | 8 => 453
  | 9 => 94
  | _ => 0

def c8 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x576404c4088b3a0eb2056ce40f991f928b0a411a6840c40428820366266ce208416693b00e515a6a203cc18083d967007ea2ac41585a803f640ece603d5185b00877204206cecc17db856773306a424408208283e544c4a948e1499c183e4201e4003d4c33b8801035c702084001f10d9772656c01040eebb956774042041d41e910c473830000082dd6c7b200e315f6c021dd19b3a00b60
    | 1 => 0x64ee603cc42da0081040620801dbc108300b2012a035ed80079a00f426b6c0b8dc41590035021f6841c40e59c0b2775542063e8c8c9a9015075ef0a13d159db82f783384e569dc8208305b1007c641041c75a900b30016a00f9859882d7b308e5021c40ae082b3100186c52c94c69b956771003fe0c409988200f5001ec169dd2db3984b502420619dc969c0b2674116e0a841400afd6b70
    | 2 => 0x6420611dc407880110260206499d0073203e630620cbed0153ba04f630109ebec400732a13850420e01418073107b1011e856441407b2b01052220c5ed917db8835031d6640c416d88287b606420abed855bba2fb5191660384180790847740b6e022c42b5a00167301c84cadc1b5a82ab200c2055ad8061b90d35207c68014119da83f3830aee478a082283953231c2080fd057b4205b60
    | 3 => 0x10ce648410c9c150101186a42440e29c08014f0420914a103083837611d4841ddd061c100f6424ce45c948008084b70056e00441553b999376656a00f9481fb083e410ace20fd5007a883505616e15d9cc05883f2810027e104101fa9037630ca0e0395013b901103b0ce6cac40e9c1af1001a704cec4038838050010a0e1c4193114006627f6c8c2d007d9006b6007e6464c8c1f2983f63
    | 4 => 0x56817441407a08016f2e70613d4ec0828054f1ed095c416d33983e31056a02040ab08001107096615edc08bb98044fa44a80140808832e341ac2060acc013ba5b7701ef0612d0101c156b302420a0c40c25b0077720097e74a0ab8800010401e812edd40719117751220a1440807308f7854c70a3841d0129dd6737f6c165dd000800350154ee4cad0000810910407ec4199cc4d8803f53
    | 5 => 0x800004181f98d6b500a20ec2cc17da0b3103616620003c12839110300d3e54d88708280e6301e64c2d45959807b700aa0eb4d840729911040c20a46c82659857b5061620ced80c99237b7002ee8444147db10fb725f6602041402818098f0020acddcc7da90031000ddebed4003cfd3283af62158414288286b700045e2040ebb3882b601220c1840dadb833b4007ca2038d005a007104
    | 6 => 0x642080f9941f314bb7000a0361dd2bbba03f42baee963d8c13399535208ce60fd9520811b3829870a6ca1025880577402208c041807108076101ec4184183f993210606a0813d903588321005a6e36ddc971a885b5001ec20394840838350600a0aad9cc1f9080f632a6e520a05808200f52ad62001d8c07209728202ee5189c4959006b505f4620fcd17dc00065f602000223c70818052f
    | 7 => 0x3678524ee61441ac3b857b40
    | _ => 0
  fld w 19 (i % 64)

def S8 (x : Nat) := let c := c8 x; if c % 16 = 15 then D (c/16) else mv (mask 81) (c % 4096) (S9 (c/4096))

def i8 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x6418020815408000e014440e0f8100019070e02804000d800070200c3400010bc000d078000603078905a00030f4000e0405c0c19000000e030085c0c03158400a02028ac1405
    | 1 => 0x2006010835d063c0f4280609138a808010193c0c2704b58f269102800846000a03c3d0605410110283c00000582c3e000000006100c1c8001f01808600400808080600028fe00
    | 2 => 0x43a200482020c048073e01800240602020181601835b00f5f39c26070030dca01
    | _ => 0
  fld w 9 (i % 64)

def c7 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x3e908454dc1b86074637276882ad8c09c66068d301841b8b90d01baec05c603c7080634c40386e18e50054880214c4dfe6052b3040a0823d8c1000a015b380909021f0886c0606c8b5216181ed041d2a6e19f301a39808ac81b086a25ca60a0f99408cc2ce44318b31409b0010d006c20afb301bf5a8ef8d82a9c21b21000831b96c40c92641343402e3015a8c0468e818e60472188430c12fc60214301d3180b58c120446434303
    | 1 => 0x621290b4c06ba604f03033e18089cc1204604de302b71810c0d831a681907741b08100cc094420743340768812c0c06fd6025c2102e9812dec82aeec4a530282d90ae8c14b620ac8b32181a0648d407a6c0d8100de9a8698886fd4617eb20c6181daccc222201545035bd185fac875166210b72d7980a89d89bc6a154103c7581040c840260a1b304cc98097040ddb6c3b871464181910d80b42005c703589b06ccd40be6e0d8500
    | 2 => 0xcb1a81d0c0cae6a0f6350c412959cdc9884207d3701a08067adca226078e10191108171d886c2085b70576883170410b820c3d3022e3826f4dc21c60236106623b9b70c0488604ed660b49b80d1c0dba2099020717980ea0403086c2a13712e302658c09db602ad3509f9b8360406cc60518b017f9824d4c1068ea19e3022e1b0468d41b240e14b31de8816ecdc6ae206c13707a0800d998068ec143360291a0001c0ab860446303
    | 3 => 0x9a1908d840d0820e00105b29c2d5cc06c070788372721a82148cabc6025f304768822dc40f086276f2218a9a855c415fa6021a205019084c8885567005c1004f980b90dc10260a30370171b8634d80b6e060638431980ab4409f2603bc3820a5808d2c0dc86c000703021a85bc81dde604ed301d71a86f4d8314602c81005213830c887704e0a21053b10811adcc0020716383273b10ccc095a60734350569b810c80990e070f205
    | 4 => 0x621013b440ea8ea000104d428000c8c0586a1b130133989c88dc1e8a00673023dbb116dc08606a0093059a1b8058dc4086e44327282bb030c81cda408c83400a5a0b20404926086930142918310dc8a660354f3081182110c14cc6070c3502f9a858884029642edb21331c10d0d02686e58d35082bb15f840dce42143370c6180810c846820315304c21b8971c095a6c04e760abd988f4c14386c15b20282d80dacc09f860359270
    | 5 => 0x9a9a83b5d8c92665545011d9a837c8400260443302641811188c8b8ec152302b79b91384106820a95210aa788454d818a6045a3210a081cc8c07766041f3013a5a1b9cdc06cec7051046218147840d50602b7105a49a8070c85db682d6305021b822cdc1866e58431000080550404be6c111321de982358c872e605b4271229808e8d8220628e33500a3b1214c083860a4310056982461d8b1a6e11e762abda8c40c08e84e010332
    | 6 => 0x34cd42822065b60278980a84c8420461a2381a11b8218d431a606ab3428f082361810e8e28913802dbb1320415d06681c304021b036c841db663bb270a3110df841400c0ba86036b998434d03516057eb317f9a8322c4988e4741762029c0ec0c06866a1bc306d718255ec84b8a0d34360139a84209c132480ba302aa718972d8062608102028eb82668c0ee2603a6372ca920400dc732442d6303
    | _ => 0
  fld w 21 (i % 64)

def S7 (x : Nat) := let c := c7 x; mv (mask 81) (c % 4096) (S8 (c/4096))

def i7 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x141e020a00034002f80c1c1d0002c5204008540c3c0300096010000412000082c0803009240220008ac0807470147a040000c00000c02800000c8800202010100c33118a42410
    | 1 => 0xa68c0620122c6d067c050c13a3c059bc024a000141600300d4105e5f09c00311780492120700080002b0140000090140600078280008088406a2b00098001517804624c0b82c1c00
    | 2 => 0x3204c0c03168041c14010042808bfbda1c238c0081ae8d6830c400
    | _ => 0
  fld w 9 (i % 64)

def c6 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x6a0813b4c064c682471034998102cc858a6072d3615a990814410f248400103a9189b14d821a68315361811904a2c495c6c2a4340af189bf4c0ab06a04436221981b7cc05a8ea50c303d0181234c16dc6079630157110da4d8552602c5102431a06c4d014e608b43022210328cc0f0a60377100bb880874c8d80602e5302059a0011d442c6c4343400e9b111ed09f4ea33db2123880824c53106020c3624e9918e0c054060abe713
    | 1 => 0x629a86c4d410a6289a302cc99291c413186050b32394db08689088e60568301251b0d59d41586059132019981000412c66c94a2322511093c403626c00d30402081ad4402626066330387980b90c0daa605281007d082478c0b406069e302121a9600c8564604c03046a081941d45c240d28b020e9a9454d462c20106302ac1a05a4980126a30e33176182385d8dea603b430347b01b04c0e706039d1004d9b06c4cc1a8208ff331
    | 2 => 0x94980d60d82166c5161045e98089cc0764602623010418256cc0c166c47930323d89350407686088536102081016c42686249a3408e9b9314d034c6214a3127d0812c88c828602a73246a32812c9848e200ac35086190e00c100b4406b302bb882484c06846059730323d81294d40f0681781007a190af8980c86847d302059982e4d875c60879320c41a0088c085a680051020b9816c4c40686c076303409814b4d46acea227b61
    | 3 => 0x126c3a03404898a490c0400202ec3016a082edcc06ac206fa75347180ca0413006067b25137180b50002de4601f261a5110400c0ab06040b350a1189910886ee66000100
    | _ => 0
  fld w 21 (i % 64)

def S6 (x : Nat) := let c := c6 x; mv (mask 81) (c % 4096) (S7 (c/4096))

def i6 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x2e140019191b19211d08002606340405020508170b0a0402010d01321b0501212a160008070c01110c00010e051b011c050b06030004070b0804110402000000
    | 1 => 0x1a1091206035a0d992b0000006b1e003108282c
    | _ => 0
  fld w 8 (i % 64)

def S : Nat → Nat → List Nat
  | 6 => S6
  | 7 => S7
  | 8 => S8
  | 9 => S9
  | _ => fun _ => []

def I : Nat → List Nat → Nat
  | 6, z => let h := hk z; (h/84 + i6 (h % 84)) % 218
  | 7, z => let h := hk z; (h/152 + i7 (h % 152)) % 443
  | 8, z => let h := hk z; (h/157 + i8 (h % 157)) % 453
  | _, _ => 0

def chk := mixCheck 81 6 S N I pool

theorem h0 : span (chk 0) 0 0 = true := rfl

theorem h1 : span (chk 1) 0 0 = true := rfl

theorem h2 : span (chk 2) 0 0 = true := rfl

theorem h3 : span (chk 3) 0 0 = true := rfl

theorem h4 : span (chk 4) 0 0 = true := rfl

theorem h5 : span (chk 5) 0 0 = true := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h6_0 : span (chk 6) 218 0 = true := by decide +kernel

theorem h6 : span (chk 6) 218 0 = true := by with_reducible exact h6_0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_0 : span (chk 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_256 : span (chk 7) 187 256 = true := by decide +kernel

theorem h7 : span (chk 7) 443 0 = true := by with_reducible exact (sj h7_0 h7_256)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_0 : span (chk 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_256 : span (chk 8) 197 256 = true := by decide +kernel

theorem h8 : span (chk 8) 453 0 = true := by with_reducible exact (sj h8_0 h8_256)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h9_0 : span (chk 9) 94 0 = true := by decide +kernel

theorem h9 : span (chk 9) 94 0 = true := by with_reducible exact h9_0

theorem allChecks : ∀ s ≤ 9, ∀ i < N s, mixCheck 81 6 S N I pool s i = true := by
  intro s hs
  interval_cases s
  · exact fun i hi => spOK h0 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h1 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h2 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h3 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h4 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h5 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h6 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h7 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h8 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h9 i (Nat.zero_le i) hi

theorem dead8 (i : Nat) (hi : i < 453) : ¬NatRun (mask 81) (goal 81) 8 (S8 i) :=
  mixAll allChecks 8 (by decide) i hi

theorem dead9 (i : Nat) (hi : i < 94) : ¬NatRun (mask 81) (goal 81) 9 (S9 i) :=
  mixAll allChecks 9 (by decide) i hi

theorem dead (i : Nat) (hi : i < 10) : ¬NatRun (mask 81) (goal 81) 9 (S9 i) := dead9 i (by omega)

def index9 (i : Nat) := fld 0x5c02600d17e7009200000fa8c07cce1af1a08a413d01a00512a01b21005401876008f680fc7bc32923098cb40597b92380a20003f4fe0c92dccb3804a28001441018040d030058efa41cbc8b47d200d8435ecaa7ce03eeb20fceefefd4066043400a1a298ddb9a0073 7 i
def index (s : Nat) (zs : List Nat) := if s = 9 then orbitLookup index9 0 40 (hk zs) else I s zs
theorem atDepth (s i : Nat) (hs : s=8 ∨ s=9) (hi : i < N s) : ¬NatRun (mask 81) (goal 81) s (S s i) := by
  rcases hs with rfl | rfl
  · exact dead8 i hi
  · exact dead9 i hi

end Fixed40


namespace Fixed41

def raw : List Nat := [0x560aeb5815933ac206d4f000003ff80001ffc000007,0xab5d41a82aa40d54bd4b9001ffc00000000001ffc38,0xacc118231330e118e098d2ffe000001ff8e000e000c0,0x310620c437470620eee304000000001fff0000ffff00,0xc21843085b87fbc3130020000000001fffffff000000,0xfc1f83f07c049c029c0200ffffffffe0000000000000]

def pool : List Nat := [0x108371345c16458,0xdc0a0686c16861,0x1082b028611746c,0x134420685d1645c,0xac1a0285c16059]

def word (i : Nat) := seedExpr raw (mask 88) (fld 0x707903c41e9ea1079fa67d2200602081081d9db4b7603afb38044d5af6681d3d99ed0f64400a0dcdda0367743b9100182cd166043022838b5680e100253c416809c068ea667a3aa100100041320b102323d414209105482b0000000 13 i)

def unpack (c : Nat) : List Nat := seedW raw word 6 c

def first (i : Nat) :=
  let w := match i/64 with
    | 0 => 0xc1307f85307f6d307f4d307fe1107fe1007fe0f07fe0a07fc0a07f84a07f6ca07f4ca07f2ca07f28a07fe0907fe0807fe0705fe0707fe0507fe0407fe0307fe0207fb8107de0107fd8107fd4107fcc107fc0107fb8107fb4107f80107f78107f6c107f68107f60107b60107f5c106f5c107f58107f50107f4c107f44107f40107f3c107f28107f24107f20107f1c107f1c105f14107f10107f0c107f08107f04107f03007f02107f01307f01b07f00b07f00a07f000e3f03807f00107f00007f
    | 1 => 0x38e3f038c3f0386ff0384ff0382bfe2e07de3807fe3607fe3507fe3307fe3007fc3007fe2e07fe2d07fe2007fe1e07fe1b07fc1b07f6db07fe1a07fe1807be1807fe1706fe1707fe1607fe1407fe1307f
    | _ => 0
  fld w 24 (i % 64)

def S9 (i : Nat) := unpack (first i)

def second (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x38241fc000907f000201ff8b8705d0381c17c0e0707f0301c1fc000707f0001c17c06c705fe181c16f85c704f0131c1fc04c705f00a1c1fc028705f0071c1fc01c705f038181fc000507fe0f101f00e0407f000101fc000307f000081fefb8107cba8041d40b8107d027041f6e601079b97041b4054107d00e041f4030107da170419c07c107b01d041ec070107b02c041bc0a4106f026041bea94106f024041bc08c106f022041bc0d0105f0320417c0c4105f000041fc0ac105f018041ec05c106f617041ac0481077d510415c034107b789041eae1c105d007041fc01c105f6070416d71c104f3c4041f250c106e
    | 1 => 0x38381f40e0c07de285c19c0e1f07b038741ec0e1c07b038b01bc0e2606f038901bc0e2306f038881bc0e3405f038c817c0e3105f000e01fc003607f000d41fc003307f000c01fc000007f000b81fc002d07f038801fc002007f000781fc001b07f000681fc0e1907f038601ec0c1807b000601ec001807f01b601fc061807b0385c1bc0c1706f0005c1bc001707f01b5c1bc06d707fe185c1ac05d706f000581fc001407f0004c1fc0a1307f0184c1ec05d306f000441fc001007f0383c1fc000f07f02e281f40a0a077038281fc0dca07f033281fc000a07f02f281fc0a0a07f018281ec060a07f017281bf878907a
    | 2 => 0xe1bfc00306ff00001bfc00386bf038e18ec003863b038c18ec003863f038618ec0e385ef000e17bc0e305ef000e17fc0e1b5ef0385d7bc00385bf000e14fc00384ff000c13fc00004ff038613ec0e174ef000e11fc003843f000e0ffc0e2e2bd038a0adc00382bf000c0afc00002bf00084afc001b2bf03860aec0e172af0004cafc0c0b2bf0002cafc000a2bf000e09fc003823f038e077c00381df000e07fc0e1b1df0384c77c0e0a1df0381c77c003817f000e04fc00380ff000e02ff8bee07ce2ea01d40e2e07d030b81f4002e07d02eb81f40e2707d02e841f40b9b07de2e601e78b9706d038541f40b9307d
    | 3 => 0x38e2ef40038bbd038c2ef40e2ebbd038ba1f40e2e6fd038b93f40038e3f000038fc0038dbf000e35fc0038cff000e30fc0030c3f000030fc000003f000e2efc0038b7f000e20fc00387bf
    | _ => 0
  fld w 30 (i % 64)

def D (i : Nat) := unpack (second i)

def N : Nat → Nat
  | 6 => 69
  | 7 => 226
  | 8 => 332
  | 9 => 91
  | _ => 0

def c8 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x8be0d408079805b4007ec80fcc8b19200e3407cc824408288203e532c6e401402c0812c3611c7040fd4c208184104056600394c0000005010a20c0441818830f1050085e03d9471a903f3110206b0e04072885b601e2071ad0000bf891042c6460441589c0c4b70002035440030818050301ea203994e88280e31042080027c072900f500f6e06c410072103506042074ed024da002100
    | 1 => 0x8820020415788200e6476629604157880461030089eb0dc407a900e63010de48d8aa8829635207e42c4d04ed902f1075a6e2bedc189b8a2282ae2055bdce35a805b508c20826c4220830050406a0a0f946cfa183e320b62012dc2ada800f205a68234d88024f87b60724a200e7c69a90016f07ec400ffd69c083e54376400f88407aa5a1020220e0f984028100f1007ea40017e5dc000b60
    | 2 => 0x820c12d804f9906b5089660c4d4d8dc0061020820e00afc000fafb1001e8512d4169a888b10b3c8600c401fa100f4013c8613dd2adb8001053a2063c41c011f83e318d6e01ad801f290210500d3f5440cd881afb400e20d68414008200e3200a0a0ad40788302b603620c7441007b18078f01e6946d0005a804b50737000c4097da803e6501ec40193c69c10810713e840c40ca12903e41
    | 3 => 0xab6c016dc1d9a887b10896c0c4d8407990110206a08004197db046b608d6214c85a694084b30746e356cc071b944b400e20e02c804f210610601ca800c7c2882d910204204014bd51a886107586a212c4091c103f41122060fd51391304b40522060adc03588003af0820a13dcc0080002ff005be0841c15a002b200162048d4c3082891050bee403c84408100b30022060003c028301104
    | 4 => 0x1e2080c416b0829b1051f640039854882d5b401a6e402d022081bb37101c8203d8407a09234200b1e039881880805ff766261c40a359809f43246e40d40c10830310410208bc40c07a980f6007e680fd441fb1af1068c20110412ad880e34207c68cee0035b803e42166a454dc80157804000e2062441807b235b8001c4222dc03882051020a20f1841625882f10507ec203cc41f3183e62
    | 5 => 0x536400d404026f801020067e0040ec882afb3007ecb46cc02fba44105
    | _ => 0
  fld w 19 (i % 64)

def S8 (x : Nat) := let c := c8 x; if c % 16 = 15 then D (c/16) else mv (mask 88) (c % 4096) (S9 (c/4096))

def i8 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x16034460e2780814002c008661f020000420018ec00000e0683e0f30008581d029189056020000801008b018260b04c06280301c0004040080c00000080c000381408030280c5c04
    | 1 => 0x606c041319bec064a169102008040f0580008c40007f0b09c08020000c6874000f41c003b0fc00791300c0620091708a040103804020002c04002b2103001019280245010680000
    | _ => 0
  fld w 9 (i % 64)

def c7 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0xa4081200d81ed662683012e1a82bbd445460c5c304461813c4c065ac2c9b30129980b20c055ca00273011a183024d815c2032923087910928d809a4412d102579b85184095a460eb3010c180abbd425ac240c36007183c0adcde84603cb704508313d8d1486c02910394181c60c04f46423022030918038c195dc80f6105461082bbd0878604aee4394908024d4170442aef530e121384c055c2065730110980ab941280460bb230
    | 1 => 0x36981266c04a6c4f3b30244182266d454868098350521b82bb9455660aaee1079180c188c11846509301968832e0c060860219b704cd98830d01184045130169104030d41426e01c20231918030c0d5de86a435096b0a180c095c2010b360a408251acc574684aee5431980c688c190442aee5057729b2c408e64412d10457718a84d0130609333601e1081b0c0574602991027f91845c8c1142088b23081b1a39cd81de440ef301
    | 2 => 0x9c108468c05726e52d103609810944155c20891b434418332c419824252d0001e101522c0596208aef10821183e48861e6026130135118274c066860288307572811c0c05e4440b22302e1b84b4415124604f2071b9b04c0d0c126e0aef2039988500c055e60aae40545931078c050a60298370449082e4d48126806c2302e190abbd495c20aa135006190870c08a64400e304259812b9406916c230301577a0030dc0684612b301
    | 3 => 0x182404af24087180ac4c066844072b7196b082b84087260234310439038f09086e60aa13600c908032dce9020d3823026980cc2dc60c6025c360331044ac8804e442aee5247981b14c055dea8df301570001e8881ec204bb210
    | _ => 0
  fld w 21 (i % 64)

def S7 (x : Nat) := let c := c7 x; mv (mask 88) (c % 4096) (S8 (c/4096))

def i7 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x2130400433213351005030a0a0013000c007f2b3a0d2b0626145c3f3f0700000667341102010d070110013301080804001701000106230700060b02000400
    | 1 => 0x129d8607051d026701050700490004104b090f001600004e1b3d5429
    | _ => 0
  fld w 8 (i % 64)

def c6 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x33210953016830173210aa301d93018c230572202d105be22075303ae30380210cd22049331da1018d1046ab63b72308d10174350623309b210a06344d303d42309a22062310a8230623604a220d3310623219d303d3b606235016301623403c301322616d220ae3024e230413018f31369350a02306e23133616ad2416a321033013b230ac22066b630c350302312d1013930305101a92108830384210c3102
    | 1 => 0x94303cf2102d103a630124251
    | _ => 0
  fld w 20 (i % 64)

def S6 (x : Nat) := let c := c6 x; mv (mask 88) (c % 4096) (S7 (c/4096))

def i6 (i : Nat) := fld 0x1271880b008164a0c040524f0531050cc0110030c00800010000c3 6 i

def S : Nat → Nat → List Nat
  | 6 => S6
  | 7 => S7
  | 8 => S8
  | 9 => S9
  | _ => fun _ => []

def I : Nat → List Nat → Nat
  | 6, z => let h := hk z; (h/36 + i6 (h % 36)) % 69
  | 7, z => let h := hk z; (h/92 + i7 (h % 92)) % 226
  | 8, z => let h := hk z; (h/128 + i8 (h % 128)) % 332
  | _, _ => 0

def chk := mixCheck 88 6 S N I pool

theorem h0 : span (chk 0) 0 0 = true := rfl

theorem h1 : span (chk 1) 0 0 = true := rfl

theorem h2 : span (chk 2) 0 0 = true := rfl

theorem h3 : span (chk 3) 0 0 = true := rfl

theorem h4 : span (chk 4) 0 0 = true := rfl

theorem h5 : span (chk 5) 0 0 = true := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h6_0 : span (chk 6) 69 0 = true := by decide +kernel

theorem h6 : span (chk 6) 69 0 = true := by with_reducible exact h6_0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_0 : span (chk 7) 226 0 = true := by decide +kernel

theorem h7 : span (chk 7) 226 0 = true := by with_reducible exact h7_0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_0 : span (chk 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_256 : span (chk 8) 76 256 = true := by decide +kernel

theorem h8 : span (chk 8) 332 0 = true := by with_reducible exact (sj h8_0 h8_256)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h9_0 : span (chk 9) 91 0 = true := by decide +kernel

theorem h9 : span (chk 9) 91 0 = true := by with_reducible exact h9_0

theorem allChecks : ∀ s ≤ 9, ∀ i < N s, mixCheck 88 6 S N I pool s i = true := by
  intro s hs
  interval_cases s
  · exact fun i hi => spOK h0 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h1 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h2 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h3 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h4 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h5 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h6 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h7 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h8 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h9 i (Nat.zero_le i) hi

theorem dead8 (i : Nat) (hi : i < 332) : ¬NatRun (mask 88) (goal 88) 8 (S8 i) :=
  mixAll allChecks 8 (by decide) i hi

theorem dead9 (i : Nat) (hi : i < 91) : ¬NatRun (mask 88) (goal 88) 9 (S9 i) :=
  mixAll allChecks 9 (by decide) i hi

theorem dead (i : Nat) (hi : i < 10) : ¬NatRun (mask 88) (goal 88) 9 (S9 i) := dead9 i (by omega)

def index9 (i : Nat) := fld 0x7086f58024014800a032008a0c6807c0110048033b2457638727638afec03d0045fc646dc3a44925bdd80c798add0000eae5af402fcc0b700038d651a20000d9ba704e5e6d713258ec28f08f744c56401288032b0ba5756803f09a76b2691b0002800 7 i
def index (s : Nat) (zs : List Nat) := if s = 9 then orbitLookup index9 0 38 (hk zs) else I s zs
theorem atDepth (s i : Nat) (hs : s=8 ∨ s=9) (hi : i < N s) : ¬NatRun (mask 88) (goal 88) s (S s i) := by
  rcases hs with rfl | rfl
  · exact dead8 i hi
  · exact dead9 i hi

end Fixed41


namespace Fixed0

def raw : List Nat := [0x560aeb5806c0dcbb00d81b2bc00000ffe000001ffc00000007,0x8b5941280965a815012ab5164007ff000000ffe000001ffc18,0xacc1182312d81302615b0261cbff8000007ff000000ffe00060,0x330660cc2720e41c85fc3f8e1000000000000000000ffffff80,0xc21843085bc3786f0e604c0400000000007ffffffff00000000,0xfc1f83f07c0380700b80700803ffffffff80000000000000000]

def pool : List Nat := [0x1402d0286f1b87a,0x16c50114671986a,0x16c150e07a1b86f]

def word (i : Nat) := seedExpr raw (mask 102) (fld 0x7cfa83d11420f5f5603c7d420f30797a6bd33e910036bb008204207672d75d60ebddaa2733d48b4ea265134880440756ad51c20e9ea30016a880b5d6e03737599da06cee841b5b91001eaaf4868b3021e78916a04507172681c3c99e237244009a9c068e66b533a46d566a875520029224b664832eb96e026a5eb946cd666ab3440018a2476a3ea046479a3c51eb1468a1c78a3d80a147a491a4872e9970c7a81235d105502a65571aa94e4688000000 13 i)

def unpack (c : Nat) : List Nat := seedW raw word 7 c

def first (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x50700fe88e01fce1c03fec3005fd8600ff7cc01fc01803fca3007f94600be00c017d89803fb13005f50600fea0c017ce1803f9c3005f30600fe60c017f61003f802007f50400fe70801fc81003fec1207f00240ff28481fdf8903fb11207f50240fe70481fc48903fec0e07f001c0fefc381fd40703f9c0e07f0e1c0ffb0301fef8603f800c07f94180fec4301fd40603f9c0c07f0c180ff40081df60103f800207fa0040ff3c081fe08103fb70207f6a040febc081fd40103fa20207f38040fe60081fcc0102f900207f12040fe1c081fc30103f810207f
    | 1 => 0x1400ef42801de84a03becd807f01b00fe00001ff65003f80a007fa1400ffb2781fc04f03fcf9e07fd9040fe02081fe0c103fec6e07f00dc0feddb81ff63503f806a07f6ad40ffb1781fc02f03faf5e07fa0a00efb1401ff42803f805007fbaa00ff6d401fec2803fd05007f9ea00ff31401fe52803fc65007f86a00ff05401fdfa803fb75007f6aa00febd401fd42803fec4407f00880ff29101fd42203fa24407fa0700efb0e01ff41c03f803807fba700ff6ce01fe81c03fcf3807f98700ff28e01fe41c03fc13807f6e700fed4e01fd89c03faf3807f
    | 2 => 0x1b286e0366cfc000d9f80d943f01b27fe03641fc06c6ff80d8d7f01b17fe03628fc04a51f807ea3f01b117e0361cfc04a39f806273f00a0e7e036187c06c31f80d843f01b04fe03607fc06c0dfeca0077
    | _ => 0
  fld w 27 (i % 64)

def S9 (i : Nat) := unpack (first i)

def second (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x981fc03b2607b0000901fc0002207f0140801dc0352007701948017c0002007f00608017c0001e07f0000701fc0181c05f0000681fc03b1a07b0000601fc0001607f0000501fc05d1207e00bc481f805c1207d00bc481f40501207700c8481dc0401207b01804817c0001207f00ec481ec0221207d00604817c0001007f0140381dc04f0e06f0000381fc0380e06f00603817c05d0c07e0130301f80500c0770130301bc0000c07f00ec301ec0380c06f00603017c0000a07f0000201fc0000607f0000101feed0020760168081dc0500207700d8081dc03202077019c0817c0650205f01880817c0600205f0000081fc0260207d8288081e6e980205ea0600815c0180205f76600816dc180204f
    | 1 => 0x174c017aeca3005ebac4c017aea83005ed940c015c05030077a140c015c05030057a128c015c06c3005f01a8c017c0683005f0198c017c0633005f0198c01fc05f3007f0000c01fc05d3005f016cc017c0503005f013cc017c04c3005f012cc017c04a3005f0000c017c0483005f0104c017f63b3005b00ecc016c03b3005fd8e0c013c0383005f00e0c013c0373005f00d4c017c0333005f00c4c017dc313004f00bcc017c02c3005fa0a0c015c0283005f76a0c016dc283004f0088c017c0203005fa070c015c01c3005f7670c016dc1c3004fba60c017a818300570060c017dd983005b7060c013c0642e07f0000b81fc0662c07f0000b01fc0682a07f0000a81fc04a2a07f0000a01fc0182805f
    | 2 => 0x1501fc0005207f0169401dc0505007700d9401dc0345007700c9401dec465007b0115401ec0425007b0101401ec0675005fd5994017c0655005f01854017c0605005f01ad401fc0005007f0141381dc0004e07f0001301f40434c07d00fd301f40004c07f0099301f40004a07f0001201fc0004607f0105101e60c1440790141101dc036440770119101ee5464407b0105101ec0624405f0001101fc0004207f0001001fc0003e07f0000f01fc0003a07f0140e01dc0363807700c8e01dc0573807bb118e01ec0453807b0108e01ec0403807b019ce017c0653805f0180e017c0003807f0178e01fc0263807d8288e01e4050360770000d81fc0003407f0000c81ff65d3005e0174c01faedd3005e
    | 3 => 0x119b81de5466e07701b1b01dc0006c0770129b01dc0506a07700dda81de5376a07701b1901dc000640770129901dc0326407701ab4017c06cce05f019f3817c000ce05fd9ab3017c06acc05f01b32817c065ca05f00032817c066c605f01931817c000c405f01b30017c060c005f00030017c000d807f0003481fc0000007f0002c81fc000ac07f0002a81fc000a807f0002981fc000a407f0002881fc000a007f0002781fc0009c07f0002681fc0008e07f0002201fc0008207f0001f01fc0007a07f0001e01fc0007407f0001c81fc0006e07f0161b81fc04c6e07f0001b01fc0006a07f0001981fc0006007f0141781dc0685e07f0001781fc05b5e07f0001701fc0005a07f0001601fc0005607f
    | 4 => 0x360afc06cba27e01b1789f806cb827d01b1789f406ca027701b1909dc06c8027b01b30097c000d827f0000009fc0009427f01b1d89ec0006227f0001409fc0003827f01b0c097c0001227f0003608fc06ca01f701b2787bc000d81ff0000007fc06c701ef0001407fc06c301df0000387fc06cba1be01b2606f806ca01b701b2606bc000d81bf0000006fc06c761bb01b1c06bc06c3019f0000306fc000d813f0003602ff65da00760176801daed0a0076bb41401d806ab607701b2d01dc000b407701b2801dc068a00770002801dc05da0077016e801dc053a0077014a801dc051a00770142801dc0509e0770142601dc05a940770142501dc05092077016a401dc050900770142081dc0506e077
    | 5 => 0x1b9cfc0006a73f000189cfc05050737000141cfc05d5073f012141cfc0003873f01b281bdc000d86ff000361afc000d867f01b2e987806cba63e01b28185c06ca063701b35187c06cd061f01b33187c06cc661f0003618fc06cba61f01b2d987c06ca061f01b27987c06c9861f01b25987c0009463f01b20987c06c7661b01b1d987c06c7060f01b1c187c06c6e61f01b1a987c06c6661f01b17987c06c5861f00fd4187c0315061f01b10187c000d85ff0003616fc000d857f0003614fc06c3051f0003613fc06c764fb0003612fc000d847f01b2810dc06c6a43701b32907c000d843f0000010fc0005043f0000e10fc06c3041f0000810fc000d83ff000360efc06c3039f000360cfc000d82ff
    | 6 => 0x3654fc000d94ff0003652fc000d947f0003650fc000d93ff000364dfc000d91ff0003644fc000d907f000363efc000d8f7f000363cfc000d8ebf0003637fc000d8dbf0003635fc00000d7f0003633fc000d8c3f01b282fdc000d8bff000362dfc000d8b3f000362bfc000d8abf0003629fc06ca0a370141fa8dc000d8a3f0000028fc000baa3f0002da8fc000b0a3f0002628fc00094a3f0002328fc04a8ca3f00021a8fc0007ea3f0001428fc06ca09f70003627fc06c869bd0003626fc000d897f0003624fc000d88ff01b20a2e4000d88bf0000022fc000948bf0001422fc000448bf0003621fc000d883f000361ffc000d87bf000361dfc000d873f000341cfc0000073f000281cfc0009e73f
    | 7 => 0x6cbb43601b355bdc000d96b701b3650dc000d943701b3450dc06cbb43701b2dd0dc06ca743701b2950dc06ca343701b2850dc06ca13f701b284cdc06ca127701b2d48dc06ca123701b2841dc06ca0df701b2337dc000d8db701b2835dc06c6ed770003632dc06cd5a1f00036677c06cd599f00036657c06ccd8df01b32637c000d989f00036607c000d9b3f000006cfc000d9a7f0000000fc000d967f0003656fc000d957f
    | _ => 0
  fld w 34 (i % 64)

def D (i : Nat) := unpack (second i)

def N : Nat → Nat
  | 7 => 2353
  | 8 => 1535
  | 9 => 152
  | _ => 0

def c8 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x8c102391021f3108c10124a729274294a6595f3487a51092108da7191e7086e438e10245b405310021b808410252b6193f658de15243515c2107f104223810150f85f6569b50293714ca4195f652a36262b1062a827ae536ca41253218b74386f4287b701fb7185a2091f7436b608b1061f10282a4044b801f104492210500030a522cb61841049165312b204a2108e1045bb8030b204fb2085675751017d615
    | 1 => 0x9310295f543aa417e1000033f051008510400cff8810630b60252247eb107a310341024db5171101008df8fb5061b8115321931007b1068ba705310397e0292b70443516cb7174a8100bdf32b5067b5157b707d71553a7130100821045da826578683e6589a7062b802710464a516cb4124b7109b807f10232a626c1006fa41293816f1009310464e7597f0552b807a103915036531053b408ef7258b705ea87
    | 2 => 0x8ee762a3103f310513100036f24381051046410630b402538143221101038d104012104d2101437288a403610078a45000bf83b404fb6157310786166fe750045f10b5060b80583108510219b517861469a4197104871064a2215c3106ff758475205b505038152b821810595e5390b4000def05b6010b4086e426f1014fb7153f752b3810d210821028aa408ff7622b829460290a4018b7182b708a10641310
    | 3 => 0x483108310283f724c10378a718650567b7181b70403106cb6272a71961068b1036cb604ab513c100003ff87a40911002ea4119b5083a4305b40162218df727da719250097f6281b3045371271022cb529710261371042105e6265b31352310623108bf7686e532c10792105313822c1060080f8d10297e5473b8072b7136f64017af8ea503e382831048f1044da518477091a4053b506cb72523213c1077f310
    | 4 => 0x621090b728410600d3f022100091f78b401f1066fe652c3710042f8e10615b80453210144f52b647b1037bb50682511f1070155f781035ab8018100817627a50500a9f0a2102135105b707db208810331310273416267615221391060e2108fa4091e7535b718ca508a10362b867510697e053410091f756cb706fb709460601bff365062338153b70014ef8bf7500e0f89101833506fb605272630b7091b73
    | 5 => 0x69b7153351223108df706fa713610481a304fb2186f6288b7012105361054c31092a7097f5297f6300fef75a718f10594a7000b4f941062cb4090b628b7708710135b706ca610151f612217bb40593104db4097e6581a5000c2f86e30841074f1055eb83901002c10089a407f10538b6100f2f811053cb5072e753828284b527af632e106572211c3108577286f648fb42937641d37271310312828c1067eb70
    | 6 => 0x751008de710191f821061fb509550518a715138191e6590a602737189103293101331064f753210001b5f65a87102100112f85672906039410334b708bf65009ef32b2075b5096103821075e22126a828374037100833408bb60916026410100e6f5eb80271071010487f7569241691004c10401e4f6568785106396748f6406910195103271067210172a618da502c10383e764f101843702cb5067a711fb63
    | 7 => 0x5631078310841039210032b705f31050b80383219750297e635d3108b3507f10092a608fb7091a703aa3101c9f18b7000e9f68b806cf6467a213910374b8069e7561b61861053332138b8275f7572e6583b7069f751fa511e221453244cb402eb411210301a9f353211732392e753ab318d1017871664b5088a702234272b7064a71856762c101353109710539b401e3107e7154822195f6339b414f3101f100
    | 8 => 0x75b609470643b8097f0478b7588b712ea718ce75841002a38185b501db8193a70391007f504801038337022361801058cf758f1007b10493762271012cb70831063eb805d72669a71243108310700b8f6332143b718cb71827632531097f02857737e1038ef7585b400141f35a828ea702cb418e10087a702736152381333108f240271007fb40651004ab405e77657a825531035b82856741d31082b632cb60
    | 9 => 0x9610401ccf53105033522138185f7581b6293e7569e659410400d2f67103626828377000d1f2eb31243218373285b606fe76341056532126b8200abf7210492e65433618ca71253611b3106431028361181018ff759110224b8291f640cb8082a507af6493f752935143b7075b7008b802b351223512a3512fb8037b207db717f10369b70043822710339a4163b806710578102673100cb70781044532688a71
    | 10 => 0x51068df756ca7152b605db823e3627d103233617ab5054b8094b7570b701810494b7045a51831001fb516210086e607fb601fb7050361301063822112b30383102ca413d3104a28244b8123310941028d10097f650044f97e0365b707ae648fa70971034fb105ea827d10591f62893107d31085b3078b4590f6485e75603617261500c8f91f7288f6453b4357b82721027a1008336094a454f1068d504000ff
    | 11 => 0x19af30b621f10170b80756158bb438577685a5065b8026361002102b37186e500a25219b417ae5493b702d3812bb8186f3034a72283518fe6586f2001b3f34b5257b8384b40907534cb4191e76847406c1065337161a8295f641fb606f10639b7071254402529010288a617ab602c33183f7585a406b31027b709210401b4f4fa510046f083628110085a600721000d8f6e31078b6518102233233410360321
    | 12 => 0x4c10000ecf83b329470325b812335183f766fb73433418b750616268110290a7034b7240b81656267810689614901054f1004fb507e1076022165b1057b734832182b50831035cb80273108650480106493612e105633132422132b628ab4000aaf2c34193e6501acf8b37053a510338260a8251b805eb827e1066026192f729210245b508610388b400db8094b4512106811042ea611f10391105926050113f
    | 13 => 0x283815331240b804fb400088f0006f86f458210369b6084a402e31053e758210086f5293605946048fe7557a7286f5383f6521361263813631095e545b31024b72975042735195e64365046ea7186e652e1036fb716a2517da21101004f10448b818b1059010658b8097e0400eef53b5183b5093602911062237175e753fb800f21012b5062b7094b651210084330213106fb6357b8097e424931036e6454361
    | 14 => 0x4fb6014310083827d1013010493f72181066f103562525136162b2100eff75e767ea715eb6092e7665b618010048b808fb5312b4032b520103f00f3f6710631b8084b602c1054d32189b400eb8083a502cb710089f0194f30b502c3616228258a8223b818ce657a10134107897145336131b82361026cb508f10212104321066fb406fb5044310533438ba5062b87721062635194653843400106f8cf728fb60
    | 15 => 0x12b705db6097f54531016c1034cb708ce7650b8139105463217e104243714fa7118a418375034a524cb7130b722537167b6159b801f1054fb707ae3481a405a1028476088a413710680104483714434185f727eb5012b60463105c22106b8000eaf66b8078b508b3028bf7038a826c1018be758bb50473104fb4163a822b310453817b10045b41781005fa8271b80332214a3210ab8080b5091b6386e648d615
    | 16 => 0x21b8185a302e10727b7130b42333822837187b7193e7610b6000baf5438155b803ab519750569a6143b81452102337172b4061b808ca61263108ff7210b70911038fe7695f538ab707731000b3f03b8086f43691067210067b206ab8067b5091e606121076b8001cef91f768b3434531027a71843604ca710048f9510118b417ff645262692106671000047f1810786102523613c10686f6522b802a34165b20
    | 17 => 0x756148fb430156f2632197f648210567b105fb801e3218b1005a3106131097e623977486e4580b7088b60032105310472f7590b60533107ae638be6578b603ab41163101eb80503133410484b706410072b506031081106613217210351b8100f4f7fe6485e7660b827d10001d7f8ab6064b7193e703c10469a5145387931052eb3035b803ab5062b6165b513a1003ab6134b20033724db5032b7234b500190f
    | 18 => 0x83a706c1026e101033628eb707e310051055035483f703210253b5386f636f1021531053102083235e31030310321076c10400f8f33b8024b808fa608650661b6001c1f28b8095e6556b8025b808b3602d3418f1065db804aa515037195e343e3217a105931067bb70632216f1046cb40361061810392b600098f1db8087e7518b408aa7075b736c31032b603ab71851050434278b706f3107db2158a7281b40
    | 19 => 0x7bb603ab208ee7581103911042ca7193b7353b710510387e6593604371045374524b70083721c321857747510362b5123b802eb5100a7f2eb602eb5065b714db41921038b1042eb6192f7569b408bb027e10595e6382b4038b803e37201caf2e10033282811078c61572b6067b6026b611632191f652a37137b50442216522175b400043f67b708fa504b21089b708cb7097e6092f76831057d104841053e354
    | 20 => 0x2eb400090f6528726b803e25186f40861048650224a829470265b508c10000b1f0189f82b201fa713c10586f3291b700193f72310293410192f52a828bb532b3212eb7100c0f0114f975038bf726fa6178a758650387a719510544321787147db708b7022e10445b515d6268a104301025c3214932189b10173108b1020437278b71901041eb81861063aa51213714ab506cb458b7606910364b705c3617db10
    | 21 => 0x5131385f76931032eb708fb4090b457a10205b208710491b45271058bb703610381a703122184a7084b305ca828f1038473001e5f93f76623212ea5191b4000f1f1831092f65671012ea314d2218b7458db707eb71543139010397f6086f5038382743107a5030154f6eb80122104d31035221881006fa5375e650096f7ab3054354313210835462b200032f683108a1004fb5134310926028567336b4081b50
    | 22 => 0x8be7691b60531060f260632304231032103543714331032a528ca7088b4101a7f5137183e7597f4235b7200f0f82a700187f01cdf6410478a65052105135245325101022c1047b10230b52946035b221622212bb8062b7163310353828de7591a602f31035a7258261003ef86f603c103915002eb106ff7483b60837602c31094a758ee657ab403eb81323104ab4132105352823010597e642d37167b2194704
    | 23 => 0x5107857758ff6585e655235437103951026910497f03751020174f87f70391044fa214a3103e310891003931005b3072e764a37100b7f4332150310101060b2107db5057b7290b706ea81851038da7086e409610262b508b6425231386e207510462b6091a530c210371056eb70301074b3106931089104881044c1063fb81753102c1020435215b817e6155810108210955030185f85b202d35165b60
    | _ => 0
  fld w 20 (i % 64)

def S8 (x : Nat) := let c := c8 x; if c % 16 = 15 then D (c/16) else mv (mask 102) (c % 4096) (S9 (c/4096))

def i8 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x180341500000a0b80000e0040b80080900a0000280a0160480580700c000160020000d40880100a0100000301001c1e00d01202c040000ec0000000300e0a8020041040100081000204c0c0030060701080000601c2780a
    | 1 => 0x300c03802200c0302405a06c08015030000000000580700080700000c008480060281500f0f200000003000004028030000003301f0080680003e0040901d80b08400c000390080000a81900002c0e80200409c04809
    | 2 => 0x2a23c0001601c0340000b00219008000032008008100120081b803000088070010001480301100005c0080301400c0080902e028008220780b80303c0140006000a00a00800028054060000000340480881301000005819
    | 3 => 0xcc0000003100c00c0081b0ca0040110b006000018642e40040102900c09c02032014044360231460003a80402625c0b00003a08805805000024070460000180182603609c1b0010000380781c0ee3d00081606e0002b805
    | 4 => 0x4e11c008150105e807000026004418d71f61a8020260020580801202c0100180a03c0040085b0a81480a80a00002c108192500c4a480702a000528160180041085014c07404806012110628000040000280a0080300b004
    | 5 => 0x74a18032210e00601381e2b800c0a80000201423024000cf01780b064000002d8062008060000080680d00101e0080300703c0012084327c0701d816020000090150060300006600200002022046034449810e000c1a807
    | 6 => 0x6c1a4028050001340300000008869c210d449c0080752c770b389b0180344781e80c0a40506b0e20f0000051d81c80e0011400017d842000000e601a00a169760080102740203200c0003800500003c0601b0205b061027
    | 7 => 0x6446527000002040018900180140801d0b65a00041201405c060c9084f140302e014070080102a600c3f8790022040013b2501a00098316e2300200d084010008d200402c0a801008001d50002b80006f80025a66c6d930
    | 8 => 0x1d20947a010
    | _ => 0
  fld w 11 (i % 64)

def c7 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x56ec0a6bc842e9118ad46051b36a0d93d8182189c59b70b3460726cd89915a8541a60932464e80dc1801bb330370b56eca9a2d81a491852b72132820cd8cdc293b1b83b340a5a40e734809917b23442322cec4134488526082b393138f0406c269c9060833221022184044d84158e1b83a222034e626e8c814607a8997372072680c55d16909b9d65a30727ecb150dda9f18811837085c6254e08c0b3198d743010b064750ccc29ed833d2383b696e4b78409c1ba11c9271
    | 1 => 0x5324409b6dc59f1084a0e602aa64060c4124d91091c3506386810f989d72313b9b104329ec0e20dc2755b8ab7b606cc5014adcc59b5b8b151004a2684a1381439882599220666c4ab1adc00899839ab726c94875c8d82d588020c6103686422508c16598821d6066d86e6adc402a8909194102338c2cc88d4284882b223403206109d0c04ac10c1d724098cc0e5c8402601994e0b717456e48e881e579085b637080c20872cc10c188322c20854c4214a0d96421010a3250
    | 2 => 0x628660868886859104061050ee4631bcc0a49db1b15102645ccaa8cdc8c9110a72351a82c0abacd0170990d2a342b6040a724dc65a9a821c230338c4cc26dc8607a91941009c068630380aaa0812d41020626042fcc84b49a1569270645ec15ccc0647d2123c205bd36e0a7cc4e507b2be1b7367d6a0d80dc07c11018b1052626c1548c06c3180bf430140842f5589d8539c034f30185e4076fcc16a23085ad35008c20d5d88c02e9b8052302190402360c4cb5da8904100
    | 3 => 0x7a6602ca6dc4c5b0a42db71a56e09039841b25b0bdc31031e64e324d84d21820e7224209ec13f4e028c118c3962754064a831d029e1b92e93503936c0c2ce1c2e9b05731054aa6a4b7840e7011029810533ae64590cc02c1a80b6b015986c05cc414e3188406620207608bccc85e03a844a20205e6c4a10400119b90e2301816680554d411d119336354940c2a434881109b8a2f6144084108dc81a84b1348fb4276a502e20d80c1b0ab7d2523db6843cc880e3938241372
    | 4 => 0x31620c303d4c9b0813e0240b0a6a1260409551b930925239ac47184c065c5b8818a02a086029e8820871814616244806a0e80d401e100aa3a520306057f0a00df189c112103504e67bcdc11d529062b102e7460876d899159800b302240443668c16aa081869370be6462554dc0dc9a801860666c440af4c0c711b85b7330058500830408518801cd3024d0206384d89803120333702046cb051c4cb5d880e7343848c6eee8e05a519931c360b126cb3788c2a0b81ab5207
    | 5 => 0xb59484b94dcc1e5380af370ad86830e080a0b11054410429a460e20cc2d7082994b02b59684e6c415c9f82994103a0b6e941cd8a6318926c3085626a0736952d01b04023724d8642d80d42699189fe102aacc2e408a029b9b98b53408c66e45aed86f99989916144c3460830400c818995c24346e40e30140a5c5b95b23014106049f4c8c60728a9f301238680c8ad81ee11036c280734e476bbd15a93139a4b60324602833d82f5990b82b50b7c4e018ac80b190828a203
    | 6 => 0xa684034049506cd88451230a12206e80d82b35a80373205484204c0c08ca7328a92106866c1504840607825ba2508b36c07c088262990a68b501564296fcdd9041015bf24041fcc0a11018d99b037bb7008c204790412341a8364f65b5e5001bed41a3b083d66163ca460c5440c731832d410344a4c46758584910a0023608fa42030390a99d905f027173a44065cc098ab09b30302322ec4fc8d005a9b056e3023ba6e0e16dc43b121b223100ec4209fc8426818097ef60
    | 7 => 0x846c4af28e1e49081c3732121840866cd82d49a824936234e6ec6f8c0e3f10917f2050226a0d508599b1b8884220b406e0fd2dca451019d333108842146189e8e08144a302828626e6ad44c8b0b1e6380340606e50d8ab9883251b71b10c21468810751a9173a409d46c2d90412ed5b88eeb7029e7014d29c291198b9ab0134e5010d6dc1161218c05036666067d18589f31a835b032d6200d92c06909b2cdf30180b6e2906d46418804dc2034d06203f8d84c8a018c0402
    | 8 => 0x12c668d4a986f7180d4a334ae0440a28dc58111054160234e481270d40189994aa332af220b680d429eb839f1205b62626adc409ac189d8e36182220b283c14c18813a3b41a836c118181d10980d7ab745c26101e0dda939182bab7126c206ce8c8de8b138562030d06c55d88541a9815abf450ae640832c08b49815b9231bd26205e4d010608180c3036f6621053d84ee9985b930118e6e166c81cc6b13de921084a642651d82751b8c0b3346e868a5f8400ee1b829d310
    | 9 => 0x230700cb4c8588103d2c6177ce680174c0dba18a5bd3624fc40d594401131b0c3a3012d6eed234c0e1f1101cb30538e404833994af183b22721a72c4011840e961b8507b72118410680e0eaf9015ee31260e4608a08157611839a6764e4c407d3d8016918ce037118e6c16afd4d9c9c1d65b208fac2c62c4081294047423030c604c89d808b1905343014b6406a139801a981ba63038dee2a398c5ed3991ad22083296874b0d82a20813f93215af6e4413982de991c9b323
    | 10 => 0xa04e0e831d82b9db08c0f031484071a0cd4cd9a033030462cc2e7d0400c2981a33625348440748c04b5b0987e63666cc4ecf8c41c138a5746255302061cf88e7c9013243614b266073cc82e15b8de32800186e03039053c1c0268734316c211b8d86941c1b3722385a602d90000de110509104b004095cc412b11b81d43802e6200d90418649a8b227303ae486ca4c044b1b9b332209d46a29a0408e4db0b64b51ae46a0788861c1b0b37e1034c3ca8c5584281303194f54
    | 11 => 0x266272e0dcaab1083b0321748684ea089e631012dc207a08626360cd6a619200c3603d06034258911c1c02b7103b56a00f01c82961a8315b5320e410f48c4d065a1d1f3709d56e14e4411581028223608bc4a0820cc9911b01e82714974a4c8ad01c48805ad2209706023ccd8505081983103bfa40ecbc88534732268e5433ac211bcc8c2d9100c0f01a56c0296081c089105f81052824a56d8c0d4c3102deb532d6e26906d0a369a91836139e4664a13d943b9909acf43
    | 12 => 0x827480833d52ec9b854170263020163adc551da920cf628ae642e6c418a69b95b636098e64643ed49b41b0256372b12706df9cd1f91a81ca20436a20af469850e9013c0330ae76a341480e9092050cb42ae76622bcd80099b0b891040726a09a0404f6da908f3035986606ac8c1c2980b64105b406874f6c1eed1808113706886652d4d8cd608202b3403fa602189dcc701b991e1002606869a0414af190a61103b6c6082bed800d921a7e62567a68528cc12b611052ba32
    | 13 => 0xa086c2360e0c34981c3a20109260b6ac84039880040314a66420408dcd347b052b7013224215ac8806c9388af32038e605044412999884e43519a04436ac41090118c0b330578648303c86759098c0f32bf56e2647d4e7d9101a2220b57e867d0840a718288f37080050e828415a51418c0f42704620d9040a9588041161031620704ed0153138be5371b7e6263a0dc1347b2d65b406c96430d4c4039880b64f61644661014c050a1c04ce3707ac4216b84110819029a360
    | 14 => 0x328ea0fe4c2104141a513017ac207596d460a3b0dab6167996a2b54c8230100c116154426c26d989693db14c72027a244126edc92c9b812025220c420ae8c05d610208f36056f4c122c88191528152625076606c01896b9881a68f642f26a10b8c50b5da81cd254aca20b49cd427b1981bb302b186e0647d0c19981ad724282820141189df6db888836082c42e3b8848c79908c43234c220d3b0dc8c69103a9715340630d1d85871192876303b1420546088060701991f32
    | 15 => 0x104440690892839b9293a6070620014c81158998393e0526c2003e1890db1984a437284244ebecd00d6283411106af4404574dc149b01cc13417ace680ccd81d4989ad3100b2e7015e440ab89b03e0343abac4e7a8c9517882ca123582820950cd811b902069360a427068d0c0975313c133142ab6a0d0ccc0e43135df3204d020d18589520980d2736233a200a38e01cd581d2c3430de620f9cd42605b8a0d31039a000478412671b046f2020b2604ff0815759a809f350
    | 16 => 0x4dc4802bed881ad812d53406c8207598c429d110d66217746602e158969418c11ee6413cc4cfc8dc1d41bb0152030f048273581860700d2be547f4604e6c408325a14b135236a20c69cc8e961081a4a609366a9678e0ade9aa35136062ac29595d44d4181cfd305940c211a0cc1db5b8888370aff6e272cc1882900d4f380752628e50c0a8b1c38fe3516ac40634cd0966b0b8a9230bf4c6b048dc1cd110cba105a546e50aadc2d5b0a5a0230aca2071bcc488f9b8dabf32
    | 17 => 0x4fa604478415a71c00c04034c220359441a95d28194b0368e2003a0d00d99a018a30235942ae16dc9a03139b5104418ea13a8c40f2310a3a20297c4435e98dd5f102318104b5620a168c106e1c0504b718c06034e0cc4df1820d9230645642504c84dd9014762050b0607151894e431019140480c20631ca1e549b11853132266036ad011c19082cc35082200141cd4ac810242e3766136c528cc1ad21813162103a440223cc40ce88207e270b486849bedd62a382985321
    | 18 => 0x1808001b480dc9880502b6206acec6e2c05b2732a372106c66c0550416d70830e63047e9405638dc4dc9a017c20327a682e52d49b89a048632719044035c900d608302d30215262064541ac29b85b3617ae8440f59019849020932042504023014162a181889220b57ec6f3c9423f18a4ba10639ae0f7ece0025110255332a8220a058d81b273053036033a80d7c0842b9d809f93024d860a6c48200c902d65b308266ed7428c29b9c011c370780ee0464d41b01b04be301
    | 19 => 0x69c60b7b8806a8900dbf3217a466a90690a51990b243515626e06b3c4d0630b424636204606028d067ab13ca0e05b5740d5b0dc4cef325e9b506c966247bd91bf7b24111026de701408c09a11880bf30503c631654c8df0980dae103a1c6a28bc419bb90153db020d0647410d5130d2029a3703b86a14f6c122a1821acb6568ec2b6c4e01c1b084d6b7032a410a048c1859991361063062005d04158498138910299c4872fcdc0fa203530330181e054ac40efc08152c230
    | 20 => 0x181ca0478419f698098234282c6ec832c0c0d1920a9b6210c7077e8c04e39b80ee360b184608bc411bc1101036064806e0677d94b6312d88101a5620cd60c052018251f3050b24114108821a9288e83308dc6e2e6c400ce882a2f610358202d70c58c888210e6067f840d63989c341a95d0a405ba604dd0e00d6082d2b23232340a0d6c5eccb12235627474624e6c40da9db8be737033bca853cc16c71a8b94b7245ec2c358d09a95b8b6bb7244c602d0cd40e6db9347210
    | 21 => 0xafe603050406d69981853832b4682644416a1921a41a528d6c4aa94dc2d018146335234e606d98c4e41882cc03016dc68142588517b0ad623139366e55c8d01c188233a22143a4850648c0bc109d027061886a898440114103c6720663020a31589ea08801cd2102cc40359440481db8183614256c2e5e4dc2a0883043362042c6cd93d89b1b1b0c050487e6c67a088550190dad360700c4f70989dcd3b99ea2046fa4c7004c062030bbd661037ac2eb84c15b431b241362
    | 22 => 0x54a6c067189cb5988035b0550460264440088120056307181ca4b53d151214050cb5259a4214e58843c1099f4610822c26ed8c06ec918322104180206f86dc4b590850122022d6e15bd89deb7b2002370359c8637d89ad5f1906fa51644200d9040694b0bca010004c6274d1814c79104542206136c05ae946fd92029530133bec843084039a8122f61281e621016c04701b1991b6572620ace0c09f8db8a81302b5620c36599520da95283736cc6e6f48e00ae9a806fb51
    | 23 => 0x7356c35e88c024110c762064ec44037d882815b92986247e9605044400ce88322f00070b6a31d2dc1f3180991752bb66a00d4c16d5b0a9cd6540f2441284dca701a8c673209d4626cc0c4cda88158c3051ac6047b4809e519a1373504aa6052d4cd21e5a11c8105a04c0e574d01c488191ea038c2440303d41bd920a9d287181e835cc405b27a8191e32181c09270dc130d28411103482442cbcc065d0810563081ce682eccc14ea182de824036c440f46dc4d6330b08265
    | 24 => 0x23a6a16fce0cc8fa14a0105706c2b594409b6189d433703c820a300415f1980a56362181e62534d88aa081b1521075a464478409bb1b858b3507f84e076cdca9618115023010a440b80dc460718991e422aa68150cd02f39b83743769b76e34ac4041599803330503c60827cdc2821b8b83105b57c8462d8583f91049c36021e6066d4402c0902ab02076e0c4e675852a0b82dbd3021e66a36b18508318809a2212b2603288cc853982a6d627b94664ce8c046e181166301
    | 25 => 0x99c6a12484161b982b54227645ca8b784160a203284f050b2702a6189828082062b706fdec0db0c8d91732544710b56001234d0dbb9293a9714508c20a94d02f51033802201800016b840860719377606240642f02dc12a921502703a3e6092818584b1b2a61b40323c875d88096c1825096203494e076484c32103b8237115e440dacdc8cc101c402100e7e46f00c81d49bb5abe434d1ccb2b9c4236104105301428608820dc8c8b301911066b2407511c4e95b025abf42
    | 26 => 0x16a6e0e27d91a11281361043c4707448809c138a9183056886e5544c05c98825303505d8442ab8a0860082376360706c24c8c98a41a800e2b4141fec00d4c5ee8082a472033586cb059896091b0383614410485471842091a8377b700dc4a0dacd4a0a90423d23245e204d91ccaf5982dc2220181ea93d4880fa73029b30233b406f5a80ad77b24141039f246165cc4cee9a80af34076060a440884b5d138f862521cc04ceadc5061081b735037c642de0c84d60810d9671
    | 27 => 0x4a8eeb4ac408d25b802034272220b4f6c041719888635480ac4075d85d913a8268f5406270f7a6d463a1881316174976a6364842951b11193701cc60a414d85bddb8b221033902069ecd4857d3115a30173560ee0c404c88003831065262016d080a3a10812b210a5242150440de91bb5e2207b186083f4dcd47992a0d27145e200b604087b920b221050f0424c604198a1b00fd3831a66057d8815c9fb0064b52b3444954c840da881c05720b7cc4ea3c80dd3119241376
    | 28 => 0x7e26e3264909f8b13a3b207134411564c06bb31bc54704bf66466b8c21427b031510567d6809f885e59980d2a2214dc6a5474c0a8491059a3401be208c60408600808c73025784610198859c101db63155cec2f6ac40a95a805802204ee6a0644d96fc30839ab217adec0f48901569185d0b311b06ecae4c048f081cb835272840442cc09fc982b09a62475685678d88e6b1299176507e4632e840ec29824762701c46e631488281101543350a7b6e2735c19dd101a54202
    | 29 => 0x9da5068bc40cd6081a1720864e6e6f50c12e9180d7035045040c8bd84eeb118414f645bc20c301405bb1a01a82036454c02dcc0e95b1954f35094020933adc9c9ba2b302879404215969006c120548310026603520c900a381201230842620504886ea180c4a210b526c0dfacc8fd9819e0350114486647d50ccda0026220ade4414dcc10c1b0b1911023cc60a028c0492db8141241bb2643283d81321815abf647e26a2964d41e29383442038e96a0df8400ce8814a2263
    | 30 => 0x1fa6a35ced058b9a80afa72ad86c2653991d39809ca20346c602c8bd94d678a5392203164207d39410608248d38051c60a8d48803b910d5410539ae86af0d95b61819fea3436e6e0e0c0004c9a1322000896406578c1a341bb5672033366e01ac841b81102a0220329ca92fcd81b25a0b5d627181c8672881d369101a42106c9ca14a0cd27d1a859962518080ae169cac090a0c73500266a860c840c5b0ac145000806104f4c06ba9b13221064982092fcd40511101cd607
    | 31 => 0x6e860a38ad45b7982cc2301a304831249c591519191613348640cb8c08479202dc6363ad6c120c4089819ad5410400460af584002f18141b262764627610c04ff9884fa370b0a6075b0c04799899cd7533c460487880c49109835b0607848291ccc94230b3ee3023e0608e0c408c8f818333217ad664653d94fa7a858f6272fdcc0060808b5db81af6175626c0f30c966390936630373560c650415331a84db3012bc60a6ccdc0ce1104573051fe42067440d8490109f360
    | 32 => 0x47060ae6ac08b5d98509106181ca6a50dc6fc30998c30470568047c840221881de27492420d6dc8412a9b910c2037e96e37d8885a7db8b743043a56e0c54419cb9a82de1043222065d880a8f9b02d8b71b52681430c0a503a2c74615612624db8c0ab21405416040866477388869b9819a0304180204c6040edc3138a73704a36e4735c0cb580042c102b562076c4c154c08248430656040c068c056010209e620322c215cec86da99047621088c66371ccc5d498ab9ab05
    | 33 => 0x5884e1624cd1a2182374384526206309994cef32b151044f060a60c4158c3a143cb522074e0c544054390416bb203a54e061cc80ef104092212419cc928d8d9201815973400726c0c884056f3a2c31331aea604c98812941819e12085986e0b5041ad95b8d0262320466974040695faa0357066b4602e15c96d75b28e72041526a010cd488272839ab6262ac2d3e8d02c49b9dbf335419ca8d7881e9b9c1a41b410a44268ac8425b9b0a3931313648112cc0e35938543b71
    | 34 => 0x678408fea948f831296bb60209ea08d6dc58ab0a87bb706e64215504198ab09237203942664538c1270313ae721065a440e44410a49881102085006ec8d6d811e11085e201b5ceca4ca90a4e198393e60706c26918c062a182d1633447a6a56448407119220cf65323e08970820011823143707e9602464d8173b0b20c10521d6e91d0d814a101998232180808735c9951da88c0e543ae420408c4d99101d2b60371a6035ad89667198464332822c284c4841349c1b93102
    | 35 => 0x328e8100c80ed89c1aeb360a054a56aed9631db9322a406c82015c0dc14f90085a318780e603010069e983a6c3071b86e328040ad7080a2b3043162081184152f139c5e31084a60a614c144b1c1ade1003b8641418dc9941439c72103726c0f48c0d555b9521331b186c0538c0d56990db5220498206c89d00ff920df93010c544cfead4a619b0bd230576e44328101a1091c0553621fa6c7190c0a08b0b0f5100b6260749cc911ab13528304a88202e0c40c321810e7304
    | 36 => 0x2e13077104415984063eb0bb9d6274bc410e24c8df21811ca206b3862104cc4efb9015746249c4411018881a4938076203b7e6068318500c18920f10097064904cc412b9045703406866e07148141f9109a7335bf66a0030d41701b0dfa3247ae42130cc043c1882a9301108c4e9e8886689401cd2249964ecb60c045d9b088f350a8a40a9a2cc00c5b1380205
    | _ => 0
  fld w 23 (i % 64)

def S7 (x : Nat) := let c := c7 x; mv (mask 102) (c % 4096) (S8 (c/4096))

def i7 (i : Nat) :=
  let w := match i/64 with
    | 0 => 0x801602604101100200200000000200100100000000002400a00000c00004803800e00604500102200201100000700e01400f00700000f00200000400003e00200304700100000001505803404b00100a01900100600201700001c001017001
    | 1 => 0x3600001a03902f00202100301800201801801c02601600409902600600000400100000200000001f00700c00300d00900000102800c08008806d00100000000a04602d00001900003600d00f00402600200600300200100000000100a003012
    | 2 => 0x4800100705400001f0090fe00900400601b00100501000900000800300200400303b06b00200a03100004e00300d00002200600400000100000300e00600f06600000d0090b300600600a0b302d000036000003002008003005000004022026
    | 3 => 0x30400230150af01700001202000200200500101d00003800709200000c02a00000004f00002200000000002000b00503c00004800e07a00600400d00802100600200200f01301000600000600a00706400900e00700000005600d020000
    | 4 => 0x8e04300b06200000300000a00001f0010bc00f00601900200a00008300d01517302a00a04b00400000a00100000100100600205a00002e00f0041b000500000802101d00101100500000102c00204d00702f01813b03c00200a00b002017
    | 5 => 0x30000d300100000000105e00001700000900000207101902600300000100e00405600900000502400107600001907900100200000905700200700300701f00309400100000605118104300102200106100302400001b004005000002000007
    | 6 => 0xe00000401000300a03a06a00002c00004729100401d00608202702a00401001503400700802700301c00000300f0020c601700800400001906e00100000802200900000901100f02f00000000d01e00e00400d06900102b08400e011019038
    | 7 => 0xa50720150060e700500702407f02c00508800a05c00d12c0032b72740ef00000203202f0040a900702e01804d01402c06105000204101a04f02000004c03100200301d05801c0700d901303a04601500000002200202001e02f02c0130520cb
    | 8 => 0x1601100102a1af0091940ef01001e02002f19629202605a01a00d00100517e00201028e00300200702900f01b02214a02a08700e0000e31290130020230000140020330e802000f03502300000103400401900e0001f308401d00b016000
    | 9 => 0x1911c00000500900600000f00000c01a0940b200201516b04501203e02900000200100200000a00000000200007902a00304200600907602900f0030560290072b501500f0110740a602c00005c03407200110c12206e02300f01500201f040
    | 10 => 0x4000303b02f00000200200f0474b200e01408903403904b00600003102201400000585c00100412a00900800b02800000001408c0af00e0020590000730580142350ed00101300105c02b01800015200a11401700200000505d08414e01c
    | 11 => 0x8a000f00529010c00700300508503c6cb04304521e06e00701000305509e1102360410030e06f70b102b0aa00e03705d0000d13ad00210500001154e0dc87c6270c801701516e02a7f500800107900500001f01870a08f502200051017002138
    | 12 => 0x404006f58c32f03606b00004b0ae05000300009b30a03815e
    | _ => 0
  fld w 12 (i % 64)

def S : Nat → Nat → List Nat
  | 7 => S7
  | 8 => S8
  | 9 => S9
  | _ => fun _ => []

def I : Nat → List Nat → Nat
  | 7, z => let h := hk z; (h/785 + i7 (h % 785)) % 2353
  | 8, z => let h := hk z; (h/516 + i8 (h % 516)) % 1535
  | _, _ => 0

def chk := mixCheck 102 7 S N I pool

theorem h0 : span (chk 0) 0 0 = true := rfl

theorem h1 : span (chk 1) 0 0 = true := rfl

theorem h2 : span (chk 2) 0 0 = true := rfl

theorem h3 : span (chk 3) 0 0 = true := rfl

theorem h4 : span (chk 4) 0 0 = true := rfl

theorem h5 : span (chk 5) 0 0 = true := rfl

theorem h6 : span (chk 6) 0 0 = true := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_0 : span (chk 7) 128 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_128 : span (chk 7) 128 128 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_256 : span (chk 7) 128 256 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_384 : span (chk 7) 128 384 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_512 : span (chk 7) 128 512 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_640 : span (chk 7) 128 640 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_768 : span (chk 7) 128 768 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_896 : span (chk 7) 128 896 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_1024 : span (chk 7) 128 1024 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_1152 : span (chk 7) 128 1152 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_1280 : span (chk 7) 128 1280 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_1408 : span (chk 7) 128 1408 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_1536 : span (chk 7) 128 1536 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_1664 : span (chk 7) 128 1664 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_1792 : span (chk 7) 128 1792 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_1920 : span (chk 7) 128 1920 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_2048 : span (chk 7) 128 2048 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_2176 : span (chk 7) 128 2176 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h7_2304 : span (chk 7) 49 2304 = true := by decide +kernel

theorem h7 : span (chk 7) 2353 0 = true := by with_reducible exact (sj (sj (sj (sj h7_0 h7_128) (sj h7_256 h7_384)) (sj (sj h7_512 h7_640) (sj h7_768 (sj h7_896 h7_1024)))) (sj (sj (sj h7_1152 h7_1280) (sj h7_1408 (sj h7_1536 h7_1664))) (sj (sj h7_1792 h7_1920) (sj h7_2048 (sj h7_2176 h7_2304)))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_0 : span (chk 8) 128 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_128 : span (chk 8) 128 128 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_256 : span (chk 8) 128 256 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_384 : span (chk 8) 128 384 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_512 : span (chk 8) 128 512 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_640 : span (chk 8) 128 640 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_768 : span (chk 8) 128 768 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_896 : span (chk 8) 128 896 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_1024 : span (chk 8) 128 1024 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_1152 : span (chk 8) 128 1152 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_1280 : span (chk 8) 128 1280 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h8_1408 : span (chk 8) 127 1408 = true := by decide +kernel

theorem h8 : span (chk 8) 1535 0 = true := by with_reducible exact (sj (sj (sj h8_0 (sj h8_128 h8_256)) (sj h8_384 (sj h8_512 h8_640))) (sj (sj h8_768 (sj h8_896 h8_1024)) (sj h8_1152 (sj h8_1280 h8_1408))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h9_0 : span (chk 9) 128 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem h9_128 : span (chk 9) 24 128 = true := by decide +kernel

theorem h9 : span (chk 9) 152 0 = true := by with_reducible exact (sj h9_0 h9_128)

theorem allChecks : ∀ s ≤ 9, ∀ i < N s, mixCheck 102 7 S N I pool s i = true := by
  intro s hs
  interval_cases s
  · exact fun i hi => spOK h0 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h1 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h2 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h3 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h4 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h5 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h6 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h7 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h8 i (Nat.zero_le i) hi
  · exact fun i hi => spOK h9 i (Nat.zero_le i) hi

theorem dead8 (i : Nat) (hi : i < 1535) : ¬NatRun (mask 102) (goal 102) 8 (S8 i) :=
  mixAll allChecks 8 (by decide) i hi

theorem dead9 (i : Nat) (hi : i < 152) : ¬NatRun (mask 102) (goal 102) 9 (S9 i) :=
  mixAll allChecks 9 (by decide) i hi

def index9 (i : Nat) := fld 0x741989a71600200d005300e225d5dfec0032000009570c0024e7b2311fcb184a0000c15f00c92fcf7a746d00231024c440163e0000003c0c07a82b520f966300f200d65caa4afa68db91000072007fe5f4f5f64b00190066e9f862a499f4b7e62aa5062c008419bfeef70067f16222f7870000000e1350ae74d23000bed86f008d8104c81deb3d84bc003effc171183124399d9d312fca477b65a54e2200456f540500c084007e89006e00948a5ed2ca00732e0084150055abc77e00007ca100 8 i
def index (s : Nat) (zs : List Nat) := if s = 9 then orbitLookup index9 0 64 (hk zs) else I s zs
theorem atDepth (s i : Nat) (hs : s=8 ∨ s=9) (hi : i < N s) : ¬NatRun (mask 102) (goal 102) s (S s i) := by
  rcases hs with rfl | rfl
  · exact dead8 i hi
  · exact dead9 i hi

end Fixed0



def projOk (k l : Nat) (r ws zs : List Nat) : Bool :=
  ((pickRows r (mask k) == mask l) && (pickRows r (goal k) == goal l)) && (ws.map (pickRows r)).isPerm zs

theorem projOk_dead {k l s : Nat} {r ws zs : List Nat}
    (ok : projOk k l r ws zs = true) (dead : ¬NatRun (mask l) (goal l) s zs) : ¬NatRun (mask k) (goal k) s ws := by
  intro h
  simp only [projOk, Bool.and_eq_true, beq_iff_eq] at ok
  have q := transport h r
  rw [ok.1.1, ok.1.2] at q
  exact dead (Run.perm (List.isPerm_iff.mp ok.2) q)

def mkProjection (table col : Nat) (width : Nat) (v : Nat) :=
  let a := (List.range 7).foldl (fun r j => r ||| (((if fld col 3 j = 7 then 1 else (v >>> fld col 3 j) &&& 1)) <<< j)) 0
  fld table width a

def projHit (I : List Nat → Nat) (N : Nat) (S : Nat → List Nat) (r ws : List Nat) : Bool :=
  let zs := ws.map (pickRows r)
  let i := I zs
  decide (i<N) && zs.isPerm (S i)

theorem projHitDead {s k l : Nat} {r ws : List Nat} {I N S}
    (hm : pickRows r (mask k) = mask l) (hy : pickRows r (goal k) = goal l)
    (ok : projHit I N S r ws = true) (dead : ∀ i, i<N → ¬NatRun (mask l) (goal l) s (S i)) :
    ¬NatRun (mask k) (goal k) s ws := by
  intro h
  have q := transport h r
  rw [hm,hy] at q
  simp only [projHit,Bool.and_eq_true,decide_eq_true_eq] at ok
  exact dead _ ok.1 (Run.perm (List.isPerm_iff.mp ok.2) q)
abbrev validCross (k l : Nat) (xs r : List Nat) (y : Fin 8 → Nat) :=
  pickRows r (mask k) = mask l ∧ pickRows r (goal k) = goal l ∧ ∀ i : Fin 8, pickRows r (xs.getD i 0) = y i

def crossWord (m n : Nat) (x y : Fin 8 → Nat) (r : List Nat) (book : Nat → Nat) (w : Nat) :=
  let c := book w
  if exprB m x c = w then exprB n y c else pickRows r w

def crossHit (k l : Nat) (xs r : List Nat) (y : Fin 8 → Nat) (book : Nat → Nat)
    (I : List Nat → Nat) (N : Nat) (S : Nat → List Nat) (ws : List Nat) : Bool :=
  let zs := ws.map (crossWord (mask k) (mask l) (fun i => xs.getD i 0) y r book)
  let i := I zs
  decide (i<N) && zs.isPerm (S i)

theorem crossHitDead {k l s xs r y book ws I N S} (hv : validCross k l xs r y)
    (ok : crossHit k l xs r y book I N S ws = true) (dead : ∀ i, i < N → ¬NatRun (mask l) (goal l) s (S i)) :
    ¬NatRun (mask k) (goal k) s ws := by
  obtain ⟨hm,hy,hx⟩ := hv
  have e : crossWord (mask k) (mask l) (fun i => xs.getD i 0) y r book = pickRows r := by
    funext w
    unfold crossWord
    dsimp only
    split
    next hh =>
      calc
        exprB (mask l) y (book w) = exprB (pickRows r (mask k)) (fun i => pickRows r (xs.getD i 0)) (book w) := by rw [hm,funext hx]
        _ = pickRows r (exprB (mask k) (fun i => xs.getD i 0) (book w)) := (exprB_map _ _ _ _).symm
        _ = pickRows r w := congrArg _ hh
    next => rfl
  unfold crossHit at ok
  rw [e] at ok
  exact projHitDead hm hy ok dead

def projColumn (l : Nat) (raw : List Nat) (c : Nat) (i : Fin 8) : Nat :=
  if i.val=7 then 0 else
    let v := fld c 3 i.val
    if v=7 then mask l else raw.getD v 0

def cpWith (stop : Nat → List Nat → Bool) (k : Nat) (scs : List Nat) (count : Nat → Nat)
    (board : Nat → Nat → List Nat) (lookup : Nat → List Nat → Option Nat) : Nat → List Nat → Bool
  | 0, ws => !(ws == [goal k])
  | s+1, ws => stop (s+1) ws || !(nextDirect k s ws (fun _ zs =>
      !(scr k s scs zs) && !(checkpointHit count board lookup s zs) &&
        !(cpWith stop k scs count board lookup s zs)))

theorem cpWith_sound {k scs count board lookup stop}
    (nos : ∀ {s ws}, stop s ws = true → ¬NatRun (mask k) (goal k) s ws)
    (closed : ∀ s i, i < count s → cpWith stop k scs count board lookup s (board s i) = true)
    {s ws} (ok : cpWith stop k scs count board lookup s ws = true) :
    ¬NatRun (mask k) (goal k) s ws := by
  intro h
  induction s generalizing ws with
  | zero => simp [cpWith, zero_done h rfl] at ok
  | succ s ih =>
    have clean : stop (s+1) ws = false := by
      cases hy : stop (s+1) ws with
      | false => rfl
      | true => exact False.elim (nos hy h)
    let F (_ : Nat) (zs : List Nat) : Bool := !(scr k s scs zs) && !(checkpointHit count board lookup s zs) && !(cpWith stop k scs count board lookup s zs)
    have all : ∀ t ys, NatRun (mask k) (goal k) s ys → F t ys = true := by
      intro t ys hy
      have nohit : checkpointHit count board lookup s ys = false := by
        cases e : lookup s ys with
        | none => simp [checkpointHit,e]
        | some i =>
          cases he : checkpointHit count board lookup s ys with
          | false => rfl
          | true =>
            have hx : (decide (i < count s) && ys.isPerm (board s i)) = true := by
              simpa only [checkpointHit,e] using he
            simp only [Bool.and_eq_true] at hx
            obtain ⟨hi,hp⟩ := hx
            exact False.elim (ih (closed s i (of_decide_eq_true hi)) (Run.perm (List.isPerm_iff.1 hp) hy))
      have bad : cpWith stop k scs count board lookup s ys = false := by
        cases he : cpWith stop k scs count board lookup s ys
        · rfl
        · exact False.elim (ih he hy)
      simp [F,covers_ok hy,scr_no scs hy,nohit,bad]
    have hit := nextKept_complete h F all
    rw [cpWith,clean] at ok
    simp only [Bool.false_or] at ok
    rw [nextDirect_eq] at ok
    rw [hit] at ok
    contradiction


def medStop (n : Nat) (hint : List Nat → Nat) (r : Nat → List Nat)
    (idx : List Nat → Nat) (size : Nat) (S : Nat → List Nat) (s : Nat) (ws : List Nat) :=
  if s = 8 then
    let t := hint ws
    decide (t < n) && projHit idx size S (r t) ws
  else false

theorem medStopNo {k l n hint r idx size S s ws}
    (rows : ∀ i : Fin n, pickRows (r i.val) (mask k) = mask l ∧ pickRows (r i.val) (goal k) = goal l)
    (dead : ∀ i, i < size → ¬NatRun (mask l) (goal l) 8 (S i))
    (ok : medStop n hint r idx size S s ws = true) : ¬NatRun (mask k) (goal k) s ws := by
  by_cases eqv : s=8
  · subst s
    change (decide (hint ws < n) && projHit idx size S (r (hint ws)) ws) = true at ok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
    have q := rows ⟨_,ok.1⟩
    exact projHitDead q.1 q.2 ok.2 dead
  · simp [medStop,eqv] at ok

def medC (stop : Nat → List Nat → Bool) (k : Nat) (scs : List Nat) :=
  cpWith stop k scs (fun _ => 0) (fun _ _ => []) (fun _ _ => none)

theorem medC_sound {stop k scs s ws}
    (h : ∀ {d ys}, stop d ys = true → ¬NatRun (mask k) (goal k) d ys)
    (w : medC stop k scs s ws = true) : ¬NatRun (mask k) (goal k) s ws := by
  apply cpWith_sound h _ w
  intro d i hi
  exact False.elim (Nat.not_lt_zero i hi)

namespace Row13
def inputs : List ℕ := [0x11b11bf1b046c88d93e09b21364f8451149f000000fff000000001e0000000078000000f,0x2452451457d147a28e2145428a90cbc2f1710000000003ffc7ff8e000000000003c0f070,0x4864862868a19143245f861f0c393c8f23a20000000000000000000fff1ffe383c0f0380,0x828f2842810a27947082289751c2112ffc04000fff00000007fff000001fffc0000ffc00,0xf308308303cc3a18410bb0e461043ff44808fff0000003fff800000fffe000003ff00000,0xf40f40f40e100420080bc0f781ffc2008040fffffffffc000000000fffffffffc0000000,0xf80f80f80fe03fc07ffc0018002020080200fffffffffffffffffff00000000000000000]
def vals := sampleTable inputs 288
def scs : List ℕ := [0x210781b0932489b,0x13c291e09925895,0x1b0290e09b24c92,0x1b05e13c9b24093,0x1b0291e09924891,0x1b04f1e09624890,0x1b0381789325491,0x1b04f1789b24c92,0x1b04f0a49524490,0x13c382109925895,0x1b0290e09b24492,0x1b0380a49b24893,0x13c291b09924095,0x1b05e0e09624c90,0x1b04f0e09325496,0x1b05e0e09524490,0x1b02913c9924091,0x1b0292109924c91,0x13c291b09124099]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)
def qBook (w : Nat) : Nat :=
  let d := fld 0x554c8c3142a8e0c0001180012082 6 (w % 19)
  fld 0x94849543ccd585444106c383cbcad48d424693a6c2819e96040201e6c6ae00dee540ee829d860300ddd3008e8c0500c5dca59cd68ac4ce45cdc18b 8 (((w >>> 0) + d) % 59)

def qPerm (i : Nat) : Nat := fld 0xb9c286ae222e8ca000000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0x1130000000d3003e60e840000000c4003aa0c78000020ab58236cd86a000000000003a400de003dc00ad7b179b05b003a000a37393dae4c00369ac996a9248a440000000c20000000b8003419e38002a564350030580290027d6226002d1602357a583e1e0000000a200278009b0029d541a5305926140027540104e031240a002552207480100000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x688 3 (fld 0x410491615c4c61879001472004085200024 2 (bsr 0xfec2e0a6fb828f20f957e4b6f6775b50edc75f20e7e8002fe55b79a3e248fac0df9b3e41df6c305dddc57c74dd7e3b8edaf1b502da6af460da0097e5d6c6b9f9d5c5105dd4b15d83ca77149ac7fabf8bc0994494c0922f4db8ca5e19b6c3adebaaa547aca9085f8fa2f2d5f2a2ab883a9e7733ac93cc3e9d8eb19e27872f76d9864f32ce8336ba717daa46ee7d3c8db47c7b514477b25c0b6f26116f6ec645866c998ae35d1ff5f951f0f60450c3b84d4a810e8a4a0dd619457e3ffc37bc66913786270730541d362cd540902ca29bed2a16156129bdc33d28c110b624a8a85720c1af3b205f4dd61f43052f17fff0a9171e26bd140972810e591ac00e13c6420dabd1680b1f4adc08bd97d908ab4b81083f91b402a08c45 32 (hk ys) 7 0 70))
def qOri0 := quickOri 144 4 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 4, i.val = 0 ∨ validQuick 144 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 144) (fld 0xf65e53f43000102f10e43e21e31f53100403e30f30400e10760f50504e51e61500e65106506104405f51f21401f31e50761f61651502 12 i) inputs
def I (ys : List Nat) := bsr 0xfb828f20f957e4b6edc75f20e7e8002fe248fac0ddc57c74da0097e5c7fabf8bc0922f4db6c3adeba2f2d5f293cc3e9d7daa46ee7d3c8db47c7b514477b25c0b6f26116f5d1ff5f94a810e8a457e3ffc37bc66913786270730541d362ca29bed2a16156129bdc33d24a8a8571f43052f171e26bd140972810e591ac00e13c6420dabd1680b1f4adc08bd97d902a08c45 32 (hk ys) 6 0 36
def cls (i : Nat) := fld 0xa300b0000004812001e003c0c10184181910440c01960 5 i
def sel (c : Nat) : List Nat :=
  let t := if (c-1)/10 = 0 then 0x184d067a5936934925522905c2a564c260b012c9b49a492a91482e13eb15a2c164b1582bd2c9b49a492a914825944a7552a52c9e4da9d4c934925522904da4d449d5027d2c9e4da4d3a9c4925522904da492a914b25520934924520381c0e070381c0e070381c0d46a35148a45229148a45229148a44c261308c461f0f87c3e1f0f87c3e1f0f87c3c1a0d0682c160b0582c160b0582c160b050281008040180c06030180c06030180c060281407038100804000000000 else 0x1d2f77b26536934925520916f2b5b0e97439d329b49a492a9048b7946d76d355b0d76ab59329b49a492a9048a653ca7532b532a24da9d54934925520914da4d3c9d4e28d32a24da4d3aa04925520914da492a904ca55229349241225e2f178bc5e2f178bc5e2f16cb65b2793c9e4f2793c9e4f2793c984c261249245229148a45229148a452291488160b058341a0d068341a0d068341a0d050280c0603020100804020100804020100802814040201c0e07000000000
  (List.range 162).map (fld t 9)
def dst (i : Nat) := (cls i - 1) % 10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem projOK : ∀ i : Fin 36, cls i = 0 ∨ projOk 144 81 (sel (cls i)) (B i) (Fixed40.S9 (dst i)) = true := by decide +kernel
def medIx (ws : List Nat) := (orbitLookup (fld 0x14065cd72071970828403120d02054481d2002c0125a3bc24444213d037027cca01c24060241126b89e83c06d89a844c227fc10639ba4b010802a897134037d096d4a4fa4d6ccfea87c0516f645305b344133920d838d01aeca03a08cb105701fa24ed071c7 2) 0 135 (hk ws) + 2) % 3
def medRows (i : Nat) : List Nat :=
  let a := if i = 0 then 0x1d2f77b26536934925520916f2b5b0e97439d329b49a492a9048b7946d76d355b0d76ab59329b49a492a9048a653ca7532b532a24da9d54934925520914da4d3c9d4e28d32a24da4d3aa04925520914da492a904ca55229349241225e2f178bc5e2f178bc5e2f16cb65b2793c9e4f2793c9e4f2793c984c261249245229148a45229148a452291488160b058341a0d068341a0d068341a0d050280c0603020100804020100804020100802814040201c0e07000000000 else 0x184d067a5936934925522905c2a564c260b012c9b49a492a91482e13eb15a2c164b1582bd2c9b49a492a914825944a7552a52c9e4da9d4c934925522904da4d449d5027d2c9e4da4d3a9c4925522904da492a914b25520934924520381c0e070381c0e070381c0d46a35148a45229148a45229148a44c261308c461f0f87c3e1f0f87c3e1f0f87c3c1a0d0682c160b0582c160b0582c160b050281008040180c06030180c06030180c060281407038100804000000000
  (List.range 162).map (fld a 9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem medRowsOK : ∀ i : Fin 2, pickRows (medRows i.val) (mask 144) = mask 81 ∧ pickRows (medRows i.val) (goal 144) = goal 81 := by decide +kernel
def halt := medStop 2 medIx medRows (Fixed40.index 8) (Fixed40.N 8) (Fixed40.S 8)
theorem haltNo {s ws} (ok : halt s ws = true) : ¬NatRun (mask 144) (goal 144) s ws :=
  medStopNo medRowsOK (fun i hi => Fixed40.atDepth 8 i (Or.inl rfl) hi) ok
def test (i : Nat) := if cls i = 0 then medC halt 144 scs 9 (B i) else true

theorem test_sound (i : Nat) (hbound : i < 36) (hi : test i = true) : ¬NatRun (mask 144) (goal 144) 9 (B i) := by
  by_cases hc : cls i = 0
  · exact medC_sound haltNo (by simpa [test, hc] using hi)
  · exact projOk_dead ((projOK ⟨i, hbound⟩).resolve_left hc) (Fixed40.dead _ (Nat.mod_lt _ (by decide)))

set_option maxRecDepth 10000 in
lemma roof : bar 144 (cutB 9 inputs B) (cutN 9 36) (fun _ => I) qOri0 scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 2 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 3 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 4 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 2 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 3 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 4 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 2 22 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 3 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z27 : span test 4 27 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z31 : span test 2 31 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z33 : span test 3 33 = true := by decide +kernel
lemma regionOK : span test 36 0 = true := by with_reducible exact (sj (sj (sj z0 (sj z4 z6)) (sj z9 (sj z13 z15))) (sj (sj z18 (sj z22 z24)) (sj z27 (sj z31 z33))))
theorem finChk : ¬NatRun (mask 144) (goal 144) 10 inputs :=
  symCutRoot (quick_safe (k:=144) (bound:=4) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof (fun i hi => test_sound i hi (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 144 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row13

namespace Row18
def inputs : List ℕ := [0x16c16c88d76c05b05b22337b00ec0ec9292af800000000fff8000000003ffe000000000000f,0x216b141781140859c505e02501155942e2e588007ff80f0000001ffe03c0000007ff81c1c30,0x2b182187902189c60861e404615981187474717ff8000f00001ffe0003c00007ff8000e0e0c0,0x2ba2ba38004a012812848818857a17a3807f827ffffff0000000000000000007ffffff00ff00,0xc40c41221841bd0bd0e006101dc1dc3ff80040000000000001ffffffc000007ffffffff0000,0x3083082446082de0de0fffbe0e6026010049000000000000001ffffffffffff8000000000000,0x3f03f03ffff03e00e00911c00b8038024900007fffffffffffe0000000000000000000000000]
def vals := sampleTable inputs 302
def scs : List ℕ := [0x1fc4d06ca8280bd,0x134351649c26097,0x22c671fc9927098,0x19c590d4bd268a8,0x22c7f19c9825c9c,0xd41b134a026899,0xd41b22ca82609a,0xd41b1fca82649a,0xd41b134a025c99,0x1342719cbd264a0,0xd4271349c25c98]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def qBook (w : Nat) : Nat :=
  let d := fld 0xcbc722d00644400554450c 6 (w % 15)
  fld 0x8adcdda541a682d406839cc105c38d428103d5ee40ceaee6c5854602de8e01c6c29d45cb00869ed644cc04848c96e5008b9394ca4300c4d300cd95 8 (((w >>> 17) + d) % 59)

def qPerm (i : Nat) : Nat := fld 0xb9c285ce22358ca000000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0xfb003bc00e300000012d0048401150000000e000371b0bd0000000c8002f000b10000000ae002ae10a800476508b8e1fe0c7c004320a78821d0ce650000000c6002e800b0003adec5975135aa4a0000000a60028da8a000369a446689086a33002e186275b86d5e18002a9581554849341000289480d5082932080027130064b8100000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x688 3 (fld 0x18822492803840868420032830708899 2 (bsr 0xf9795bfaf7ca5b71f5bf7ce0f163380ced9c28c1e94ccfbde058865fdaf380a7d840bc00d79982c3ce89ad8ece82c438c6ce523bc0fd0ac4bd0fed01bcfab1a9b69b83adb23ed016b0fb3666b0c1e62daba738b6aaca9698a9ebec5fa9dd629ca52443c2a48ba7fa9fdf667098e2a61e8d02265289ba790489afb26b8568c2c484c9e6908295090c81d5c9697a18dad2737193a4695708f968cc8bed60e0a5a660ab18a1608a3ff95f41c7865eb654ca5a25f2da5910af6d54d59f9047ca584e451e2fcb421dd2bf40e1f9033e3a2c25384bcb65321a3b972dbc0bf7272886371db835851c6fbd121be8f6051aa9a0ae18a9b674148b0d770b63a955055a7878 32 (hk ys) 7 0 64))
def qOri0 := quickOri 151 4 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 4, i.val = 0 ∨ validQuick 151 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 151) (fld 0xf10f40106f21506102f50e64404f41e40502f53e65e51401e54500f51100e41e21503103405e50f54e34e10400f34000f65 12 i) inputs
def I (ys : List Nat) := bsr 0xf9795bfaf163380ce94ccfbde058865fd840bc00ce82c438bd0fed01b23ed016b0fb3666b0c1e62daba738b6a9dd629ca48ba7fa9fdf667098e2a61e89ba79048295090c7a18dad2737193a468cc8bed60e0a5a660ab18a1608a3ff95f41c7865a25f2da47ca584e451e2fcb40e1f9033e3a2c252dbc0bf7272886371c6fbd121aa9a0ae 32 (hk ys) 6 0 33
def test (i : Nat) := checkD 151 scs 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 151 (cutB 9 inputs B) (cutN 9 33) (fun _ => I) qOri0 scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 4 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 4 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 4 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 4 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z20 : span test 4 20 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 4 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z28 : span test 2 28 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z30 : span test 3 30 = true := by decide +kernel
lemma regionOK : span test 33 0 = true := by with_reducible exact (sj (sj (sj z0 z4) (sj z8 z12)) (sj (sj z16 z20) (sj z24 (sj z28 z30))))
theorem finChk : ¬NatRun (mask 151) (goal 151) 10 inputs :=
  symCutRoot (quick_safe (k:=151) (bound:=4) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 151 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row18

namespace Row19
def inputs : List ℕ := [0x42fc2c012c7c04b9cb00964f01591f045278007ff8000078001ffe00000e00001e00007,0x3c544540257c409505533aa3902aa214bc5cfff80000007800000003ffc7000000007838,0x898898eb98881260a6414c92cf30f23c8e90000000fff800000000000000fff1e0781c0,0x11211210c2111bc83081791c45b47043ff020000000000001ffe0003fff80fffe007fe00,0x2242242304222dd0dd0ea20206b87ffc10100000000000001ffffffc00000ffffff80000,0x3c83c83c080009e09e0f3c1ff8c0040100807ffffff000001ffffffffffff00000000000,0x3f03f03ff03ffe00e009c0100700488a22007fffffffffffe00000000000000000000000]
def vals := sampleTable inputs 286
def scs : List ℕ := [0x114201449724490,0x20c451dca323c94,0x19c51114a324499,0x1dc6720c9723c90,0xd8201449725093,0x1142019c9924091,0x19c200d899250a3,0x1142020c9323c90,0x20c770809124c8f,0x19c4520c9323c90,0x20c45144942448f,0xd8201dc9023c93,0x1dc5120c9923c91]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)
def qBook (w : Nat) : Nat :=
  let d := fld 0x3b898033028162e03001102e30001 4 (w % 29)
  fld 0xcbd59ee6ddd684ca850500a583c101438193008ec294cd0682cec544424640dce5d30204c3d403958a9d9ccc0041aec4458bc68d96ee00a6de868c 8 (((w >>> 23) + d) % 59)

def qPerm (i : Nat) : Nat := fld 0x35710200000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0xeb00000000000475bed30000000000034220c40046e1f028720cee740000000ba0000000ae0000000ab003d54ea30000000a100275e099003cdde677718cbe5d0000000b700335b85100001b6aa6d3048a420033000a0658d97c33003017a975e0c05a2c002d56820002714c1d002a54a19522502a130026d3c0f4d02d22090024d20064780c0000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x4 2 (fld 0x1858e48be88228500 1 (bsr 0xfdbf7bcafd7239e7f853cf8ff3a47eecf2c4f171edab805febd25c57e58a7b05e35ef914e00aade0ddc13479d7cb6f94d53813b8c9252652c2cc5fa4be370bdcbdb2c8f6b93c43e1b7eabc0db6563989b15059b2a9b60f5da23bcf419ac580ca93dd0d12904f2e208adf4a6384253f6e800f32447d71db547cc8d5d77bf9a0a5773ee0a57043f3476cf6ceca6c82649a6b3bcedc698c41da60635b1960205ccd5950015f589d670856a171b94dee9f4b4ddc56254c70b91b4671850b464185543ff014f93a510d9537f90bb23700a0a2330c54be3019fac72b5f3ac726b4de2c2131f5dd1bec420c174d6aa716b4fe39157bf054115fec560c01d95d0342b8480316ee6001b5a6cf00d1b3c6 32 (hk ys) 7 0 67))
def qOri0 := quickOri 143 2 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 2, i.val = 0 ∨ validQuick 143 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 143) (fld 0x406f40e30104505106e43e40e60f20506f43e10403101f30f52e65e20e50e32f53e62f62f10502750504102f65f50402400000501f32652405e63f60e53f63105e52 12 i) inputs
def I (ys : List Nat) := bsr 0xfdbf7bcafd7239e7f2c4f171edab805febd25c57e58a7b05e00aade0d53813b8c9252652c2cc5fa4b7eabc0db6563989a9b60f5da23bcf4193dd0d12904f2e208adf4a63800f32446cf6ceca6b3bcedc698c41da60635b195950015f589d670856a171b94dee9f4b4ddc56254671850b464185543ff014f937f90bb2330c54be3019fac72b5f3ac726b4de2c1bec420c16b4fe39157bf054115fec560c01d95d0342b8480316ee6001b5a6cf00d1b3c6 32 (hk ys) 6 0 44
def cls (i : Nat) := fld 0xa0003000000008007202080000000a57510012002042 4 i
def sel (c : Nat) : List Nat :=
  let t := 0x55a8d429979bbd289149a411ef551a7532f37725122934823d4ea378265deee4a245269047a8d32ba51a656ab44a245269047ab938a655aa54aa751a654ca55225122934823d469450a6d3ca34ea6538944da6922934823d329149a41289347a45208f3399cce673399cce673399cce633198cc6633198cc6633198cbe5f2f97cbe5f2f97cbe5f2f974ba20100804020100804020100743a1d0c86432150a8542a150a8542a150a85426130783c1e0b0582c160b0582c160b0582c1209030180603018000000
  (List.range 176).map (fld t 9)
def dst (i : Nat) := (cls i - 1) % 10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem projOK : ∀ i : Fin 44, cls i = 0 ∨ projOk 143 88 (sel (cls i)) (B i) (Fixed41.S9 (dst i)) = true := by decide +kernel
def test (i : Nat) := if cls i = 0 then checkD 143 scs 9 (B i) else true

theorem test_sound (i : Nat) (hbound : i < 44) (hi : test i = true) : ¬NatRun (mask 143) (goal 143) 9 (B i) := by
  by_cases hc : cls i = 0
  · exact checkD_sound (by simpa [test, hc] using hi)
  · exact projOk_dead ((projOK ⟨i, hbound⟩).resolve_left hc) (Fixed41.dead _ (Nat.mod_lt _ (by decide)))

set_option maxRecDepth 10000 in
lemma roof : bar 143 (cutB 9 inputs B) (cutN 9 44) (fun _ => I) qOri0 scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 2 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z2 : span test 3 2 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z5 : span test 3 5 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 3 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z11 : span test 2 11 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 3 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 3 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z19 : span test 3 19 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 2 22 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 3 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z27 : span test 3 27 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z30 : span test 3 30 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z33 : span test 2 33 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z35 : span test 3 35 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z38 : span test 3 38 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z41 : span test 3 41 = true := by decide +kernel
lemma regionOK : span test 44 0 = true := by with_reducible exact (sj (sj (sj (sj z0 z2) (sj z5 z8)) (sj (sj z11 z13) (sj z16 z19))) (sj (sj (sj z22 z24) (sj z27 z30)) (sj (sj z33 z35) (sj z38 z41))))
theorem finChk : ¬NatRun (mask 143) (goal 143) 10 inputs :=
  symCutRoot (quick_safe (k:=143) (bound:=2) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof (fun i hi => test_sound i hi (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 143 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row19

namespace Row20
def inputs : List ℕ := [0x42c42fc2c10bf0b047847c02b13e0806ca78000007ff8001ffe007007800003c0000007,0x857c544542151152bc8bc405524294bd45c8007ff800000000007807800000000fff838,0x3c18818818f062061c93c88a660e478098697ff8000001ffe0003807801ffe1c0f0000c0,0x12a12a12a14a84a85125111ee8f087eee38200000000000000000000001fffe00fffff00,0x2142142142f50f50e202222b70fff81300100000000001ffffffc000001ffffff0000000,0x3d83d83d838608608003fff38049121c01007ffffffffe0000000007ffe0000000000000,0x3e03e03e03f80f80fffc000c0080046002007ffffffffffffffffff80000000000000000]
def vals := sampleTable inputs 286
def scs : List ℕ := [0x20c771ac9023c93,0x20c291749929098,0x1dc5102c98250a4,0x1ac0b1dc9923c91,0x1442902c9323c90,0x1ac2920c9824091,0x1dc51174942408f,0x1442902c9124c90,0xa40b20ca424c94,0x1440b0a4942448f,0x1ac0b144a424498,0x1dc6b20c9924c8f,0x144291749925091,0x1440b0a49124c8f,0x1ac0b1749924091,0x1dc5d1aca423c94]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def rho (_ : List Nat) : List Nat := []
def B (i : Nat) := mv (mask 143) (fld 0xf43404f53e21e40102401106e30f50105e31f24402e63406100403101104e62f60e60e61663000505e52500f54503f61f63760e51e24e50e10e41f64103400f51e20405f31f62f52e65f65f20e53e64f41e43765f40f23e23502f10f21f30e54504506501 12 i) inputs
def I (ys : List Nat) := bsr 0xfbbb207cf846ca6cf61c44aef1b63f6af06788f3f031bf29ea55c7ace5f9f36fe3a88167de74b108dd3a27eddaffd105ca576bb2c7982f8ac6d913dec5966451bcfa0acbbab7b327b8baf593b418853ab15943afb131d659afe29894ab31c543a11482539fd1d2c69f49cf7d97512cf58f527ac58e3190de8d86beca8d5482e48ca23b4f8b6d44ce89a6f67187ca36b980bc0f9a78c2eb90788cce96776f78a472a0de69722a42c06ac9398c65216b4b61e17a56612940e660131ae153f09545530585d250c39e5b470a563941568e913dd4164a3b6dbc71359a118e2aff0cd01f724bbd1d0730f518edb4be17f81bf2170a89d51628de5813a908c611d1e6300c8d7ce50bbe84ff033eea7e 32 (hk ys) 7 0 67
def cls (i : Nat) := fld 0x9000064000007220800252c11000006800000090500a0702a00200000000000030 4 i
def sel (c : Nat) : List Nat :=
  let t := if (c-1)/10 = 0 then 0x59a91529865b1d289149a411ecd5228d30cb6325122934823d60a4642618ec64a245269047a9130c1522617cbd4a245269047ad942af59ac95cb0522615eae56a5122934823d489454a7d4ea451a6142944fa7922934823d309149a41289347a45208f1f8fc7e3f1f8fc7e3f1f8fc7e3b1d8ec763b1d8ec763b1d8ec6e371b8dc6e371b8dc6e371b8d46a29148a45229148a45229148944a2511088441e0f0783c1e0f0783c1e0f078381c0c060300b0582c160b0582c160b0582c1008030180603018000000 else 0x54a6166a463b2d22944824d1ec84c2c148c763245289049a3d469866a9196c648a51209347a6148c14c2917abe48a51209347ad95ea154a9d3ea34c291429f4f245289049a3d309159ab96498582915e91572b5289049a3d48944824d229047a51268f1f8fc7e3f1f8fc7e3f1f8fc7e371b8dc6e371b8dc6e371b8dc763b1d8ec763b1d8ec763b1d8d46a29148a45229148a45229148944a250c060300b0582c160b0582c160b0582c100811088441e0f0783c1e0f0783c1e0f078381c0301800000000c0603
  (List.range 176).map (fld t 9)
def dst (i : Nat) := (cls i - 1) % 10
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem projOK : ∀ i : Fin 67, cls i = 0 ∨ projOk 143 88 (sel (cls i)) (B i) (Fixed41.S9 (dst i)) = true := by decide +kernel
def medIx (ws : List Nat) := (orbitLookup (fld 0x201035124854d4085a159760930810102c75944521300c304118198810653001c400004a22033090c0000005c1e10595f3e840502c557940c55011f28c5140c89814ce06cc33750000510591c3301f1c206051411903bc874c80413d39081d60124850431873a76d1d4c7401429ce00c00103128cd8022c2428f34349160b2e440154d8637 2) 1 177 (hk ws) + 2) % 3
def medRows (i : Nat) : List Nat :=
  let a := if i = 0 then 0x59a91529865b1d289149a411ecd5228d30cb6325122934823d60a4642618ec64a245269047a9130c1522617cbd4a245269047ad942af59ac95cb0522615eae56a5122934823d489454a7d4ea451a6142944fa7922934823d309149a41289347a45208f1f8fc7e3f1f8fc7e3f1f8fc7e3b1d8ec763b1d8ec763b1d8ec6e371b8dc6e371b8dc6e371b8d46a29148a45229148a45229148944a2511088441e0f0783c1e0f0783c1e0f078381c0c060300b0582c160b0582c160b0582c1008030180603018000000 else 0x6ca51bea4742dd1e9869a6522ad4a2c148e857a3d30d34ca4542945b2916eaf47a61a69948a5149114a292051047a61a69948b358ca36cb4d4ca14a29146a64f23d30d34ca45288f6fc09f094582918c8f8132130d34ca45489869a651ed348a613291271389c4e271389c4e271389c1e0f0783c1e0f0783c1e0f0784a25128944a25128944a251287038773b9dcee773b9dcee773b8ec763b2391c8e0b0582c160b0582c160b0582c0603349a4d2371b8dc6e371b8dc6e371b8dc6a352190c0000000201008
  (List.range 176).map (fld a 9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem medRowsOK : ∀ i : Fin 2, pickRows (medRows i.val) (mask 143) = mask 88 ∧ pickRows (medRows i.val) (goal 143) = goal 88 := by decide +kernel
def halt := medStop 2 medIx medRows (Fixed41.index 8) (Fixed41.N 8) (Fixed41.S 8)
theorem haltNo {s ws} (ok : halt s ws = true) : ¬NatRun (mask 143) (goal 143) s ws :=
  medStopNo medRowsOK (fun i hi => Fixed41.atDepth 8 i (Or.inl rfl) hi) ok
def test (i : Nat) := if cls i = 0 then medC halt 143 scs 9 (B i) else true

theorem test_sound (i : Nat) (hbound : i < 67) (hi : test i = true) : ¬NatRun (mask 143) (goal 143) 9 (B i) := by
  by_cases hc : cls i = 0
  · exact medC_sound haltNo (by simpa [test, hc] using hi)
  · exact projOk_dead ((projOK ⟨i, hbound⟩).resolve_left hc) (Fixed41.dead _ (Nat.mod_lt _ (by decide)))

set_option maxRecDepth 10000 in
lemma roof : bar 143 (cutB 9 inputs B) (cutN 9 67) (fun _ => I) (rowOrient 143 rho) scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 4 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z8 : span test 4 8 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 4 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 4 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z20 : span test 4 20 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 4 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z28 : span test 2 28 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z30 : span test 3 30 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z33 : span test 4 33 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z37 : span test 4 37 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z41 : span test 4 41 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z45 : span test 2 45 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z47 : span test 3 47 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z50 : span test 4 50 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z54 : span test 4 54 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z58 : span test 4 58 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z62 : span test 2 62 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z64 : span test 3 64 = true := by decide +kernel
lemma regionOK : span test 67 0 = true := by with_reducible exact (sj (sj (sj (sj z0 z4) (sj z8 z12)) (sj (sj z16 z20) (sj z24 (sj z28 z30)))) (sj (sj (sj z33 z37) (sj z41 (sj z45 z47))) (sj (sj z50 z54) (sj z58 (sj z62 z64)))))
theorem finChk : ¬NatRun (mask 143) (goal 143) 10 inputs :=
  symCutRoot (ori_ok rho) roof (fun i hi => test_sound i hi (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 143 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row20

namespace Row23
def inputs : List ℕ := [0x4b04b2235cb012e72c080afc02b13e1153c000000007ffc000fff00000f00000780007,0x95ad505e055025415494dd44055242af2e4003ffc07800000000001fff000000003c38,0xac60861e408627182187811885660e47234bffc000780000fff0001e00003ffc381c0c0,0xae8ae8e0012804a04a12062115e8f087fc13ffffff8000000000000000003fffc01ff00,0x3103104886106f42f43818400770fff84080000000000000ffffffe000003fffffe0000,0xc20c20911820b783783fef83f98040048800000000000000ffffffffffffc0000000000,0xfc0fc0ffffc0f803802470022e0089100003ffffffffffff00000000000000000000000]
def vals := sampleTable inputs 284
def scs : List ℕ := [0x1101e1409723c90,0x1d81e208a024893,0x1d844178b724097,0x140440c0922388f,0x1d85e2089223c8e,0x17830078a025cb7,0x11030078932408e,0x1d8501788f23892,0x1d850178a023893]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def qBook (w : Nat) : Nat :=
  let d := fld 0x7002d40033d100a7d3 5 (w % 15)
  fld 0x95aec6469dc305008c85ce439e00a5c400d48e41d5968dc20283ccee039ccd00018400d60686dd008b82420094cb00c1e6404445e5dc000093d3048ac5caa681de 8 (((w >>> 23) + d) % 65)

def qPerm (i : Nat) : Nat := fld 0x2e710200000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0xe900001bad100000011b0043c01030000000ce003297ab70000000b60043400ab0000000a7003ed48a00042e2c82851d9e873003e9e66f791acbc5c0000000b400001b4aa00395b2506c31c884100000009e0026d789700311763d5d0c0582a002c9621e00269461a00299441750a4c261100265380e4c0292008002491e064700c0000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x4 2 (fld 0xc07d61251b0941ae 1 (bsr 0xfad57cb8f9047f6df75acffbed7be9d0ebdd4332e951c2f7e84a982be66bcd2cda83b6a2d9681db1d39d99dccd0b5820cd09d6d8ca5d2c92c3b0b69ec223ee35bf567c23bd81d0b9bb13f5dcb6d82285adc7586cada8c338ac8cb5c4ac7e0d38a2be6553a0b125729d83592a98f245569756d55b95268ac49377e3d79164dcb68d3232e286f93574830329a581d920eb7a1f058178c8f10a7482b68d6968e6a668f7a89367b8c7d6675a0ee560fd95995accbdfd5a3906515885c981534d0c244f485e064ebbd8de4ce777da486b43f04010b6873d5df0733d31516f3699612b2f5a17b02cee13cf22802718116347de1041c9290b589ae80b0d049403c2b6a1 32 (hk ys) 7 0 64))
def qOri0 := quickOri 142 2 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 2, i.val = 0 ∨ validQuick 142 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 142) (fld 0xe64e51e52f34e54e40e20404f65f40f20402503e50e65506f41102f52f53106e34e41f10f32101501103f50405f54f51000e10e24400502 12 i) inputs
def I (ys : List Nat) := bsr 0xf75acffbed7be9d0ebdd4332e951c2f7e84a982be66bcd2cda83b6a2c3b0b69ebf567c23b6d82285adc7586cada8c338ac8cb5c4a2be6553a0b1257298f245569756d55b9377e3d78d3232e286f93574830329a578c8f10a68f7a89367b8c7d6675a0ee560fd95995a3906515885c9814f485e064ce777da486b43f04010b6873d5df0733d31516f2cee13cf116347de03c2b6a1 32 (hk ys) 6 0 37
def test (i : Nat) := checkD 142 scs 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 142 (cutB 9 inputs B) (cutN 9 37) (fun _ => I) qOri0 scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 4 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z4 : span test 2 4 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 3 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 4 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 2 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 3 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 4 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 2 22 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z24 : span test 3 24 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z27 : span test 2 27 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z29 : span test 3 29 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z32 : span test 2 32 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z34 : span test 3 34 = true := by decide +kernel
lemma regionOK : span test 37 0 = true := by with_reducible exact (sj (sj (sj z0 (sj z4 z6)) (sj z9 (sj z13 z15))) (sj (sj z18 (sj z22 z24)) (sj (sj z27 z29) (sj z32 z34))))
theorem finChk : ¬NatRun (mask 142) (goal 142) 10 inputs :=
  symCutRoot (quick_safe (k:=142) (bound:=2) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 142 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row23

namespace Row24
def inputs : List ℕ := [0x12c12c88d72c02b02b2232eb003601b55d8255e000000003ffe000000000fff80000007ffc0007,0x216b1417811404596505e025004aab500a85cb2001ffe03c0000007ff80f0000000fff80000e18,0x2b182187902189660461e4046156c0260130e8e5ffe0003c00007ff8000f00001fff00000007060,0x2b62b63800460978978e0009801900c80641ff09ffffffc000007ffffff00000000000000007f80,0xcc0cc12218c13903904887105fe0ff07f8792000000000000000000000000001ffffffffff8000,0x3083082446082de0de0fffbe0e601300980200000000000000007fffffffffffe00000000000000,0x3f03f03ffff03e00e00911c00b801c00e0040001ffffffffffff800000000000000000000000000]
def vals := sampleTable inputs 314
def scs : List ℕ := [0x2141f14cbb2b4ae,0xb01f0489e274a1,0x244120b0a52789f,0x2146d2449f2849d,0xec121b4bb2b8ad,0x2143b07cae2b4bb,0x14c1207ca52749f,0xb01214c9f2849e]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def qBook (w : Nat) : Nat :=
  let d := fld 0x301f3d0e19058c0040138122 5 (w % 19)
  fld 0x8c93c5d50000058e00459c00d6cddd0143d3e5cc8a448bdc8d40c18306c39e85c642d496e6caa6c4038602c241ee9584cea58200decb460481ae9d94 8 (((w >>> 0) + d) % 61)

def qPerm (i : Nat) : Nat := fld 0x174650283d6221dd358ca000000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0x107003ec00ef0000000ec003a1c8bb000000137004ac01200000000d40031d74ae004a6689194216248200462227e881e8da6b000000104003e000ee0000000d20031570ad003da025f7a94dbe5000399bc4c6e92076390000000ab002a16ca500305682c5987c240f0029d520c530253e07002853c054e80c0000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x4688 3 (fld 0xe465b8084d80806c001965881811001861a653052400291 3 (bsr 0xfd73216afd2ae6a0f4b4ebf0eebc10b5ee8dd76ee615bbb3e2771267dcc8cd84db1f5491d9204e97d82f7fc1d3bc4e42d26d8defcf757ea1c77a1116c3428d89bce7a9e1ba26b6e3b8ed470bb1f21bebb0f1248fa9f68c8ea820a7a09e1133ea9d7fb3f59821dd2d94b96e8c92b118818f112e658a3c63418944838f7e976dac7e6e118f7d3edc677c2f6c1276c035e76b7510e56625fa5465e342a66579cdbd600390ec5b81fc0d5b728fb5522d3c26518f9a784cc737e84a3af73d41b01e383b19fbcd39e2c65133c0b0563136606d2d6bcfc22d5bc1062870c4e623ac96e32281415921d63bcd20a119321663282a1523e67c14e5b5370c33c12b07c33d73 32 (hk ys) 7 0 64))
def qOri0 := quickOri 157 5 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 5, i.val = 0 ∨ validQuick 157 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 157) (fld 0xe40f51000106f30e51400503f31e50e31506f21e21e30403f40504f41104401f10e10103 12 i) inputs
def I (ys : List Nat) := bsr 0xfd73216ad9204e97d3bc4e42c3428d89bce7a9e1b8ed470bb1f21beba820a7a09e1133ea9d7fb3f59821dd2d7e976dac7d3edc6776c035e76b7510e56579cdbd600390ec5b81fc0d522d3c264cc737e82d6bcfc221d63bcd20a119321663282a 32 (hk ys) 5 0 24
def test (i : Nat) := checkD 157 scs 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 157 (cutB 9 inputs B) (cutN 9 24) (fun _ => I) qOri0 scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 3 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z3 : span test 3 3 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 3 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 3 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z12 : span test 3 12 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z15 : span test 3 15 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z18 : span test 3 18 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z21 : span test 3 21 = true := by decide +kernel
lemma regionOK : span test 24 0 = true := by with_reducible exact (sj (sj (sj z0 z3) (sj z6 z9)) (sj (sj z12 z15) (sj z18 z21)))
theorem finChk : ¬NatRun (mask 157) (goal 157) 10 inputs :=
  symCutRoot (quick_safe (k:=157) (bound:=5) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 157 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row24

namespace Row25
def inputs : List ℕ := [0x41fc1c02389f009c4f802e23277001e4a578007ff800001e00000f000003ffe00000007,0x3c244246a487125a438805244019297239ccfff8000fff0e07ff8700000000003ffc7398,0x848848ea978201489132e41e0a209d5c1f10000000ffff000000003ffc3c0003fff83e0,0x11111110c21246d93c21669e04440d59fe0200000000000007fff803fffc00003ffffc00,0x22a22a23142489621245b71ffb78f260108800000000000000000003ffffffffc0000000,0x3cc3cc3c1840027c3ffe38088380438081207ffffff0000007fffffc0000000000000000,0x3f03f03fe07fff802001c0111c009c0124007ffffffffffff80000000000000000000000]
def vals := sampleTable inputs 286
def scs : List ℕ := [0x13c360489524ca9,0x1dc4f20c9a23c91,0x1dc36084a924095,0x1a0210489a24cac,0x1a0211dcac23c93,0x1dc36084ac2449a,0x841213c9523c90,0x84120d8932408f,0x13c211a0ac254a9,0x84121a09a24091,0x1a0360489a24cac,0x1a02120c9524c90,0x1dc680d8932448f]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
def qBook (w : Nat) : Nat :=
  let d := fld 0xb2a90805ef52b700c701001303182 4 (w % 29)
  fld 0xced6c5ca8a018600ee84d593dc8de5cbcd40434504c1d385ae9d81c6448ba5e6959cc3940503009ecca68c41d4dd83de460282c242c406968e 8 (((w >>> 5) + d) % 57)

def qPerm (i : Nat) : Nat := fld 0xba2643435313171800000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0x4762305000000000003a620dd0040a1ef68720cee740000000d00000000c40040400c0003c978ac002ac00a000275dc9a7e9a1da6476184ba5b0000000cd0039800c30000000bf0036572a9002a0009f7193daa4b00261a895699208842002999236002716c320025d6a2e5a24c421e520493c0f4d831220a4b01d20054780c0000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x688 3 (fld 0x4ca5c03880c243322ed706239220fea4 2 (bsr 0xffc6f9c4ff41e8e2fbd0a54cf606c261f4a30a53f2969921e92c093ee7041e37e63d7411dd2668d5c6cca5b0c5f20b3dc424d732c0987827bea7d536bb5677f8bada98a2b9008580b21ff34eaa85e630a31945aa9f9ee1e99c41684c9ad428319876483e95deaa86951f47a69483de0593dbbcc29172253d8dac909b8a1809cf89cba2718924bbb385d02f51856e310484ff0c0179f3338c79431fc0766724c1743f5c48724dcc286b654a0c68d3a29c65efabe465ccde23622f2961561473d54fd401c84c7e3d33494994ac4328b7fa424e10483052afba2624c49e25a41b5a1f1ec26f180438f81538f044106645730dc8155e0ba567900812b114000423c2 32 (hk ys) 7 0 64))
def qOri0 := quickOri 143 4 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 4, i.val = 0 ∨ validQuick 143 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 143) (fld 0x504000e40e20e10e52f10f53104f20506400106e32101f32e62f40e43402401f12e12f42f52501 12 i) inputs
def I (ys : List Nat) := bsr 0xff41e8e2f606c261dd2668d5c6cca5b0c5f20b3dc424d732bb5677f8b9008580b21ff34eaa85e6309f9ee1e99c41684c95deaa86951f47a693dbbcc28dac909b89cba271743f5c48724dcc2865efabe4622f2961494994ac424e10482624c49e25a41b5a000423c2 32 (hk ys) 5 0 26
def test (i : Nat) := checkD 143 scs 9 (B i)
set_option maxRecDepth 10000 in
lemma roof : bar 143 (cutB 9 inputs B) (cutN 9 26) (fun _ => I) qOri0 scs 10 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z0 : span test 3 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z3 : span test 3 3 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z6 : span test 3 6 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z9 : span test 4 9 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z13 : span test 3 13 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z16 : span test 3 16 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z19 : span test 3 19 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma z22 : span test 4 22 = true := by decide +kernel
lemma regionOK : span test 26 0 = true := by with_reducible exact (sj (sj (sj z0 z3) (sj z6 z9)) (sj (sj z13 z16) (sj z19 z22)))
theorem finChk : ¬NatRun (mask 143) (goal 143) 10 inputs :=
  symCutRoot (quick_safe (k:=143) (bound:=4) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof (fun i hi => checkD_sound (spOK regionOK i (Nat.zero_le _) hi))

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 11 ≤ t := by
  refine proveAtCap 7 143 10 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row25

def prefixGates (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x505f20505f10505661505501504750502f31502e51502e20502721502720502620502501501f65501f20501e10501762501710501660501610501500500f61500e61406773406770406670106f63106f61106f53106f52106f41106f32106f31106f21106e32106e31106e21106e10106501106106106105106104106103106102106101106100106006105f65105f62105f60105f41105f40105f31105f21105f20105f10105e30105e20105e10105105105102104f62104f52104f50104f10104e40104e10104104104102103f10103e10103102102f51102f20102f10102e51102e50102e42102e10102101101f51101f50101f40101f10101e50101e43101500101100100f61100e40100e30100e21100101006f53006f52006f50006f43006f42006f41006f32006f31006f30006f21006f20006f10006e42006e31006e30006e21006e20006e10006504006502006500006105006104006102006100000f62000e60000e40000504000503000502000105000104000102000101000000
    | 1 => 0xf42e10f42751f42750f42740f42650f42505f42500f42242f42105f41f20f41750f41740f41710f41650f41400f40f20f40f10f40e10f40b20f32f70f32f10f32a74f32a52f32741f32730f32721f32650f32640f31f70f31f10f31e40f31e20f31e10f31730f31650f31640f31504f31500f31231f31104f31100f30f10f30e10f30b10f30731f30641f21f70f21f60f21f40f21f10f21e30f21a53f21730f21720f21710f21630f21503f21500f21400f21221f21103f21101f21100f20f31f20f10f20e31f20e10f20653f20631f20620f20103f10e32f10a52f10a42f10a10f10642f10610f10502f10500f10210f10102f10100e60101e51f41e51a10e42f60e41a71e40e21e31100e21f41e21e21e21e10e21a10e21401e21101e20f21e20e21e20770e20760e20500e20370e10f50e10f30e10e21e10b50e10a30e10770e10760e10750e10740e10730e10501e10500e10370e10360e10350e10340e10330e10101e10100506e21506671506505506007505f71505f70505f42505f40
    | 2 => 0xf65f42f65f31f65f21f65e10f65101f64f50f64e10f63f50f63f21f63f20f63770f62f10f62104f60b50f54f21f54e10f54752f54500f53f21f53f20f53f10f53e21f53e20f53760f53731f53661f53102f52f41f52f31f52f30f52f10f52e10f52761f52750f52721f52661f52660f52501f52106f51e20f51e10f51750f51101f50f20f50b10f50662f50661f50100f43f62f43f21f43f10f43751f43740f43650f43102f42f10f42e51f42e50
    | _ => 0
  fld packed 24 (i % 128)
def thirdGate (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xb61b60b53b52b51b50b43b42b41b40b32b31b30b21b20b10a75a74a72a71a70a64a61a60a52a43a42a41a40a31a30a20a10771770765764763762761760754753751750743742741740732731730721720710674670663661653650641640630620502501386385384383382381380376375374373372371370365364363362361360354352351350343342341340332331330321320310281280272271270263261260253252251250242241240231230210107106105104103102101100000
    | 1 => 0xf70f64f62f61f60f52f51f50f41f31f20f10e76e65e64e63e61e54e53e52e51e50e41e40e31e21e20e10b80b76b75b74b73b72b71b70b64b63b62
    | _ => 0
  fld packed 12 (i % 128)
def fourthGate (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xf50f41f32f21b73b64b62b53b50b43b40b32b30b21b10a63a32a20760752751750743742741740731730720710660405400387375374373372371370365364363362361360354353352351350343342341340332331330321320310276275274273272271270264263262261260253252251250242241240231230221220210106105104103102101100000
    | _ => 0
  fld packed 12 (i % 128)


namespace Row26
def inputs : List ℕ := [0x3b61db21db0ed92526d936c936c9b649494955b600000000000000000000000000000000000001ff,0x40b7050205b8285c082ce14041670a1717172c0a000fff80007ffc0e0003ffe0001fff0383838600,0x2e0c20617061030e89c304184e1820c3a3a3a380dfff0000fff8000707ffc0003ffe0001c1c1c1800,0x8504285728b9470011408a14ea2751c024bfc0500000000fffffff8000000003ffffffe0001fe000,0x2e61730e4302182009d84ec388c0460803fe48061fffffff0000000007ffffffc000000001fe00000,0x30818409840c20492de06f03ef03781ffc000028000000000000000007fffffffffffffffe0000000,0x3f01f80ff80fc07ffe00700270038012480000301ffffffffffffffff800000000000000000000000]
def vals := sampleTable inputs 322
def scs : List ℕ := [0x1a8000a0a929ca8,0x1dc00250a6294a4,0xd428000a2284a3,0x114000a0a6290a5,0x11400250a9288a7,0x1a828000a829ca9,0x21c6a000a5290a6,0x1dc00148a6288a4,0x1a8001dca828ca1,0xd40021ca528ca2,0x25000148a9294a8,0xa00021ca9284a7,0xd4000a0a728ca2,0x250000a0a9298a5,0x1dc0021ca8298a4,0xa000250a728ca1]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xe0c530a38e1528c055e80ca1860b10c3cdc0000007d02ca0000000e0c590c14de8214ca727c18b03ebf0652dc0c0a540214de3408284614c60c3cd40000008850e9380f2d449ec86aaec86a98dc2d0a5f0a3cdc7e5edc12e6ae9414de7e42c8400e960000005810b6a0e08b1c3eeb50f6e60814ca5e801aa23cd4083cd42af65f0a0459123cd40e0853734ce80000002cb2650e14caac3cd40604594ae2d40e06536932030b3a8b0e0253183ebf4c14ca0000004c801a4218da7e4adc3346528614ca0a0a544e10dc0c06590614de8214de189cd41c10de043cd4060a547e3cdcb09cde063adc44a6dc1c4ceb6a80ca0e3cd416941a66d40644bac84a10dc0000000000000c5edc44d8251f365340080954821c0000004a10a954c2ca6306d40606545e9ec80000000000004cf4ca963cd4083c121ef2ca6aaedc4102d34042120e421216981c0e80d9000000244d0846ec184c10c8063ea76a801a1aee180a06588e14ca0c1c1818f6187e3c1270eeb2400c270000005414c6a616e8000000
    | _ => 0
  let q := fld packed 24 (i % 128)
  (prefixGates (q &&& 511) <<< 24) ||| (thirdGate ((q >>> 9) &&& 255) <<< 12) ||| fourthGate (q >>> 17)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xdfdbabe8b75c00560060ccd9a5611a6a0936bbd700c44a926e0f29c5477d7f8490009133b524289d0b42803ec30ee6001b4673431e13f94d2886990090a3112eada7b7461059f7290bac6cfd6cb56fc834f5cd8f95000038d756d21d00eb3af6708200002b66b8788a1d91d2e80f008fe3d60a7d4683e73b5e8ba2cc00c9a100
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x103ac00000000086c0000000000000000013bac00009cd400000000218be00000000000000000000026708000000000000000011336018200000360800000000106100000430c18ca0000000040b5c0dcc000000000000089c20000000000000000000000000000000000105f072c83984000000000000509640000366b000027b6c000104e8000003384000000007f2d000000000f0ca81658397c0000000000000000000014258000005328e66e000000000000008b210c11c630000005d0f2ca0173269852a3280ca305884399f5cc10c8782f8fafc0000885f00000fbacc23610ae0a6f00000000000001e6a013500000000000000636821bc08b4795a0000141b8085f1e630000089ac08de
    | _ => 0
  let q := fld packed 17 (i % 128)
  (prefixGates (q &&& 511) <<< 12) ||| thirdGate (q >>> 9)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x500000a500000000c300b000003300000000000200000000302b008f00007000a3ba000097920000009a00000000000000008a2fd90000008200f3009f008e00020000980000e58ff30000000000eb00f5480000000db7c300c3d3a6d752fbb8bae801808c0040006f0bd1e8000000e3190000008336c6cb00ee5d5e00e9ed
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 128 else 0

def board : Nat → Nat → List Nat
  | 7, i => if finger7 i = 0 then [] else cpBoard (mask 161) inputs 4 (recipe7 i)
  | 8, i => if finger8 i = 0 then [] else cpBoard (mask 161) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 128
  if table i == h / 128 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def x8 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x4de1cf000000f800006173d04dd50b41110d0aaf4d0003c098584000069530c01c3fac8c007940480780000cc04c8040e1ce9000074893c02300c2d563513e0003803c538c24303d0007934c9105005000aa102a3ca6c500705bf0e6471ef44904948c00024c24b587a445d513139fb8080f7d101bbb9675795bc044f041039d17001d6b05a71100968039b00ea231d41817801d754020171d4530ef31e25e45e01e2d044403228215c00f71501d1c00000f405475a0011405d42807f9665015
    | 1 => 0xd84fca1ff5528070318027b5cb0665bc65298d8d21c101f25300900403203c6c0012bb32c007404b03ee1b32d980b151800c21c04f910000e5080370012d85952d1b5778701d08320335a034c402ba6b70566000c50006000973c6ec02d15e29405713cf12105c1ccf3b7868803d538d4f0240287141000009bf80036d86500971db55041c02e18362707b38430d8ce7ca00005503b8057900251477403c0222d8d15000044001470314a64004b03100a2c001c53271c0009d827a00b04ef40
    | 2 => 0x27b00a189543cd97c0bfb10004000a2190130406010730250f3e800097403a6fc12eea042c571de8f6ce3c00ef0a1e0f141c40648940794368e4b0ca24003900b1801da60014d00e22c00415b68101b4d079100679353faa104cc000080920b17500150e30250407008c013df10f9028d02724b03214d01e00059b3c22454c0e846c03c003d600cc001cc0a031300200035016f126f900146575f00aac25c170ed8427100301604159f2c08600180e2089f5664468a0403ef02ec825d8000987
    | 3 => 0x3a02c992a086150003081481cf70169c008000d30038738229d1e31a11c8000c1205c00602c08b545dc0c630f9004056049c8520039f25f71b0144411402570120001c169b0800095c07735e3000003ecb028bb20003c157306fdd960c08000001aa1302474561007000914b001040000a5230a404303000004000016581e8801761f01403d44535015c6806d1e4082e444011340019ef66c064677d6452684986c010020090a0001257410083bf6302400041400033e72c0025040c55b0d000
    | 4 => 0x19114101138b30418ef1b10025605f700040789002d40616106500054896302c88dc018510001c20130c7807b610b5c002e4002b5708000739000a40cc883f19bd4200047cecd01d00bdc542b4071dc1069545c72402ee35001400000034800635f78b78401386d6740536007c000001d1142150004801d73b66d820c4c229f1510d751d59b198315002b422806489d401db622543a77370186a0f10758018008697415d871c01011114160003742131630192c1c470809931d2053ec00052ca
    | 5 => 0x59a0000c0cf301afa5b4c2c447d6c02412025d80c0540732440c96312dcb0040db0056503c019d6005c443c45c0283d6651dc0540180e166804c003548001741f0043004cc3120051c0016fb80000043404b8f870390b670002f10000a85586c00018608a0003cf59e309055ac82d1be614f12f1012420da400019ab86088590db3516810ce5c3196141b840c00d798f4961c503c4802ea380015008740b430c001600041111500048551c0002c11a114401e500a860bc448001e56c4b20a7d6
    | 6 => 0x1fb02c1a54cc3653805207d102c01fbb900033b3f20004f802278310b02545f7876c6000cf0e40507130261018000700980e8000940f03f008685ec029e188701207009803f1480508c30300500002d1980983c0044000131000d0730e02f00079f3d939220901a0000c03815c4702000dce440ee377d84d24b17b5604850a7000f5970008e00d00aa9bbc27d90038027db4e7ac0780584031004000702140014000004018ba6015f5129655a0770c86d5
    | _ => 0
  fld t 6 (i % 256)
def hint8 (h : Nat) := orbitLookup x8 0 592 h
def x9 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x1cb00470f07e01c410a548906ea310200ee1e005c61710659302f582b0da0b50b207608b520b0f00fa64a32002d400c5604a3e32a33f47301410c2b000d009090a03949f53910608e90e6940de0f03897481020a85e3662af58008f2d0113944d10bde100b7425bd38e873009a002cc8d05850c33328c05070684e0f4414b060
    | 1 => 0xd2044cd107040b3a810c0b0023705
    | _ => 0
  fld t 4 (i % 256)
def hint9 (h : Nat) := orbitLookup x9 2 95 h
def hint (s : Nat) (ws : List Nat) := if s = 8 then hint8 (hk ws) else hint9 (hk ws)
def labels := 0xff003c800e50000000e20035400c80000000c50030800a9000000122004540109004c67a949821e4a84004524077899aa10670040e0a6481185505f0000000df0034800c7003b9f45276915c64200345ba35680a18c250030586226007d4e1d0000000b5002c800a6002e5761a5c05d4a15002c566125803d480d0028d440b508240000
def cols (t : Nat) := fld 0xd5c285c5460a72e08eae070ab839714117350e15a8711d4477141cd51056b184758c5ce2211b9c1723182a3d4231ea0a8ee08b9708cad44655c358ca1746508f528231dc1c46e11ea88d63445d1a20aba308dd188d1d43972223b9111a370 21 t
def rowIx (t v : Nat) : Nat :=
  mkProjection labels (cols t) 9 v
def rr39 (t : Nat) := (List.range 152).map (fun i => rowIx t (fld 0xf36d61611246143eb6ce1611246143e31f2eb61611246143eaeae1611246143e299a59a385c5956964d845c38d68e2d82461460e1611246143d34d34d34d34d34cb2cb2cb2cb2cb2c30b2cb2cb2cb2cb2caaaaaaaaaaaaaaaa289248a281451449249040c30c28a288204102081041041041 6 i))
def graphId (t : Nat) := fld 0x0 2 t
def qBook (w : Nat) : Nat :=
  let d := fld 0x1225a7000008009b8a800513100074b270408c061f2198c0400b0e085400402105892e68388a208d02 7 (w % 47)
  fld 0x18a00182340000ae063190013a0ee6f28a3038239e0011d19f020c2042291a11409c3e0a1007264dd56eb91814a54004a83951ba000041811808039c021825068cd407c50228b94246460823808400074580181ac0cc74503040004c106abe2d59c395065aa280880c30208a29902acc5eb31197a63965eab605d020cd0463374dba3400533629a8cb46002860410c000062811c1cc0d35a0027a10228e4651b0431628b3e52f5073a0c40e50114594c4006a0374b8264622003281bc7405668e50000f407a337b83ba00404b02080000930428f757ba0dc2232a2d9166ca045c22c51a08116eab2ca8c001720001e0800ce 13 (((w >>> 3) + d) % 149)

def im39 (t : Nat) (i : Fin 8) : Nat :=
  projColumn 76 Fixed39.raw (cols t) i

def okTable (t : Nat) :=
    (decide (validCross 161 76 inputs (rr39 t) (im39 t)))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem rowsOK : ∀ t : Fin 36, okTable t.val = true := by decide +kernel
def passed (s t : Nat) (ws : List Nat) :=
  crossHit 161 76 inputs (rr39 t) (im39 t) qBook (Fixed39.index s) (Fixed39.N s) (Fixed39.S s) ws
def stop (s : Nat) (ws : List Nat) :=
  if s=8 ∨ s=9 then
    let a := hint s ws
    if a=0 ∨ 36<a then false else passed s (a-1) ws
  else false

theorem stopNo {s ws} (ok : stop s ws = true) : ¬NatRun (mask 161) (goal 161) s ws := by
  by_cases lev : s=8 ∨ s=9
  · by_cases outside : hint s ws=0 ∨ 36<hint s ws
    · simp [stop,lev,outside] at ok
    · have good : hint s ws - 1 < 36 := by omega
      have sel := rowsOK ⟨hint s ws-1,good⟩
      have hit : passed s (hint s ws-1) ws = true := by simpa only [stop,if_pos lev,if_neg outside] using ok
      exact crossHitDead (of_decide_eq_true sel) hit (fun i hi => Fixed39.atDepth s i lev hi)
  · simp [stop,lev] at ok

def ck := cpWith stop 161 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma p7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p7_64 : span (pan 7) 64 64 = true := by decide +kernel
lemma good7 : span (pan 7) 128 0 = true := by with_reducible exact (sj p7_0 p7_64)
set_option maxHeartbeats 50000000 in
lemma p8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p8_64 : span (pan 8) 64 64 = true := by decide +kernel
lemma good8 : span (pan 8) 128 0 = true := by with_reducible exact (sj p8_0 p8_64)
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def qPerm (i : Nat) : Nat := fld 0x29cb822e5c0a8ee08c77070ab84655c1c46e0539a845cd4151ea118f511a3a82ae7015ab82e29c1a94e0d51701574611d63171518b918c6a8c61cb8a11dc508f5285ce142e8ca0e5c887354447aa2357111ab850711d4237462e45c08dce0735284656a2e71108eae070ad45d1a2352a31ac6508d1b815ac623b91000000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0xff003c800e50000000e20035400c80000000c50030800a9000000122004540109004c67a949821e4a84004524077899aa10670040e0a6481185505f0000000df0034800c7003b9f45276915c64200345ba35680a18c250030586226007d4e1d0000000b5002c800a6002e5761a5c05d4a15002c566125803d480d0028d440b508240000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x103ce34c2ca2481c61440c2040 6 (fld 0x241e8700452bd4d5b9ac0800b194030a0023292721100198a01150119c0510843008c02906010001 5 (bsr 0xfd356f1ef6e89598f389cc02eaec9a74e968fdc8e90a70ade6a94e04ddfbeb78daa3d3cbcbc8cd82c8b110a9c6f26311c33ddce8bfca6579bf2fb6e0b9aafae4b6d3eddfb24e7b36ac56727da3255ffe9836ca2f96b10df38a5599d588a3c458878fa7a584ef97717cee56ca798bb9e87940e06777fadc0165e3f9c265b85c2d641ccac75cf1d879583f712c580c731957b07efd558e792a558b6be055809c225499bbec4f0e61214d99dc424ca69a8549936523398838913613983b346e7c9331cf2ecc2c7b9ebc298b49532544fb592448e2d92085ee49187beddf17882ede12009c670f4f26fe0cdf66f30a1bc6c4092451960379507400e99527007e3081 32 (hk ys) 7 0 64))
def qOri0 := quickOri 161 48 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 48, i.val = 0 ∨ validQuick 161 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 161) (fld 0x401506000e10f10500106e21e53f31f21400100 12 i) inputs
def I (ys : List Nat) := bsr 0xe90a70adb24e7b36ac56727d8a5599d57cee56ca580c731955809c223613983b2448e2d917882ede0a1bc6c40379507400e99527 32 (hk ys) 4 0 13
set_option maxRecDepth 10000 in
lemma roof : bar 161 (cutB 10 inputs B) (cutN 10 13) (fun _ => I) qOri0 scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x8a408e40ba30be306e2082217a218a21910286219730977095001a207e2195029f649f319f549f342e139f309403910395033e139f419f4094049e548e219f2056135e131e209e3195076e219e4194003a603e600e534321472145004f7640004f2645034f214f634f614f644f6044062e644e7641054505410245023e624f134f104e614e714f434f4044044e544e644f301e644e63450741074e134e434e1444004a404e404e605a605e609e604a304e307a0156037e015e03be10b6109e30
    | 1 => 0xc4033401cf42c4048402c40076027e0222215724262157705000550355005f645f542e213e415f405f4354045e545f135f035f105400bb204b30100015001f321f421f2014021e32140026032e0305060106b710b712b717b713bf10bf12bf17bf13b500650075076501bf736f62bf726f61bf706f60b40764066000be17b617250721076105b5066505b507650661063507310785076f21bf306f20b403640255075107bf206f1015071107b4006400ba20be206e10ba70be706e6036033e03
    | 2 => 0x7b0100000f0104000f210f317b218b31530304010e010e215b033b423723272393305370937077014100910001003b6077027f0105007f027400510081003100bb7027034b602704200025032f032f542f0424009b302100250037033f7630003f643f6035033f6135003f543f403f422f413f0334005b403a403e409b4026042e041b207f218f6485008f308f318f548f342f138f403f138f418400570382308a3086308e30bb304b4026017402cf64cf32cf54cf342401
    | _ => 0
  fld v 16 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 161) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x773d179d18f90f93f76f0001875269516500004ee11fb16cacd12faf7488519540000d9042645530f342cdd3b4176c6b5b9d536ce2f21e15a992832871307def054d00005c7004379e3407225d0a509b0e8ce3390dd566e3e30f7052000059d44b5f114288dff48e55ccd87a9418000ccfd39f4d0c195a541ebad837f18c24000059dd6a6269a3dc4a9495a4edc4470e47960412c00037cffcb083400068b8000f32ad3900f10f4
    | 1 => 0x3b4d29c5f556f3301643f44dd992cf9ff08347c32fb8e534a4618000afcc000a0a401a493524ff5d1d4be08c000009d0fc1f8400027c9c95fec93c3e06edcba74456324ad1dcc33e40c14e702900016344eac00010c400066073ab0002403b39967a2bd80000423d207601ae47f3dc106acc000706000073618365db842b5e760be3d747dedde9e7a0000400000000050e85dfea8800015c4000c9100001df2225c897e670410000
    | 2 => 0xa7fc000bfeffda0003fdd512864923d000087ec6600a98000de588dc3afd6e1f8be643df067989e680000cc796242a3641e3ff55d597495dbfec000d63c0000000000df8844a72adb1b0b159f422d2bee12f6d3100000006076f615a6d3dd44d96144bedf9f0001b84383000000000009624a34218c000dc70000cad1a410000000f4de56216a65f440acd5150f429dc6026787ee0000a45e8c200c51f48c146fb6a116ba51e2d5b
    | 3 => 0xf7b014915d80008e8be46a7f23d9ad1adfe2c6a2ef5a44000a76525b6c3d30203c2c37c97c0004b200000001446220400080b2c5b5d08000d5eb53fd94800000522d9eae33af58ac46d0001ab6018134590b4000347efc359952575ec18cb5906eeb3f9fa4c4370a29b9a000000000000b8fa5c5bfc0006d78058da70000a7fb38700006c7739c0002f5ffea53ed3f45a5cdd908785db267c06c0db4f340000000cf00adf2d038e6
    | 4 => 0xb1c864000038bd11a000040800003d55c5dd39bf29c3edae61d8c000a616214ce6d0df00015cd54e631c7c941fe009937c1790000c28e762433c0001bb05cfa6049957c454a30c0b086000311c037800060a92067a141ae372dc2100011d3b416bfe14d682b5fd8997192b58f542d959b35bc0040fe72f4e25f60f31400060c76e025880004c7c0989fab09d29e03c3d404315bdec000a4535d03c2a1e10001e832b38ad40000102
    | 5 => 0x3ee0000b7a3c194aa7e9c25c1423bb2e868b00ffae00011613c85b66bbe80005077d8300000008aa13b981bcd170000000d6fa68247845597e0c0002084b63e698000022f6c5b0e722e959d20d701e48a00000008e200001db8000473893300000000000000ce95f22000000000000170000000bf745a4e2cd6e26bd178f5ba7bfc4fff58014980004e85f4012216399cc1d1105600003987e257c740000000ce1b6fde92abcf983
    | 6 => 0x2997760001a3e1622b08df0528a4c6c6f1e8726f15b79bdf0003b01000168100012de000291f4d32d9d00023eb972a5850001aa404a800023aeca050fc00026c4a0713942d4000165628a455affa81a72fdd78059584d6fe3b9b949d00001c40238c818000986b2318235b450000cdf00001415aeb5d03458c058ede78e000088e02185adaa69231eba3a8e0002071ace4d2763ff965eb5de49623e4c30000000be91ea6b378049
    | 7 => 0x3106217cf1f4f0c0004047c9243b80590001e450000000345b6e6b876f184b1e314c9bb7160001a864b6c25d2dff4d990b209b00009c8053a80f5a8c000f823bc80000967695457c0002c980001b1649f8000b128000ce13f03000122098fd7c67d1564e8c18000e159c6026b8000a4811ed3e61dd8291f2a111c9ba95d1d8b6000082c5f4827b5350a1a000304c0002cc3169dd2d3c78000d6563a56e5265259fc97eceeb69a
    | 8 => 0x9fd0d372bf5baa035d79f000250f0000000419a3982a4ea9a3e62882e8b40000000000000162ed995455000091b4cec5e1727f502355c0a5820965e675be63cb9174c000093200037ab3a79fa23eeb8fea15c5b3bec950e5e38597453eaf2f1a2ae38c68000e0b34292f159d2df650bc0000b2e0002867b03c48a3924000187800ea0eef495e77a3fffc3afc0000250000016f39f7015261b3c7d1820d6e53cd1f90977c7d154000
    | 9 => 0x2c9f9a30c4c00058b414c13417db84bd3b526c90982ad95f2631a1382a6c46a2988e2b0745147000033c00039a2d550000f64eb3dfa7e9490b1889a11f00008ae40003ce671978c16d800000002d22f1c3612ca15a294ee3bc946f4bac00000017998ced4df6e9bd392fc410f00027880001d3c00003541783a6b4b34feb747c9657df14deb332cae0000000000000095300000002823996d7030001c7b000000000027d76714000
    | 10 => 0x52000000002f4fc26fac012f55c0527c000df2c00038b00002794b4b15736a5042c000359800026952a00000861928248cfc8156c7db000000025dd00000000001ab89014ad15a52cf17b3800038fdc59e0c95060000000ea580002170000cf85872dcfd826032d37c2623cd46f4c000af8c7ddc119bafb0d32574bd92882a0c00080a71b5a37001023604d7265561400000000001e370f4c0006b6c00049183f852c858caca253e
    | 11 => 0x5ac0c7071b84a90ec34e316d13a820a9ceba8be1ac5a380008f3c0007ecdc02d86196700000003ed04f80003144fb7cbae0000000d68df2c520c0000c97ff7000131700000000000446ca18000491fc3347d00009dd038f1ef0d890003d7ef7d3724b3780000003f82c18cd88a7055bb108f731e2c40009fe0000fb67589a9dc0a0c47c0733498000b18865c00000006ecf3f3272dbc3000305a48b360d03280001213a8acff0000
    | 12 => 0x3bed777a06c000f55800052044b409536285b7f783b298000969d2d10002c8a0000b9c61e0000d4b000014af51cc3bc94300000005e84839895c00000008ee0000f5e0000000026c185f3ec66c00014904936f560001d9b181f27f045620b5433192e232c0582b8000dcb000049f8ef401baeb6a530000ec0028c48397e5e86eee255041177ef463c6d2c00014a8216313800069a430494e19e7d43c00021701e2f16a8064a8eb6d
    | 13 => 0x7e3d71978221945c12d370001ee82d04c21dc58000024ef3536b4e3553a400000022f559380004a4940c313e2d94e529a200010eb
    | _ => 0
  fld v 14 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 426 (hk ys)
def qPick1 (ys : List Nat) : Nat :=
  fld 0xbeeb6caeaa43a279a51ca3e48cc88886035f78e09d7056da6582d75905445014d2251180 6 (action2 ys/284)
def qOri1 := quickOri 161 48 inputs qPick1 qRow qWord qBook

def J (ys : List Nat) := action2 ys % 284
def r2 (i : Nat) := bar 161 (cutB 9 (B i) C) (cutN 9 284) (fun _ => J) qOri1 [] 10 0
set_option maxRecDepth 10000 in
lemma rp0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp12 : span r2 1 12 = true := by decide +kernel
lemma secondRoofOK : span r2 13 0 = true := by with_reducible exact (sj (sj (sj rp0 (sj rp1 rp2)) (sj rp3 (sj rp4 rp5))) (sj (sj rp6 (sj rp7 rp8)) (sj (sj rp9 rp10) (sj rp11 rp12))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp0 : span t2 63 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp63 : span t2 26 63 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp89 : span t2 26 89 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp115 : span t2 36 115 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp151 : span t2 31 151 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp182 : span t2 22 182 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp204 : span t2 19 204 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp223 : span t2 42 223 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp265 : span t2 7 265 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp272 : span t2 7 272 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp279 : span t2 5 279 = true := by decide +kernel
lemma secondTestOK : span t2 284 0 = true := by with_reducible exact (sj (sj (sj lp0 lp63) (sj lp89 (sj lp115 lp151))) (sj (sj lp182 (sj lp204 lp223)) (sj lp265 (sj lp272 lp279))))
lemma upperDead (i : Nat) (hi : i < 13) : ¬NatRun (mask 161) (goal 161) 10 (B i) :=
  symCutRoot (quick_safe (k:=161) (bound:=48) (xs:=inputs) (choose:=qPick1) (row:=qRow) (word:=qWord) (book:=qBook) qCert) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => cpWith_sound stopNo closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 161) (goal 161) 11 inputs :=
  symCutRoot (quick_safe (k:=161) (bound:=48) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 161 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row26

namespace Row27
def inputs : List ℕ := [0x8d8846c4de36026c41362679b080769016d47c000000001fff8000000000fffc00000000000f,0x16290b149038a95148a8a488c553eca27cd4bc4000000000000000000000000001fff83fff0f0,0xb8305c183840c4e18270c1c1063808c70098c8bffe1fff0e0001fff0fff870000e0001c000300,0x21425ca3c085008a12751e022820311756e30100001ffff000000000ffff8000000001ffffc00,0xb98790c1010604ec3c460804303abe1c0702023fffe000000001ffff000000000ffffe0000000,0xc2046102260816f03f781ff7c0c4c00098001000000000000001fffffffffffff000000000000,0xfc07fe03fff01f002380113800870000e000203ffffffffffffe0000000000000000000000000]
def vals := sampleTable inputs 308
def scs : List ℕ := [0x1f067234a52749c,0x19c1f0c8b3280a1,0x1603207c9f2689b,0x7c0c19c9d270a5,0x19c0c1f09f26c9a,0x2345807ca1280b3,0xc80c11ca02709a,0x11c0c19c9b2689f,0x23432030a52689d,0x19c0c1f0a12709a,0xc81f234b327ca0,0xc81f11ca526c9d,0x19c0c11cb327ca1]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x4542c0802535e861f2cb26572de070238138614ca6608190452126a9e5c0a3c950e542c5480c90e52c80842120e02530e4a9546d0120e005364061854801a0c14ca0c42b3045e1242861f0a3c120e5213040c540e5e129c5e924c861f4c10b30a44ed0e82f89c5e12020253409eed060a550400530e3c123e428f2a266c2440be0a38139c42123e0212243ebf6a9ec81a4ef03064724ef4190452136aae120e0a537e52923a02120e06530e38137734ca043c1236021204048e5e106d65441a0252920c0a552738535f16530606597e5e924896c8549ec8549612488a64025e9254106d0404536a9e12080453568a645714d04c348f6b16531696190e0c535516530c42c80e0453080e240242125092ed0c4ac84d16535804af0200536a26ff0c42fb5c900a0ee08b0e44ed50c8c246ae6d5515026a98120a3c6d7e3c12804a134626ff064a950a04539414ca00000058941746106d3062aa0e24190e52120a5e124716530244ed065e12040e580e02292f002d040a5508542c3edc88085e92
    | _ => 0
  let q := fld packed 24 (i % 128)
  (prefixGates (q &&& 511) <<< 24) ||| (thirdGate ((q >>> 9) &&& 255) <<< 12) ||| fourthGate (q >>> 17)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xd3a7b0f6cceab6b43cceda778ec6a795a466baa85c54b736cc7b09abd280569b997ff3b09d58d569db1baf79215090abcecab9342b24893a6e6715842fe8a2c2423aa5ca8483e15459242cfd89514facd1d4c4bf5037f02db1cbbb02f02b4055ea65871197d9aa730836521d4a7b100017ea9efb222e142c78a3ba4d808a1609
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x2b809ac5258ab046180650e9c4a6367a59083326b200cb4025c0000039812d79405458163f3241d16ee2d08598b4682190048e493818b1c000148550849041900cb8f25f027d8144c205c00005c15349b478da0000035daa0bc0d9010b908303f981dd86102d0000014a489da3e72255e81a4809fa0461088aa9bdc79fe0e5f87303b2e49a5658d01d7b10be505f80000072e15408000000002f5900000759a5e8f862fc0184797a2ac0637e03152199c14ca2159be0b4066a110f4b6400000a858f6c90780041bd38c004bc1a4780000099102cb3b9cab46020da0230035980001622a00004f7f01bec95f2e26d7a653eb2874e496b95736aa19098e600004b873eb2e04c03ecd1f7b29be80000946e
    | _ => 0
  let q := fld packed 17 (i % 128)
  (prefixGates (q &&& 511) <<< 12) ||| thirdGate (q >>> 9)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xa082a0dec5663aba4850974e00558f1bb1d557873e9f183656eb00faa772f5526773b000790b7200b50d337c81469d5e0010b96d23d2acf0a2b926e3547fcdc2f996d00084ab00000c00ae5806c1453d532bf3bf247fbcb1e300220b9deca54999009cb9f2e68d804700eb00bd0f1728a809c0ee9e136600d3de5d1c97cc00fb
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 128 else 0

def board : Nat → Nat → List Nat
  | 7, i => if finger7 i = 0 then [] else cpBoard (mask 154) inputs 4 (recipe7 i)
  | 8, i => if finger8 i = 0 then [] else cpBoard (mask 154) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 128
  if table i == h / 128 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def x8 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x67c40e7c0ee000fcb113f72300228b1286af680bc250640a5004a770b7a00d900583be200003098a600ab1057272708b0006300900a96025c3179216c5b07837926d00ec09ed0580d38a859a0563006715b0b40f00100d1c02340401e85030d44444f0f03b3f295708002020c10705cbcf2d07080ad00e0107503995dbd37d38
    | 1 => 0x1604110f360f069fe0091d0000f12cf98e2d10100064c21b5074cc06d7a40e673bb6e481ee629e350d0e0605a07371bde23bd15ae307b30ce0f01bc0110c1416420de263f00ad03f7b0020d000cd54c006a850a06350c40060e1b3800697507102e7c2c0285071319043055082180125ace8a217ec2e4f3ae726061f46003
    | 2 => 0x3cbbccf0be60d99d0a7c6d0c00a0d117708aee66460b0a0c9c0a00fe0d0ae309d1a40030d95a40903690e0686024fc28050960e6a25a70911050d879055503230c1cb20807f94013043200b26841ce00400cac389ce04f3e0d73010d182b5cd375307103b0712cb03fd8a48296075031172dc0c2449d064a20c005b573001669
    | 3 => 0xd6eb46001212f55bab03680000b0b1571d1a0b0f040b580052a4b0fc1046a69286ac0c00b19efc4973667cf093d54aa905b02b36203e0263070cc980208f519d00600886cee6df6d11106096ca00cbf02d900f150804d004d20a44c27a2410413aaac04a003571b6308ebd1700922a3c790e04900920d293652c207d34de5fec
    | 4 => 0x497180b0ec72ca4000f0411310006ca4d84e0769b80be1957d902197c0000af47c75260000483f000b9f682e90131c05fd2dc0a32e640e0312677084670d064c0462f070480f49005d76001e6d31802f800deb126b91c933104703c5d025cd2dc03001a308b017c029211071d008cb6cfc0600b0c3004700891959f1056bc1e0
    | 5 => 0xf9035007e0049cdfc7a2033343f0100048b005510a2a86416c00a3d180130e66c0a7100f048e0c6963002aef0c642a8ef071460084e0011c13e03119c50de424ef0d082185a9910723d32164730b8500171a19030707be37fa06045587d803c97007001a008da0cdc0bf0045f0010019264588bfcb3140093019e007f004b4e
    | 6 => 0xe4380204b3f708410104a7249310a07f76e254350ac09eebb58a8c1a69e1320004bb063a3c0e9269902dc2190f95d00170f1f180ce60c7fa21008410f071b660ea6ee0dff2457a0271b940d90610041572f06d55201460ad00000704d931f8e000b05f391c100e003521a8f4c12130b00fa0000b7026b603801ef29060444762
    | 7 => 0x9b00a1afa1fea500315b585220204d420072000e5395f0ef201d9dc0237d31907a018060f627c70020e043e590b5d032bc006ccd0a00c0006a1a7e500400000ec894100780d1c03e26300000b0501fd0007f59073020001165f0c080ab63200b09b00b0d2a9f080005839748083f08a00200e0640cda17001cd650eb012f0ce
    | 8 => 0x24927607138b0909007a61083b8f05b82b5300bbd76dd0ac0a0826c30768c4400820180003014030e6d0010ee03408915a000f40e0d6260a50a0e0f71a0cb3fa756c2d909560125f0f7fdc916e5030cd41edf6df217107b4a0f5000c0710550e7084d000dfbb3e0b905f7104807ac01c41000078b5200cce001ee7f81a580d72
    | 9 => 0x80303902fe00ab217b30043c05600e73604a22227094e300003ae441d0209c0035c2002a41a5d5b0b067d70e9a8087c009
    | _ => 0
  fld t 4 (i % 256)
def hint8 (h : Nat) := orbitLookup x8 0 801 h
def x9 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x21f8d903001da3051e3640318a000010e0401b031052b3053ed08413f11027e40f3e287301430090300d0e0c013416268dd23102275d7301061b07001096232500423010201e00d9901344b0545fb303f166180132703e0957512f700011a6443852701032fb010107074405067aed01024450505a910058400a9f53262c0605
    | 1 => 0xc000e45000520a0001022107070013300018b5575b360453d6603731121339813140005005070210a0509b20d31b2033b740b2f61031010c20a30a0531a07bc0007436d0600b550070038c61d030b0204057536f024204d366600790d0b03102014738e57eee00663d250e522301892663c101460b233171306232007a33200
    | 2 => 0xb4202306570410d0200226004d003b02b313f07a7204140749012381327cff2520750c460678eab34004d19760d80210fdf2b7121640410206111c17c070e700a4a040026702102152619100d0e0004ca0e175019250000416030060f10e01de0315750060b6100108f57d6820dfb17f4a707833001203024064132010709700
    | 3 => 0x7e2172400d304602520618651f04e0043f50500040520723a0097004250140700000619bc07010ef723d02507c12d0468200759f052d2027480c7044262d0a378
    | _ => 0
  fld t 4 (i % 256)
def hint9 (h : Nat) := orbitLookup x9 0 299 h
def hint (s : Nat) (ws : List Nat) := if s = 8 then hint8 (hk ws) else hint9 (hk ws)
def labels := 0xfe0000000f10000000ed0000000e00000000dc00001b2b3000000120000000114004c25e8d0031618890047e3c7c002ca167800442147584a84ce650000000ea0000000df003e9f2580030dac54003a5d047002c1aa430036da84069a8064300000000b6002b800a5002fd8e2d5f07d3a1d002ad681a55031380a0027d36084d0100000
def cols (t : Nat) := fld 0x152e0cab307ab888b9c444a5662547308cb83b0acc23660f58d10e5c818f540dd1a223b90362398 21 t
def rowIx (t v : Nat) : Nat :=
  mkProjection labels (cols t) 9 v
def rr0 (t : Nat) := (List.range 204).map (fun i => rowIx t (fld 0xd30b289a56091850f2c2aa268d8246143c70a689636091850f0a34c28718595246143cb0a1a6164c91850f1c28658553246143c18c2ca1c60e3491850f0aa869838b246143a182461460c91439249249249249249228a28a28a28a28a286186186186186186081451451451451451449249249249249249145145145145145141030c30c30c30c30c30a28a28a28a28a28a208204102081041 6 i))
def rr40 (t : Nat) := (List.range 162).map (fun i => rowIx t (fld 0xf36d62611246143e32c7cbad8984491850f8aa99a5c699638984491850e271657289a6164d124614361170e36a89a61138b2461436091858860d12450f4d34d34d34d34d30c30b2cb2cb2cb2cb2ca28a2492186186186186186181451449249249249249249040c30c28a28a28a28a28a288204102082041041 6 i))
def graphId (t : Nat) := fld 0x1400554 2 t
def qBook (w : Nat) : Nat :=
  let d := fld 0x65901449b063a03001e531202200100031106be603e000402161015010505b23d090204c90b34041302030c660018360007015e671f05 8 (w % 55)
  fld 0x4460ce062d59cf8316eab781866c504099189b828a64082b8f86d460728a4c3065ae023bd0452cacc0010004000b461ce420493c5c53e9801418a000069b119f16a9306f023453c44172080006847c1460ae4ca82f9364e06095ca00046283521161dc0000a381dc0ce46e874c52a000723000c13cf9c3613a0c1aade50631304000ad31460232084000041931433a84146183715382425ee824c13a5a60032e0d5dccdc0e11704194f46641825011404616e3909d165a58498101b043dd0212a7438a0001e99f09184a42740bd095ac08e84e2e097b80cb2e11d0408709d741030812c6c166f420a10639d0c983101cc29c0001271f04acb2a332741041c15a11d09882641369ae700820000663a4c0881dd1cf1b0d0840956a1029810a0dd6a0821078428d000322c0004c300000017a67dc0668a2c93b04174ea371f0218166ea91868c09c060870c11664200000015bade61e1ab505283931ee37b8dba4dd0000f14a84d81002011559aa4106b000014a0001232b545a68d3545ae7400e241043000053a746 13 (((w >>> 11) + d) % 241)

def im0 (t : Nat) (i : Fin 8) : Nat :=
  projColumn 102 Fixed0.raw (cols t) i
def im40 (t : Nat) (i : Fin 8) : Nat :=
  projColumn 81 Fixed40.raw (cols t) i

def okTable (t : Nat) :=
  if graphId t = 0 then (decide (validCross 154 102 inputs (rr0 t) (im0 t))) else
    (decide (validCross 154 81 inputs (rr40 t) (im40 t)))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem rowsOK : ∀ t : Fin 15, okTable t.val = true := by decide +kernel
def passed (s t : Nat) (ws : List Nat) :=
  if graphId t = 0 then crossHit 154 102 inputs (rr0 t) (im0 t) qBook (Fixed0.index s) (Fixed0.N s) (Fixed0.S s) ws else
  crossHit 154 81 inputs (rr40 t) (im40 t) qBook (Fixed40.index s) (Fixed40.N s) (Fixed40.S s) ws
def stop (s : Nat) (ws : List Nat) :=
  if s=8 ∨ s=9 then
    let a := hint s ws
    if a=0 ∨ 15<a then false else passed s (a-1) ws
  else false

theorem stopNo {s ws} (ok : stop s ws = true) : ¬NatRun (mask 154) (goal 154) s ws := by
  by_cases lev : s=8 ∨ s=9
  · by_cases outside : hint s ws=0 ∨ 15<hint s ws
    · simp [stop,lev,outside] at ok
    · have good : hint s ws - 1 < 15 := by omega
      have sel := rowsOK ⟨hint s ws-1,good⟩
      have hit : passed s (hint s ws-1) ws = true := by simpa only [stop,if_pos lev,if_neg outside] using ok
      by_cases h0 : graphId (hint s ws-1) = 0
      · simp only [okTable, passed, h0, if_true, if_false] at sel hit
        exact crossHitDead (of_decide_eq_true sel) hit (fun i hi => Fixed0.atDepth s i lev hi)
      simp only [okTable, passed, h0, if_true, if_false] at sel hit
      exact crossHitDead (of_decide_eq_true sel) hit (fun i hi => Fixed40.atDepth s i lev hi)
  · simp [stop,lev] at ok

def ck := cpWith stop 154 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma p7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p7_64 : span (pan 7) 64 64 = true := by decide +kernel
lemma good7 : span (pan 7) 128 0 = true := by with_reducible exact (sj p7_0 p7_64)
set_option maxHeartbeats 50000000 in
lemma p8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p8_64 : span (pan 8) 64 64 = true := by decide +kernel
lemma good8 : span (pan 8) 128 0 = true := by with_reducible exact (sj p8_0 p8_64)
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def qPerm (i : Nat) : Nat := fld 0x72e40dce2223b9031ea81d5c4439aa06e8d1000000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0xfe0000000f10000000ed0000000e00000000dc00001b2b3000000120000000114004c25e8d0031618890047e3c7c002ca167800442147584a84ce650000000ea0000000df003e9f2580030dac54003a5d047002c1aa430036da84069a8064300000000b6002b800a5002fd8e2d5f07d3a1d002ad681a55031380a0027d36084d0100000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x6543210 4 (fld 0xa1c3269301086009430000c2b222cc10001411c7140c2088 3 (bsr 0xfc4b4dc4f92dd3dff61fed3ff211aca1e747446fe5011aebe0c65e1ee0bec9a5dd5f2d6bd98f9235d6b3f50ed4374c98d2d8af1ecfd00ed3cd66fd69c8b4a9cdc5c11f1dbe262fe8bd9611c6ba26cfbeb6dee1a3ab7077f8a746b738a4ed92aba25f850ca21c1a76a06890169d0dc8ed9bfe408f9a3d9b8f93f46c539100bc9787315ce181ddfa1c7a807146735658f171e68e7f6606a67d62f503dc626c705560bc372c5e96bbfb5d5c0b5a5c2e1b595bf34bc35b35d66658b7e884572aefb653f30f574f30a7ce4e426725445164e537c9eea53440a5903382a54727ac431823b384ef1e3d14911c63350c17d8839c13487c1407fc126d07c8c95c072bcecb 32 (hk ys) 7 0 64))
def qOri0 := quickOri 154 8 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 8, i.val = 0 ∨ validQuick 154 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 154) (fld 0x102f10000502400501e50f23402f31e23106e20e53f53f43101e43506e30403f20e10f30 12 i) inputs
def I (ys : List Nat) := bsr 0xf92dd3dfd4374c98d2d8af1ec8b4a9cdbe262fe8bd9611c6ba26cfbea746b738a25f850ca21c1a76a06890169d0dc8ed9bfe408f93f46c5360bc372c5d5c0b5a5c2e1b595bf34bc35b35d66653f30f5723b384ef1c63350c13487c14072bcecb 32 (hk ys) 5 0 24
set_option maxRecDepth 10000 in
lemma roof : bar 154 (cutB 10 inputs B) (cutN 10 24) (fun _ => I) qOri0 scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0xf322900154a0de605728378109480de035f201390222031b213f28c5c862a011f738fb947dd63ee31f748fb84501e20011f248a80c540d3c471f238f90c7c823ce51f434731c398c5cc31f407f31479d23c4911048a824441a2a0d11028a813b98c1cc31f501f311b98e3ceade638f98c7cc228071e738f21c7c417cc31e712f39339863c464e610f30ab88e3ca714008f381a980dcc0ae605d302f9823c804a6027302b8c23ca11e3033021b81034804e300f204a80434612e01a30853840dc06be302f08158409ca01e30
    | 1 => 0x2732104108a084105228293c8c1c423e022529139489c844f3127981100c9c864f102728939048a0e4107273191000b4805e4067180180c1c0611020b9085cc02ee015000800054083ec81f540f9a07cc43e60140308818540c3e840e310fa0050103ca81e340f9087c403c62150708838790428000a6007301f94d4ea0962152802bdd874c0af265282278855ec8af634730abd955ec0a40657a88b9915ea0a405573b2b995420aa5055081294095e280e621f301b9855ce2ae5157a1abcc14806ae635729979d5420e4e62
    | 2 => 0x6281b0414aa0cc5052a83b1419820c5f5367a10141c020e5f5067a00d41c620e5e653083979159c685f32679097cc19e40540362011790d9c645f2067881500988025e42588395000a2025a302f1833881d4c0ee602d38179c19cc14604bf01d3810b4a05e50672016880bc40ce10a3015f8069c04e6037701da902dc8096034f0190404144241032398104080c42474023a811dc08a004f761b0113d949ec84501228193d888a044f6327b093d80880c4e7627a993d0c9ea24f5227a813d50880a4f42172093d0088084e54
    | 3 => 0x15109f8856e60bb621310add416ee0bf7658002fd896a00b5015a81a794d7ec6bf615fb02d0197cecbf234729afc905c42bf205f312c4096a04bf430720afd007c846e535f122fcc57e60b4035b11af88d7e20b400288130404a20671062b8815c4cae2e57152b8915c50be205f132f8b97c54be245f142a8014000bee8cf632a8131404aa06c5022fbaa441cbee6cf622fb933d84bee0cf602a03b101980005e172b0b97d0d9e645f40679817d95020e5f45679a0941c420e5404620197850ac285e7467319441182065504
    | 4 => 0x6faa37c91bea68e516fa937d41a80adf21171237c81bca4de62688135409be28df04072137c0c7c806e516a001a940dca0de509d904bc493e876500b79823d0e1e862f317f995840e9e656f40778983cc47e646f436fa1d9001766091004a80588c2d4616630b71816cc096611b3013018b80e0c090e04430223810b640ab303a00cfdd80c033f639a804900928073f629fb04d01a7ced3f324201c100c4802f4029f31cc40e6a06e40302008d008c806d4039f904d00a68007e0193014b8090c068e038301c380c4442b101
    | 5 => 0x7aa03d081e8204040082014101e060f23020019c0c04a00a500328039417680d703052003900b6a01b408da80fdd80c043f651fb20d4086a063f601fb18fd88680c3f531fa18fd487ea03f541a028fd004808340418820d4107e0604021a00498125c08632133a819c90ce42672533b81bdd874a06f65328199410dec26f6032801bd90dec66406373b1bd50de426f5137a80b950c80a610532829bc50de080e5237818f940c8002604170236c85ae42df761d2037d95bec4d5036a8227945bec0d5006fb237d8da80cde76
    | 6 => 0x7a81a5015080aff0412013d0010c0a8e059301cb80d2c0c9e064b02a781514c08e6085304398054c02e60a38251c0a8e2151029081a4415020b0102108153c41e20125034a82a14160a0425027a805fc0e9e097f01a78150406880021001280404020a008100428001c0ddeec370377b2bbd91dec0e5037280a7c51dec6e50077a83bd45de80ef41478a3bd51de842f43720238411ca08ef03720019c11ae08ea5077283a901dc800f76000003d941ec8050107b00140c1ec40f63028003d841ea60f4307a003d401ea20f52
    | 7 => 0x50800440082011b700100a2d812e0b2703588002d824e0d270293824bc04ea012f0392814bc1a5e052f04920027dd876c09f064f9327c153e0695044a001ad81b6c161006880184000200bb60708016dc096c12606970321c11d68027032da002d010e0a0b5047bb0ed411ec08503428223d851e088f054781a100096a0db5055b043dd876810f6587b043d8a0a0705044fa8c3c121e070f5047a8c3d4a08006b508528439405eec200017b00bd884a02250317b20bc0c5e462f0417aa0bc9048004b400d982ad4236802602
    | 8 => 0x710105a898c0cd6072b013fb29c000fea47f023a809fc14fe027f033a001fd4e56c27f513a029f814fccb2b313fa19fc8c420674023f011f948e20475027080bad44c608010318819f80cc2086b043f11c9c4ad664e713599810cc1d6840b420391c2d8a16a46350139189c908680133051a821c8c86a0b3504b9325c8cc6e0437059b804dc0b6211100
    | _ => 0
  fld v 17 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 154) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x5355e2edb00008db4409150dc5102390951c000ebdf78d0d931755a2cce0f48a0511b1afa20000b1d11080008cc80e9cbc27a74250134800001faa87aeedd922117fa32e1ce8f1f08ea7f4000f6af28ec6674cd733a2c708000d9dc189f9c000efa1b58caa5560006c63108000000936dae8b5be21989f4b8a20bd508c80013f85f70e179b8000000b9812f0001ba441308e54383557d59d300007c3
    | 1 => 0xd0ea5979d207c0007d605da7923fc66e40013afa1d6f44001bbc9de80017b539ac268f50869c188bbbfd387220900074b38b2a82976011f9f89c91880003e0a3e5bdb000000164a78d52f00004b1259af0e16546c00053f4001a91326e3537e37a00007d9000020bda109a406a2b903780010235f300066589a524907a9d75004f890961b10000000f3eb5b0000373000219d29174168b99bc108000
    | 2 => 0x8dfeaed4da7aee13253ae8c0000441d9985256d107000000000072926f8b7a00000026b26e56921358002b50387103a2c8000120ee562e2ef266687d16595984fbdc70001f300005c40f5c7811690005aec4a0000f34fa721ffa9200027cb013092e3400000009be110840b8c8050335ff598866f11b82845734000720614db121df75700037ec000d6c60b0001247435b74c12e6340000001d2737e
    | 3 => 0x3ccc7513d187ed6a0218afcf7626b02bc00310ce8d80014cb77427c3f562280006c060266de0503d986a67d300061112764ce0000ddc0010b10ff000000143feeb27efcba2a037dd920000d210c9dcbd99d35f58e8468c781a9c47360572732aa7f8df8001af2f498001272f330007fd01d90bed4f316fba2725000129074403302c80038bd9a3000236a121281c24a9a58a0e29263c78e2bc946
    | 4 => 0xf70b9171a1cb100000023033937d6014800199c7f58000001e438b5d9c436e38aa9b6e642be00000052bd6bdab900000010873b649880000010694b06bfc001aa5219d7fbdc21910001ce771a19cfbe0db71101d80000001830c6800035d4000376dca59e019d930a9dd2dd936000411000024735100004cd2f0fcb000543800115d0870000000558de7e2f40017767e2e21896eaa100045e63d2000
    | 5 => 0x3bef0a80017dd3891434fc000096d29d3d500009268002889aa8000545e7fc00000016e1f421da17e0634ebf023da2093ec8a4db46b4efc0004c7f7c8e18148d4fcac5ce78785e9ad880003f000000000025e600012f93223031524a992ec5eeda4650c103f55aab00006a400006072b41e0dba0dee4e712c0012c21a07c0dc42c546638948b356ce0f3c96020679200004908c8259c08d7fc4e2000
    | 6 => 0xf850a4eb2a0000000003100000f3b2929b90000b6dc968001acd0001ece18121e000771d9974d4a0a80031f928065460a0500ca4b2338385a42030587f29cca8bc2c52cfc00009afd112b239b422e5535200000000007378001f2b0001b2400053b4873c06e0cb11253871051501ae596ea8000cf03ab6b61aa30dc4c58e5d37802b2cb81112fa0000003541c56cab0000001286ce0d705da38e1fb7
    | 7 => 0xbc60a7c02297d0001c86f5e71ec00dba572e5d756b43276ffe9300000001e17640000b649a4391000000000000000044901299b04e081ee1fcea3155823c000898523f42d5eaf125f4e0eaa8f398e4bcaa3c46000cfbbd791bd0467670001f68cc326114740006006ddb4f35450863a07d640000009ca84b4c5bca40d501fccf56122eaec54000fdf30748739f84ac67600022560d864d2fbfe6b0e8
    | 8 => 0x6d608cbc918f57ba0000aaa0004e8800000050a61360840012bedc3800287a9e11260000e79c93f1754e100c41ac14912823e669ca0bda8001605b670000000000000566bbae00005f56c4304add000689c0019160005094000000e018a4e79e0594540003fdf092d748003bc596c00000023d400090c0c46a019d15153c7c9c6ef58a8694e8609919da291e2739810f1cb841fbbe4000620b4661ab
    | 9 => 0x86b87449f8b510002420e56000b5000012d8682a19c8300c2399f7ee97273738f00000028876981cb63c8001475cb40ab21e60000001ec7d1d4a40000002667b2e6da8fa57da89fcc683d5651f0f000000271600077096d78c425726100000017930005b0400006f8bc0001dae872703a428db01210003f9531f1b900001498ce0e58198e4834fbad52d00030fc00031883302f61262c92b7c00121d
    | 10 => 0x228003a61fca7f4244c00061d1766a4f965b530000003bf3268c4433fc000563a2c424000089ab289a28aadd2900057d08900002fdbf76ac412b000000049c5810003e455e7a78d13e419b280009163584000ab54777d82632996dbd0001b77996aa13b2d5100000000002248f003795ce4000571089a8540ca3f0612800101eac60002c883d353ac36ac9cbf2374f780003ce8ba762e08b4f1f2f2
    | 11 => 0x250001a6285d2d247f8c802fd82e1103cf045fe381930000d1600018ceaf5885c6c0c984061c762e3c9bf85a9b4c780005fe0005c0593d1b438dd1d36d075d068b486f953c0000ad11e38001d2ce3fc311dbc3ad0000413c149f10d44738db782ba468b172b7b53aac8b141095595ec8003abfa8770b0dc627400000047700004913a12fd4000a9926dde0c00184600061a89a23bc532b9e8b64d2e
    | 12 => 0xcad09235c812106789a4000f619e3cc21708dd295dcac4001773bea13fbb990945150000b08000b700c2e3ad21b7760abc86822e7930002c03b0da7ca56a76b673022f7716840cf518c6d07f604c1088c800000800a3f2dca9412008f024b0220a59a2095495e005000429c000000a2a0003610c900000399bebe104e7b503a5751367d3f8404e000b8826d455a000171476cf72d45a388c2f48513c
    | 13 => 0xc4fed483ff591000000189021f31339d853466314b000126370f2042157656ca300033920ce8df77d18d4d8555959d8003bb823201288ec964000477b9cb1965cfcd2cb300013cd0002095400e1daba0002edb9e8227b6c9fe40002e1800093192388046f6533fe70000002c0039f200a79d2db38f0001f7521c000000249253f9fa5e120f05913e3000363c00166a000059a7548eb07854bdfd2000
    | 14 => 0x395c000ce500025b8d60000061b2f48b18bcbba4f13f55c4d00066a0fba2a0880c62e730ff47fe4d2e4807a9952baa4e240008d99d8da9d9d7f6b8aca1f600000008acb46000cddb6fc001787a7bb2cf6be0002360bfded3d2600064bd59bb290005cb45490ececac5b1d99aee00003a0001d440005b731830c10005728000deb7e6e7f80006dd0002ee5083eb3c5bbcbc00119e2a9000096c000
    | 15 => 0xcd63fb53e32880001a9d3571de0d28b336ca000af61d7d68000031f068232c000e40333b9d1e823409dde94e0005f10000001dd10a58001fc74bf595000096e233c3a07c7f64ca4a393ba800000077c5f940000000004a351a837e8cd00d70e50760eaa6d000187700061790d2b6b4e7000100610e0000000d1c00013b9b91e0400021600020a80000c744bc846d3648c00029abaf8a1c00030aae48
    | 16 => 0xa87d7e05dbc4800043287afd878ac080c0019b428ff1ed82400001a8000001194b5cacf1dbeece7f600030ee06d4300001beb10d36ed15400003144402de047eb6e9e8ec0987897eaf849beb41a600000023982ed0003b4c0fb88a37ede877dabc170ca099f45c12000337c001c76e05b832b6c7558fb80000000000003157a48230c360eb61c322441a94e87a928654dbcbf4e299b9db345c001357
    | 17 => 0x9b94300000000002170cadf784bd51f77b684da3f8001ff54ddbf6e63400000024a5f21b70b020007d98000e198c78f6e16b1220006ab8729b997b900035d90b1c8d086f7a600000057a1467d2c08682c1efb46f05b03503463720391ccdc741612df92102be31447821c9b31f2defa9b5800156bd7d8000562e690000001e3211c70c87e80000000000001dcb79e8378002d680f201db310000d5c
    | 18 => 0x700cb5c000a5466298decb002a7c777dbc4058100039cd9cc00022ca9accda0f900002b00f12cb0001da413c2564f7425b55200079900026759870002b37938fb504adf443a76570006234c4073598857860161de0003eff3296fa0005c6c471111972fdd40008be04b1966980ebb3643eb881c000bdaa11596e0006268f740000003711fcda3a0000000003d9d3a2dce21d914f73003c5ed09092b9
    | 19 => 0x7e5837002b7fd67aab67ce1000199fb22000ab48420ef0bc400000000f40009a640987b45243c0b6c9655d4d1b39d30d75c4da1a21d00001cd0dd80010600001d8c50b6ea727032d040001a79a565ed41a6fc50bff4314b618d382ab041ea3cd3529851281cc10007bec00143d0004459222237b442db46e800002f11d2b17c7200000017b00009cecd55a80ea3c1459d8000f8682fb7dd367b1d
    | 20 => 0x4351810ce253faa40002c60d66000362fb033de0006e0358a70a1a2800262bb0cd66300e0f20000005e30a8e42326e0bf96ba9240003a20000089b9b6d5e25a45815897e46d510f2db8002f630f00005895dbc7952cf5c059d9cf2b77e25e182000ee3bcbcf0a44d00014f3cb380055ddfe6bc6ef5ac53450000000a96ef8fe98000d1406e547e2bd29300029b94f40002c0394e0000004af4aa91cf
    | 21 => 0x846015f335ab40005d4c43551f0003b3d128aea34f177800027602e843171293f00036e66ca1650002f0ea3e7b2dc6a7b800015be232a90000000f488cba2052094678dec4ee00079812d8000000fc198ba7ea314b1c0814000389fd590af4b89911398000925bb1e18d02d653b0a7360002aeca3d024417b583c161724ba59052285ccc8d20b2f4308415d1c0dd8d00037a40011434ed00008acf21
    | 22 => 0x10d8000000888d149bcc00023b74e000029c0003c500023e7fec0002bfa5574db0964add7f231b45bc7961600000c65c87608f5d038813415466388d8002c11e7e00072a649801bbe38001c4000012c0a380000005e625390ee532898366f6160006f81e21c14849cbca042973a50a3680000009fabbc7c5c0000007e29699f5a4234e583c400066dea1a75bc5e3adaef8000000000d6ab81df2f89e
    | _ => 0
  fld v 13 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 736 (hk ys)
def qPick1 (ys : List Nat) : Nat :=
  fld 0x75246310 4 (action2 ys/833)
def qOri1 := quickOri 154 8 inputs qPick1 qRow qWord qBook

def J (ys : List Nat) := action2 ys % 833
def r2 (i : Nat) := bar 154 (cutB 9 (B i) C) (cutN 9 833) (fun _ => J) qOri1 [] 10 0
set_option maxRecDepth 10000 in
lemma rp0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp12 : span r2 1 12 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp13 : span r2 1 13 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp14 : span r2 1 14 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp15 : span r2 1 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp16 : span r2 1 16 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp17 : span r2 1 17 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp18 : span r2 1 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp19 : span r2 1 19 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp20 : span r2 1 20 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp21 : span r2 1 21 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp22 : span r2 1 22 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp23 : span r2 1 23 = true := by decide +kernel
lemma secondRoofOK : span r2 24 0 = true := by with_reducible exact (sj (sj (sj (sj rp0 (sj rp1 rp2)) (sj rp3 (sj rp4 rp5))) (sj (sj rp6 (sj rp7 rp8)) (sj rp9 (sj rp10 rp11)))) (sj (sj (sj rp12 (sj rp13 rp14)) (sj rp15 (sj rp16 rp17))) (sj (sj rp18 (sj rp19 rp20)) (sj rp21 (sj rp22 rp23)))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp0 : span t2 83 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp83 : span t2 77 83 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp160 : span t2 28 160 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp188 : span t2 38 188 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp226 : span t2 37 226 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp263 : span t2 44 263 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp307 : span t2 40 307 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp347 : span t2 31 347 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp378 : span t2 10 378 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp388 : span t2 45 388 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp433 : span t2 25 433 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp458 : span t2 65 458 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp523 : span t2 34 523 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp557 : span t2 15 557 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp572 : span t2 72 572 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp644 : span t2 65 644 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp709 : span t2 50 709 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp759 : span t2 17 759 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp776 : span t2 10 776 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp786 : span t2 13 786 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp799 : span t2 25 799 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp824 : span t2 9 824 = true := by decide +kernel
lemma secondTestOK : span t2 833 0 = true := by with_reducible exact (sj (sj (sj (sj lp0 lp83) (sj lp160 (sj lp188 lp226))) (sj (sj lp263 (sj lp307 lp347)) (sj lp378 (sj lp388 lp433)))) (sj (sj (sj lp458 lp523) (sj lp557 (sj lp572 lp644))) (sj (sj lp709 (sj lp759 lp776)) (sj lp786 (sj lp799 lp824)))))
lemma upperDead (i : Nat) (hi : i < 24) : ¬NatRun (mask 154) (goal 154) 10 (B i) :=
  symCutRoot (quick_safe (k:=154) (bound:=8) (xs:=inputs) (choose:=qPick1) (row:=qRow) (word:=qWord) (book:=qBook) qCert) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => cpWith_sound stopNo closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 154) (goal 154) 11 inputs :=
  symCutRoot (quick_safe (k:=154) (bound:=8) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 154 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row27

namespace Row28
def inputs : List ℕ := [0x23611b2236cd809b104d899e6c22880b653e000000000fffc0000000007ffe000000000f,0x48b74505e062814520a29203155e12e6a2e2000fff80f000000000000000000f03fff070,0x2e0c2061e4083138609c3070418e47804c345fff0000f00000fff87ffc38000703c000180,0x9504a848831426284bd47828a0897bb71c08000000000000000007fffc0000003ffffe00,0x2e61730e0041813b0f1182010c0ffa0380811fffffff000000ffff8000000007fc0000000,0x30818409118205bc0fde07fdf031004c000800000000000000fffffffffffff8000000000,0x3f01f80ffffc07c008e0044e0020047001001fffffffffffff00000000000000000000000]
def vals := sampleTable inputs 290
def scs : List ℕ := [0x13c290f89b24c94,0x210771789224496,0x1dc290309c25caa,0x1780c1dc9b25093,0x1780c0a4aa24c9c,0x1dc5e2109624891,0x1783e0309624492,0x13c0c1789c2509b,0xa40c178aa24497,0x1dc0c0a49424c9b,0xf80c0a49724896,0x1783e1dc9b24493,0x1783e13caa26c93,0xa40c13c9b25093,0x1dc29210aa25897,0x1783e13caa26c9c]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x14941a6c8a106a8a210000530636166406188aa5210e005345160b0c08533f42535ec212420a6d4029215e04941698d49237206709175e9812467e10451c04505f320a4014060e3c064014045212209a1b54870a6a861e0e0c532c28743c02126a0a6d5f0b186a0a895ea6126a861cace81808023c0608542a42900a5212043c128c29210404534e95040402534b1a530a0e3c064212209e1e02025322a8210a3c12460612080653085e93045e124883032b041b63240c46be0f0a530c6c8a2360e50b0804535f16530802530240140606530e521254861c6aa6120a5e1206045354c2120602534639049c52125aed0d0600530c0c564a8a2247165314e8184cc2123602120e3c127e4add0e065304005360841b020053043cd40e04534d16530e02532b021c6b16533d3c0b5516530a00530a0653a4928a0e4a121f36530e29219c4212061ede0a02530e0a53040ac4445b1e581104083cd40800539e0e8b7e4212b429211a9e200c5e120e928b62eb200c0a530e085354801a568a2348e2d4
    | _ => 0
  let q := fld packed 24 (i % 128)
  (prefixGates (q &&& 511) <<< 24) ||| (thirdGate ((q >>> 9) &&& 255) <<< 12) ||| fourthGate (q >>> 17)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x80fb3542fe9da6272fef1f9b5dae946b117c7113095ccedd927a5776a0fc4c221e231a6ab29cbbf234179ed02b14270183869da31d2b04b6274f0b830c10434cb644484024cf2d224fea4d73499fe15ee772266c21c5f8512bdc7502715a5ad056d11d4e6502beda4aa6c66b0e38f5fd114a731b60e96287f2cec7d710ef9a0e
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x29625040107416de537914c6d747c2e6a1d50c3bd1f0be36de2b928395d59bcf876214c40100102462d00346c190420640c3a45082f83c3dbc085c4f09019722470ba120233298494614529287308fc6c10308a63010922c7c1146103e041cb803c04184014032b302243de85f25108820c0c8464970b4b1f16c709650426d2b1a8f2261e0c36a2169517424a42414b8049090a4c947ce41251314f832801902cb79912d994a56a3aa42a83a5848822c3c120a6311358b1a0530c6109128e820b8333624938b4901c7a421291058a484bc24f4402509144d15c7c11040745819b6481804322452bd9008a4a591d047902255f912090b041f24a3205bc1905580800c641918801a2162ad4b244185e98
    | _ => 0
  let q := fld packed 17 (i % 128)
  (prefixGates (q &&& 511) <<< 12) ||| thirdGate (q >>> 9)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x7cd04cd0fe3f67442f1fe9a37bd4c729e73c74b5fc9559654bec57d54dd1eb9874e084e5a09cafc12e9b75729e29270110ed9dcc1d6c1bbe969064970c108567e25a489c7b049f49ad78ca8afe3be1c606c7266c12d10174bf4d7aa63825cdd073d11d7765ce939bc5a702a37dd4b50b834feb5c346edd8716ea3ce2596a24c4
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 128 else 0

def board : Nat → Nat → List Nat
  | 7, i => if finger7 i = 0 then [] else cpBoard (mask 145) inputs 4 (recipe7 i)
  | 8, i => if finger8 i = 0 then [] else cpBoard (mask 145) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 128
  if table i == h / 128 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def x8 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x36978060867003ca0d06f8070ffc004009f15a61093c05536601f40f43ff56d94c60f00010103349165202f0073d17a255000cd6450a0525375e600a591b0203f050bb26b562000100b336fcf923b1b6b6c186da650427049b44867206a07a50e0c1540950e0d053600f0e20938182b31ee0001774887950204432007d770869
    | 1 => 0x90d00a7106d32553c00ec50023d24064d16df03600a30bd260a70070a54e5d83029c3510f305861d40da03440018e04a00f7add7ffaf46860450ca0c84cd0f23cf006c5f016600e51b16c10700ccb02b80b5d64066263467a51b0eb2267200de50700572669302f05350a36c5761f03807ae3554737b71a230a1924471190da4
    | 2 => 0x959405b40894d74602074321dba6a0000000548a1500c34d0e61060dd732e11422b12f257768b107890d423caf901c070740c1b1deea74807538930da3c5690c20bd16e145609d35b49d323713b800351040b6af90ff045157aa54500b50005e3f41d870d3a5619a0a2d312c60ac07d697123573e6644eb84db0005fc809c300
    | 3 => 0xe8b05ec300c937fe09e7071f72c0b826040600c9f9576b5866a453f0eb86001000c03013b3177000646052343f45042017792032e39004001420109c005014e3bd6a710001a0b0172216c26000b010e04750808bc60010b2907002564006f0009f2803e7100899107071664440cbb0100296122306ca0813d03514a109400121
    | 4 => 0x183ac3b8c7f00a32284a591013500d0601ca09e0d6200a662848081c7700d7496620a540f7e0d02df4b78c6c10e044c205b704e0b7974e40c0b460b106553f2f42c56ca610d20010dd6b317d3f702055b09edad1b0d8c5e00f1f52a402fdfa707401ce60414002002ce7913f4270f673920c4b34413e0d00150084040752530
    | 5 => 0x966301300e00120d9c3403e286b534932301e2407d7e56c0fbd9150d04081700d2071043090f071e006327047750100308ccb600902f71032043bf203c104f7017b4000db95e7ded6f034b0b9b533560031620524ee6020081c00d110d30ba600b510480525e7b0030a030a018e14b392e607059490604207d96164e80120c3a
    | 6 => 0x66dc92347520a003af1ea150615da4a307f0f0001a33011466f0a310114737618500d75c0d0f00b08a000dbc1180f00b014f485771743c60e209f0c22006101085000ab133a61c82bd0224c06050260737b257e1ad742c65370c527c2208440c079c3c009629077d255c6805810900365303ec00e8f1f902ba5110c460005f
    | 7 => 0x723506a2001646d200640054610510605444a94a60091000090ee01c05500ed2e2030036a0682a314b00802503040f6000702ea042bad4d43071214413150100e0678e16db67443f7df069b33308150a670e0b67d3f80b770d7f08f17e2070bdda0a053506b35f8101b3c13a008a6fb0b84d00d306418f8400179173000c26ff
    | 8 => 0x58a4600ae5960365b24f41a06002d479c52864e26f56f03c230f9384640726406858086591fe79007724868021b03e14a01d0000c83e5000517df8e9c0720002901760902200d00155a7c8a452008fe6050a10d15a600d030612309d2393086d94d313721092712b00d007b000104b6304b0a380997d06730af0e0b073780300
    | 9 => 0x35007f0010ad06060010fc220828070559902e1803a070f04700e080046230eefa08565bf80100e06ae0b0c22016004239300d42f403d0570da40010360c40003e4f80047049a069701890507e0f0254472020960ce0c038708210e02042109e0bc75337dd004f20142321a0d76510056260070060090ac07043060b80db233c
    | 10 => 0xa4771f73e05da24289047c0730a9c800056d0a131974060398c60753308d00003b78708092b2b57c39a01908508010a0a305a000e1e4544705e333204b772170b41020074007700243020e08e0f00e141000331100e400300202970928440664805f00174000044010902404aa8453b0610e0e78a301d0acc9420004801b8c5
    | 11 => 0x3ed07fbee0073b40d710405c030075376f17ce0167b024600307f09b0801b50dc4416ea0a3608450ed9f4760005ac047c0b030450bc9002fa0440a400503f1e119226bd5e0fbed3a023000a553d5f606065576f0b00c0403d4305085d6b00bb2df412a4141c470209238076c4af2c7b5000f628794a02df0a2e8cf206110264
    | 12 => 0x76a40051b18cfa07ff50397e064401a7d0810f040bd0d70017502057047530dc0adee84f4ed24000c0cf241056fe009f9079100c753e20048a0f500c40000d100807c0f0b04ebcd000c400309f04070f0001c6f10e3040600ac6c4000604e20009203421b04504831e26067f8190571000b100308829490600f009e64e661616
    | 13 => 0xc000e22c3efa634050270302ecf0542427e21f02d8d95009574270403f920bc2a10f000d454d1d0d0004e0b388089d070056710007100303350b5011300e1e39a907d03c44e12fec126177111f0550610c6103ba08601781b200003074000001e111acbbe82f0501f0790f3209e4760e136e0605770080004450680cb0ed106
    | 14 => 0x3750b4510400c00c48019d3300506049084001a50ab0306060578109e60409690a120008203cbaf3100b700d9b600640333c5c06b054c550a6140c2240006d20eaa800404bc90010c43066dc1f0e40d762c042b606fe0a7189925df30f40150170f728976eda045460770e583e6a2f00a1f00106f3070050147704300837908b
    | 15 => 0x5434d32e600300427149d20c02540106e03b103e30034001900e4007a3060947e02083b3550099060426b13003263030c6c0705936f008a00f3480b625bf010010c36079508d40450035a4c431c15d06d0055210b05ed1d0c5300045061261e00500d06c00a470411243e0b0b4f0200450530b979dc874011320035c908cbc0
    | 16 => 0x600010f56740478077771532048f0302125e02
    | _ => 0
  fld t 4 (i % 256)
def hint8 (h : Nat) := orbitLookup x8 0 1378 h
def x9 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x1c1c35453a0e501f138c0206f677f0e0b0237000c5828d7a410e5c57d647d8a2c0006a17701170d070537c7d793684c42001871042facb90f5f505013f9cd2a4007080d6232cc200cf125047221340013a0e642126010500f80f009da4b3d9c506911936f8cc5a1e70250103a10a74087300111b64b02c8f11e1e0d3e6d02503
    | 1 => 0xe07a5066571f307000116089d0302e352b7f200bad0f387348768722a600200cffab4d00898bc30503b54a04067d0706c3ea780870616362781760b0040023220cdf7ab05374907b8070e3001663feeaeb805852330429936140460800530c017350a2660d573b3efa671b0b030240104b550d000000409db444300cb213f319
    | 2 => 0x7a9831c606944c2383c760a5e0107f90ab0b0304074f120400030013910912227c2e00670702c02d105b8051640030500e00002af930000124598cd0cf1037d0fc44517030504f1f096b00085eb3014070052c206936c71000707310084700078a040396b07ccd350ba0db0458125af3b95d5366a60ec016d060307ae0e7c737
    | 3 => 0x1780080a70030000cc406759430600102d8f8e2bd10400052590e8166063c00270fa41d806036e907269e3104412b60000a033080d0e03416207cc02009d39081b303e92607110f660409e06c7010370304270090a00c56f220708e0100229070005c979420005b010006d0e264e204f63340234cfb08550e0e761240010ae
    | 4 => 0x9465cf710b9782a9334030020a9f22340ad4600704720030e2100f66500772150e9cae0f2324dca0b90061090d7a3cb1617c00030035120bc00a320f4058d00060a00075c004f01f1cd73663da1078e11260006641ad0600e16847000100886d5001021904d73e22b61f50e66c60084d00fe22906de2570ab30a7ef00b36b5e
    | 5 => 0x28e884309060ae0320e05880b0061000b2007265365000c0d00a953f031aaf4402569736b4104009c50a407066c506db07d80fa76307000a150d0d4a0900a10e0d408a9045f07010063e2c071e2320470aa007b871300980104000208b00b5202500d3611bc44a0530073830623f749003c79113dc4a7a200050006
    | _ => 0
  fld t 4 (i % 256)
def hint9 (h : Nat) := orbitLookup x9 1 509 h
def hint (s : Nat) (ws : List Nat) := if s = 8 then hint8 (hk ws) else hint9 (hk ws)
def labels := 0xec0045000df0000000db0000000ce0000000ca004018eaa00000011f004480106004463a84881ddf4740000000ae002a5f29c003f9ee707b1b0bc5c0000000d80000000cd003a1ce4f002d1884b0035dac3e0029d863a00325843760a5c52270000000ad00294009b002c96a2458881281e00289561a508312609002592407488100000
def cols (t : Nat) := fld 0xd5c4457a20758d11722e0b33445c8c61d43432a398 21 t
def u8 := 0xec0000000df004762284003ea0c740039db04f00311684b002d55a2458a50401e0000000ca0031c00aa003dd5c707b179385c003099237608a52e27002492c07488000800
def u9 := 0x1140000001000000000df003398eaa0000000b40029d829700335884b618e852270044a2077002a5ec6c00419f47457270bc5c0029562205083122040026d281e498240000
def u10 := 0xec0000000ca0000000df003398eaa0000000b40029d829700335884b618e852270044a2077002a5ec6c00419f4747ca70bc5c0029562205083122040026d281e498240000
def u11 := 0xdb0000000ce0000000ca004018eaa0000000ae002a5f29c003f9ee707b1b0bc5c0035dac3e0029d863a002d1843760a5c522700289561a508312609002592407488100000
def rowIx (t v : Nat) : Nat :=
  if t = 8 then fld u8 9 v else
  if t = 9 then fld u9 9 v else
  if t = 10 then fld u10 9 v else
  if t = 11 then fld u11 9 v else
  mkProjection labels (cols t) 9 v
def rr40 (t : Nat) := (List.range 162).map (fun i => rowIx t (fld 0xf36d62611246143e32c7cbad8984491850f8aa99a5c699638984491850e271657289a6164d124614361170e36a89a61138b2461436091858860d12450f4d34d34d34d34d30c30b2cb2cb2cb2cb2ca28a2492186186186186186181451449249249249249249040c30c28a28a28a28a28a288204102082041041 6 i))
def rr41 (t : Nat) := (List.range 176).map (fun i => rowIx t (fld 0xd30b289a54891850f2c2aa268d2246143c70a689634891850f0a3cc2879d4891850f8699d16571c286554d2246143c12b0e370aa869238b246143a091854860c91439249249249249249228a28a28a28a28a286186186186186186081c71c71c71c71c71861851451145145145145145141030c30a28a28a28a28a28a208104082081041 6 i))
def graphId (t : Nat) := fld 0x541045 2 t
def qBook (w : Nat) : Nat :=
  let d := fld 0x416451db603e5710c1d281d10e3005a7fdd1330c911006941020402582f004908a104010d693e021a253a1000130a0003570400201200250c040201000555250a060127080001000101000a07173601002400000304030d1113010a0102030f050800160037 8 (w % 103)
  fld 0x3a0800d0440f2b5100044cb36542159181ca3e61f2810cd857a20f94d9ab441ee800048c18b04997041a6f9464e833052619d7a18a740060443203204d5c0d6066b628a80a462d28351686d827772f4c00108d7218b345142ee2ea8315d5c4cd3a30370886bd45c12e151823440c09110328ce604a000098a0431661275c8108a5468a38118185852820411c2e56428a351cb09d62007145a8343002091168cdae0e5abb948808b0ea0379080bde32307315142d502107357dc7c28200e5808e09d06502708805c20c106559160c484612b8c86cdc5f33d01c8c0ee46a8e796800000230e7468c394041aa941ca0a55ce8eb81865ee56a3a74a8c5ca6f72a3155c6c106e8b7419674442193b814cbdd1a0232995cba5361062972ad8d27286ba128ace54a3e057b86c524e00155a6000000133088c18d1f70105b4a1c166e9511d2aacd2e6800175c0c60d2a3095985e53e0b50008a8cc3659716086de552192981842a546a4255f1408414581019ca5ae56eab597ca0016529731b023c57459d0df041c25eb12949821ee6c63a1588c8cd5459b7411a28c3ea33b81043a63e58305d14a9d003890d1960d50ee8a55b28395621ba041cc5d46cac209728e8d462b111f1808a1ea8279f164dd6468b28e80f466a30e94ddc09654a82b8784085165a3743aa09514a42055ca18c1c98f507388445ea9b555aaacb14b422c55c0ce 13 (((w >>> 3) + d) % 315)

def im40 (t : Nat) (i : Fin 8) : Nat :=
  if t=8 then (Fixed40.raw ++ [0, mask 81] ++ [0x8b0059145802b081b52e0000001ffc000000000f,0x1024806880810404001000000000000000000000]).getD (fld 0x64359281 4 i.val) 0 else
  projColumn 81 Fixed40.raw (cols t) i
def im41 (t : Nat) (i : Fin 8) : Nat :=
  if t=9 then (Fixed41.raw ++ [0, mask 88] ++ [0x560aeb58159332c206d4f000003ff80001ffc000007,0x800000000000000000000000000000,0x310620c427430620eee304000000001fff0000ffff00,0x100400000000000000000000000000000000,0xacc118231330a118e098d2ffe000001ff8e000e000c0,0x40000000000000000000000000000000]).getD (fld 0x64521938 4 i.val) 0 else
  if t=10 then (Fixed41.raw ++ [0, mask 88] ++ [0x560aeb58159332c206d4f000003ff80001ffc000007,0x800000000000000000000000000000,0x310620c427430620eee304000000001fff0000ffff00,0x100400000000000000000000000000000000,0xacc118231330a118e098d2ffe000001ff8e000e000c0,0x40000000000000000000000000000000]).getD (fld 0x64521ba0 4 i.val) 0 else
  if t=11 then (Fixed41.raw ++ [0, mask 88] ++ [0x560aeb58159332c206d4f000003ff80001ffc000007,0x800000000000000000000000000000,0x310620c427430620eee304000000001fff0000ffff00,0x100400000000000000000000000000000000,0xacc118231330a118e098d2ffe000001ff8e000e000c0,0x40000000000000000000000000000000]).getD (fld 0x654d3c10 4 i.val) 0 else
  projColumn 88 Fixed41.raw (cols t) i

def okTable (t : Nat) :=
  if graphId t = 0 then (decide (validCross 145 81 inputs (rr40 t) (im40 t))) else
    (decide (validCross 145 88 inputs (rr41 t) (im41 t)))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem rowsOK : ∀ t : Fin 12, okTable t.val = true := by decide +kernel
def passed (s t : Nat) (ws : List Nat) :=
  if graphId t = 0 then crossHit 145 81 inputs (rr40 t) (im40 t) qBook (Fixed40.index s) (Fixed40.N s) (Fixed40.S s) ws else
  crossHit 145 88 inputs (rr41 t) (im41 t) qBook (Fixed41.index s) (Fixed41.N s) (Fixed41.S s) ws
def stop (s : Nat) (ws : List Nat) :=
  if s=8 ∨ s=9 then
    let a := hint s ws
    if a=0 ∨ 12<a then false else passed s (a-1) ws
  else false

theorem stopNo {s ws} (ok : stop s ws = true) : ¬NatRun (mask 145) (goal 145) s ws := by
  by_cases lev : s=8 ∨ s=9
  · by_cases outside : hint s ws=0 ∨ 12<hint s ws
    · simp [stop,lev,outside] at ok
    · have good : hint s ws - 1 < 12 := by omega
      have sel := rowsOK ⟨hint s ws-1,good⟩
      have hit : passed s (hint s ws-1) ws = true := by simpa only [stop,if_pos lev,if_neg outside] using ok
      by_cases h0 : graphId (hint s ws-1) = 0
      · simp only [okTable, passed, h0, if_true, if_false] at sel hit
        exact crossHitDead (of_decide_eq_true sel) hit (fun i hi => Fixed40.atDepth s i lev hi)
      simp only [okTable, passed, h0, if_true, if_false] at sel hit
      exact crossHitDead (of_decide_eq_true sel) hit (fun i hi => Fixed41.atDepth s i lev hi)
  · simp [stop,lev] at ok

def ck := cpWith stop 145 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma p7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p7_64 : span (pan 7) 64 64 = true := by decide +kernel
lemma good7 : span (pan 7) 128 0 = true := by with_reducible exact (sj p7_0 p7_64)
set_option maxHeartbeats 50000000 in
lemma p8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p8_64 : span (pan 8) 64 64 = true := by decide +kernel
lemma good8 : span (pan 8) 128 0 = true := by with_reducible exact (sj p8_0 p8_64)
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def qPerm (i : Nat) : Nat := fld 0x2e463000000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0xec0045000df0000000db0000000ce0000000ca004018eaa00000011f004480106004463a84881ddf4740000000ae002a5f29c003f9ee707b1b0bc5c0000000d80000000cd003a1ce4f002d1884b0035dac3e0029d863a00325843760a5c52270000000ad00294009b002c96a2458881281e00289561a508312609002592407488100000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x4 2 (fld 0x66751402adaa695 1 (bsr 0xfc42f9d4f983b625f65fdd8aef12a16bec0068fceb7ae66ce7927403e2dfa6bce2db16bfe26ffb0ddcca50b6dbb0c082d44e0266cc4ddd90c85b11f0c1dfed25bf892aa7be90fde1b9bc5323b8bf2ae5b840280ab5d8ee2bb3adf8d9ab918a6c97bbd4b794566034940775d48b1dbc4189fbe569857f9ccf8332a657802623957e18e57872440c2866b42c306577bede64e28e865fb708ae5f5ac764582d6f9955b81b3d559524404b5745984233e06b3e995e0c3ca6bef13b7161ac39b75ee63691856b3404dacb3142e40e3053a2802852bf39263f2b591ea98f881e2ab19a1d566ad01839463c149a43ab0b8e4e0d0b26fed30646ede901f9f82f01eef95d 32 (hk ys) 7 0 64))
def qOri0 := quickOri 145 2 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 2, i.val = 0 ∨ validQuick 145 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 145) (fld 0xf54e52f21f41000401e10e20f65e50100f20f10402400506f53e54e41e42f31106e51500e53503f50f52e31e21f51f42104e65504405103 12 i) inputs
def I (ys : List Nat) := bsr 0xfc42f9d4f983b625f65fdd8aef12a16bec0068fce2dfa6bce2db16bfdbb0c082d44e0266bf892aa7b9bc5323b840280ab5d8ee2bb3adf8d997bbd4b7940775d48b1dbc4189fbe569857f9ccf8332a657802623957e18e57872440c286577bede5fb708ae582d6f994b5745983ca6bef139b75ee63404dacb3053a2802852bf391e2ab19a1839463c149a43ab0b26fed301f9f82f 32 (hk ys) 6 0 37
set_option maxRecDepth 10000 in
lemma roof : bar 145 (cutB 10 inputs B) (cutN 10 37) (fun _ => I) qOri0 scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x33d90cf5433d8c5e6533d80c40633d4ccf5031014ce76339d4ce6533898ce2530414c505139502e6530408c50233c50cf1333c40ce7133984ce5133d0ccf40310107e64339d0ce6433cc0c4033398cce53339ccc5073041cce243384cce4323988ce2331000ca604f818ce60329423e05339407a608f8107e603b90136034f80dbe606e9023e0377981be400d8183e06339c08a603b9408e60339007a401f9008e40328c1be50338c1da4077900ea303b8c1ee606f8c08a307b9008e3036804ba010a840de012f80426100b8407e03778c15e1055841ee30
    | 1 => 0x6d401bf736fdc9bf766fdd5bf716fdd1bf706d01c16026fc989e2337985b5035388cbe621b88cae21078083e136fd95bf456fd8dbf436fd845e636fd81b40667985bf405f989be766f9d11e634f88dbe246c411b504139442e626c409b5024398dbf516fd41b4056f9d5be656f9158e616fcc1b4031f98d2e635b981be616f905be71579c8fe613b88dbe516f8c48e636d00036030f80dbe703040cc10432c84ba6131d40c72131400cf7433dc8cf7633dc4cf7333dd4cf703101c160533c989e253140cc50433c84be611b894ae25078143e1633d84cf51
    | 2 => 0x7bd49ef327bd445e437bd41e405678c5ef305f8c9ee757b9cd1e434f90dee637840de503138842e3278419e5064384def417bd01e4047b9d1ee547b8d18e217bc807e134b84d6e207b945de31578c8fe213b84dee4179000ee703a9813e044b980ee60198146e052040c8321204088721214008f76200008f6523d90850323d8885021b9448f6323d801e530f9908f5123d045e5423d0c8f40210108e54239948e64139082e5323c848f1323c407e41239448f302100c8e432141c8107239848e13210012e507b9c12e037b940da612a885b10303944a621
    | 3 => 0x39010ee763b9d0ee643b898ee2438410e504139482e6338408e5023bd44ef533bd40e4053b9d4ee653b914ef133bc407e613b984ef303900cee633b90ce5073841ce400569c15e703f981c500704015a6057980fe50569415e503f9015a2057880fe10098084e010b80906034380d8a406390146035380ca6052b8142a40138c02e40569015e403f8c066031b80cda2162885e102618840e2179d01e73079d41e76079dc1e5007bdc9ce437bdd5ef747bdc5ef737bdc1e4075a881ef652790cde21794094e432f8c86e132b8c5ef60078c83e437bd51ef34
    | 4 => 0x3d40c45061041825070841d55073d418f1064141cff4257d48ff4157d40ff4055014f40457994fe5457914fe3457cc8ff2157cc0ff205500cf4021d41c71074941cfe5257c80ff1055008f40157988fe5157908fe3155000f4000980c4e020b80d5a30578c0fe202980cae03518114e04629818e60429810e603840ce730384046a2103948e75039d00e76039c94662139dc0ef713bdc8ef7039400ef763bdd4ef733bdd0e4070580cef2627890de6239404ef252f98c6e212b88c1e030d8503e143bd94ef453bd84ef603bd04ef403bd8c5e6439018ef43
    | 5 => 0x5b8c1de5175001ce037180dde704580d1e03779409100254024100914002605138102e0554408f1015440cf10201418010655c41571355c5d571655c55571255c515f1057c4d5f1757c595f1557c495f1455400f50057dd8ff652541c91073541cd1075540cf5025141cff642d41cb1071941c61072941ca10757dc0ff600541c11073c00035020c4095f653fd515f453fcd15f603fd415f403fcc15f633fd495f433fcc95f623fd4455071441d54063d0155f423fcc554043d00d5e16558595e145585115073f94d35073f9955e743f98d51043c40d5504
    | 6 => 0x2900414020d00d6f525bcc854035bcc164034500d34035b98c44010900904035bc8164021d00d2403590000e012d808be021580c5e038580e1e039180e4e038980e2e032580c9e0364884da3166885d10375cc00e3175d00961365885d75075d81d77077dcdce5377dd5df7477dc5df7277dc1d4075a8c1df652784dd500378c5d5035394cbe421b90cae4177d801e420f94ddf5477c91df5377c8ddf511784ddf50750159e215f809de75779c91e134f94dde6274409d502138c42e424390ddf4177d01d40477951de24638c5df307500c76231f88d2e43
    | 7 => 0x1d0147f231fc807e751f9c87e521f9947e621c4087502138c82e431fd047f401fd0c74041f9507f131fc0c7f101d00121014ac840e4249c8527704bdc52f764bdc92f754bdcd2f744bdc12407480012f6227990de524940125014bd94be531b9852f602b98c1e630f9d12f254bd152f214bd052f23178912f204bd0d2f40490112e724b9d11e244b9892e644841125040984c2e13439452f504bd4d24054b8952e454bc4d2f034bc407e51490012e701f9c07a50478107e504b9015b203acc08b3032cc004015bdd8a6015bd9494033540144032d0086403
    | 8 => 0x1009ff7071011ff757fdd1ff727fdcdf40719805ff6525010d4027d40144042d00c64012900c14030d011ff547fcd1ff507fcc1ff5215011f4056500d74037f9d5fe734501134047f98df1037d40c44020900d04017fd09f40461009f40003808b6032f80cd60237808960427811ce047181246049381196036780c56041781073211c4047b21038c877401dc9077211585077501dd8077701fdc47f761fdd47f741fdcc7f721fdc074071c0007f651fd8875031d40075011fd9075041b9047f601fd8c1e430f9507f541fc907f511fc847f53178507f50
    | 9 => 0x43d045f5443d0d0404439510e65439904f420bd4d0f03410007b404ad40a100294010a4043900610019401db4056d40eb507ad01bb50858161e059181a4e06658119e04898122e04258149e0503c858f7063dc98f7663dd58f7463dc58f736101d6b2063d949f4337c85850253d0d850063d80bf321bc4caf3107cc83f4363d518f3463d418f5263cc18f3263d445f43610158f315fcc98e75639cd1f434fd0d8e636040d850313c842f3263d010f1363d05840076cc0770349c0d4100514018a50639418230628c18630638c18a70639c15b306ecc0cb40
    | 10 => 0x114104f5213d444f5004418310709c544f3409c4c4f3209c4827140bc402f700bd002f730bdd82f710bdd42f720bdd02407080002f610bd9025020940c2f65094142f630bd882f60054182e760bc542f450bc4c2f430bc482f14094004f310bd084403090102a710b9c44e630b9d026140b8502a610b9844e530b9904f040bc144f020bc0c4f010bc0841031140c25040840424001440055008840225008440215000a9c04e600b9c02a60139402e6041c0c31000d4010f76400010f6527d510f6037d090f622fc4c6f512bd4d050007d4c3f6443d010f51
    | 11 => 0x1b898ae26078183e174fc593f564fc513f544fc4c5e624fc413f534fd4134054f9d51e624fc193f044fc0d34004f9c19a60679809a21258863f74738563f768fdd63f738fdc63f708d01c16048fc989e213798e350453894be641b890ae24078103e158fd963f15879922e628fd8c5e618fd823406679897e608f9da3e71479863f058fc123f034f89634000d8143e058f9c11a60479813e508f98231008d40131004d400270509c0c270244401150064401950009c404f6013cc04f6213d942b7113d904f6113d8c4406100002b6113d4c4501114084f54
    | 12 => 0xd0157f545fc117f535fc0d7f521500574055fc097400858121e04869c21e708a9c22e70898162e05258189e06669c19e7073815c605918164e0514884562147dd9100047d889e6147d80de5347d94be541b990ae64079903e7547c911f1447c105e2147c4d1f0347c4114003580cde034dc1a3705518194e06518154e052d814be052d810be044dc123704198106e04198186e064dc0e370329818ae0629810ae04869821e608a9822e60169805e604dd413b214dc853f744fdc93f714fdd93f734fdd53f704d01c16064fc849e263799535044fc98be65
    | 13 => 0x894054f542fd0c6f412bd0c1f430fd522f048bd522f248bc161f418bc0e24003ad01170415c0c5f76140005f6017d885f611540c5f65154145f6417d8c1f640fdd45f0417c905f1417c0c54001ed41db507ad423b606ed80cb6067dcd9f7667dd59f7467dc19f7167dc994075acc19f6567d809f1337cc5950353d4cbf421bd0caf4107d083f5367c119f5467c919f5367c0d9f2367d419f5117c4d940045c0d9a5067941eb304ad013b5022d01bb4032d417f735fdd97f755fdd17f725fdc17407158057f6525004d4035d40d44052d0106404290101404
    | 14 => 0x294146f2329001db600dc0d01002a9c0ae700ad815b707ad808b6007dcc1f7007dd81f7507dc81f740501c100007c181f0405408150307c14150507c0c1f0205000b6062f818d6063781833210dc8437270dc8c3f21069c03f170fc543f050d40c3f160d4183f140fc103f130fc0c1e700d0010b4062d415b6056d00570487dc21f7173dd21f7287dd61f7387dd214077ed421f6087d889f6437d4a150153d90bf531bd84af6307d8c3f7487c161f4587c0e1f0485000eb6062cc22f708bdc5cf548bdd62f748bdce2f728901d77038bd962f6027c50df32
    | 15 => 0x35c18df0137c0cdf7634000df652540cdf0237c18d40048400a7051c4014f0653c154f7053dd14f7253dd94f7505c154f2627c954f0437d914f03510018100529c14e70519c1427019c0cb7022dc0cb7062fc04bf702fdccbf762fdd4bf7401400bf052fd94bf0425414b5022d40cbf612fc08bf032fc18b4002e9c0be701bdc06f711bdc86f761bdd46f7405c0c6f061bc986f041bc906f051940c65011bc946f031941464000dc107b604ad806a701b9c0af702bdccaf722bdd8af752bdc4af7405c08af062bc98af0427c8ca5012bc14a5032bc94af03
    | 16 => 0x30d424b710cc1c3b0786dca1b6238d82172316dc8572415c8c735074d41e35051c98972519c90736029c98972329c94672374d81e36071c90e3701cdc1d37078dc123700ac40c1006c400810078400970535c0cab702edc02b700ad022b7026dc06b7073c0dcf0573c11c40006dc0eb70384007b7076dc1eb704edc23b7032dc12b706edc0010029c18b70516d80670693c1a4f7073c5e4f7505c1a4f0393c164f049100097032dc10670427c149f7027dc89f7627dc4170427c189f2627c0c9f04250011b600dc164a70939c09a70279c1d10019c14d702
    | 17 => 0x28404330304409ae050c40c3b036bd05af211440cdb315c40911036b80931036b948410108409010336c84ab3162cc4730369005ae011c40c7b034840ce330004098b5262cc9d33052dc433062ec040f6003d880f6503d90bb7103d840f6301018000003c100f5403c0c0f530140405022ed840f0103c080f05010000e6003d480f51010140e050ec180e652ed44bb4103d080f3203d040f43010100f310100c0e640398c0e43038100e03039500e530040c050300410050442d88b71342d0873402dc49072374d00e35078d00971438d01972378cc13350
    | 18 => 0x404db016bc09af6568001af542440daf016bc14d1015040cb1021840cab71
    | _ => 0
  fld v 18 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 145) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0xd716070006c00000fc6b10000005de000aabd8640882b79dc66b88e6e1cf8093f9b34000b3037525fde70009e52cb29c6770d72a6000e93bde37a7d10003f5baf707b111436610003d0483385c1409fc3cf5209bb1400086cd9afb838e30951631b2657705c500000000000097d3f1c823cdf416150007eec030003066fc6140008a8df13517614353800002559cb8b1
    | 1 => 0xec400058a5d97990000003db000a234fd0009f51e118a90a0005bf35800037e191a38cf5d1ffbfd780009533c29fd1d389688f00055d7399cc70bbf980746805bf224395f21494dde2002e4209120000009fee5a12ba9723d3e6062993d5db4dbc5000ad80000000b33b62920007b9025000000e10844902561ef554010aa5d000819a3fc021ea8a5a21866000362d11
    | 2 => 0x9856a3c2bece4c887a46dedf2dfa3eb7000077a9eeb24d8b28071518fc9a9f300030e60bd8368075fe019a1aa934d0008710aa50f00011800096a8bd802000d2e00047993db8f043000000bbc1da0002950000004c7000000be3000271c34c8f000ad2f0ab058ecc14000a5c2a91c244e9e83fc9a200075b1470007c5e81435000cbb000e46000483000b9c0006b587f
    | 3 => 0x9bd3cb0008d445491c0ea7adc9eb8f8b1b992df303e530001191e74d9251d79000d3900039f325bcb11d0006f100055d052fe600012176e55630a593912e53000ced16f000823d603a151345739000088658eae8d8fecf6a0a91a25e0a42555434b1d25b2ad5259bff5877b1cd46e8a327b53862a7907aef745cb83321c100064556c8678804b8dc5448538cf34be2fc
    | 4 => 0xeb60002a252bf72b392b2ec110c00007a5e9bd1783000000c16079000ff7256bdcc0292842cbdeac300077f000cec0000a1a4a93b24df9dda5916232439000d16caf2e023d104d1fd545da924000d02d184f7a206c9a716a48f0000b75ac840a4187fa000f7046a4c05dea0338cac8de800071096d4fc17567c02e9afbe0c785f48de000dc0cc8d09477731953000
    | 5 => 0xa4a000000de3081dac566228561fd9000000b5ff0acd04c8363ddc33e82cc4c349fce3cee521134be694df388f2787ee000a73079d81d98537030a6d42849851e04bc99224000dc12c53e4e731a1d95857a8a05a0002e847cb8cd52398d9aaa5a63bffef10000a30000005f708075f000222000e1c5a5e36db2551300cd95ab1a320e8dc6adb576f3b869b00ab3b3000
    | 6 => 0xc400000004f000059c40e0000000000006c100054292dc69d7cd81037c2e001f5913f88a1d53250009393810000004f2000b4ab5e16544417781a323000e330c254666f5bc649748c99000f5eb86000030cdd68f000266e84aa8eda2aa000801dfe000b11906000dee9fd5642c0bc0830030fc8d8f29d3b73b42d0d94a43d0c6267bd0004a5e6262de37e679834b00cb
    | 7 => 0x6b6e1700020203c0004384db4fc00002ec0b2e18d20002a20000000988a0a7eb9b438890360c51fcc49a1e94e00003a7dfd6c330a7d433100250837f0004f3e180f81be71baef6220009b10005dd7ef0001370006a67a649fb072b079d13f9248bb5cfc17dba31a0006601fd000ce900050e0623203be93c00000087b646000b4dd6d54da55a3700054a000e42168f70
    | 8 => 0xd0bcb02a29dfb1d0002c3aade8d7f3f82a4ed2a0ac000fe53ff5760001a63f31ef72e77229a16500000022de9135edcd42b3325f30cd9b270adcb00000000000000b00014dae0173f1f5b27c60009db000c12fe300042624a900a9eeb65d4c2be83b02425d6671aa62f8210879a8d744650ef0e617df52c67adbc87a97f5635103b10000c90d4157447a4c74927f11d4
    | 9 => 0x243ed7dcd000e19cfb94f5ca3699d2d865e978a33900091e3d35690043e800009cbd70898842e59370000900008aae8d72a98efb6002ade00017c00060da067240000000f7766000e50000000165f1aedd8795190004056747be1052180007fe7eb4292eea0c015f4f0ba517000739d3f0fb000000000b36ca692eae0b8cc07b2700012a5612f2571b821fe6c2e54daa
    | 10 => 0x81a0000003e7c044b25ea7f45ec5faebe42cd7b0962082127b842c43b000549455000c57383000543146845439fe8eb0fbc0ab3580005adc5c00008a5b0056000ad1e02ee611206d44d85b92337a069000422f838d3315374dab7480003705bd5a45245d1e61dd7cd99961fae9b6bca486cd51d8e0795000b0c0002d386c2ba0002287378171aea086d2b12b5711789f
    | 11 => 0xdb45876eb2987464fc1d910a3fd8e828a226c254994100005fe0d92b9000cd69b769da84db8795000af0a555462688af4a800069309286c5a694b000722de0c19778737829dbd3a4548d242f00005d0bd63df50f000ec433800048295e00076a53501200033f0001ce6edaddfe7095000655000000b8d14f1bd8fa73db4e230a3736f000d186d7da6e91dff3fe10e
    | 12 => 0x99086e18afe441000000cb61ac399c26e86000316c866a234e000b0a11c2943a0d034d20434c7f193588a90006566f7ae31e24eb000000714af7000221a63000262af50c263beec0d40000e91cf63b6245c00c800085daea13f2d3bd3a350c70acbe5725b1ee5c53fd9297ed12b75f7a02300000047c99640e4a2000cd4b627ad9deaa934b6ec21e000fe4000f437cb
    | 13 => 0x542e86fc6706b67fe966eb9b7d338fd7d8520f733ec25c42fad000667e2b0d800007f3eb986f9b7b7f99000b2d6c418600030f000bea63920372cb339ee26f9510b30da978ebd41d00000024b4deccc5ed000000f51a9f4f9502872f230004de78131cdd8d7a3090008150c9000a6c712563cf0f487db85607300008d7d2c1ea6f00044a2200003de072587c5a13f03c
    | 14 => 0x1b2000000a287e90004d9150000b2524a8dd7ef4750f56fb1083045144fe00077550973db4b8ab000101116575efb94267887056c4738b8b7364bb5309c52b4df344000252fde3ab96b453df6000aa059d2236d676166283c807164520000fb1000dd130fd6a200557fcd0000009f7281000adc000a7e00096500044f000af45b4a4b5c8f3de990000000006be59784f
    | 15 => 0x8f4b65aa25c2af50c1d0453efae60a94451eed030b5eae790000001998e460f082783000612000814f629d3000840951de6000d3f0000003c57f82f30000000002d4ec90390005900000b13fb8860005fcc7d83e4f1fef300a9c89d5831364176745de45f92b1b18146c5c99b5d254000000000fc9dd90008467d16ed0d477c209ea3000c79cbbb1ed9b81f61c0004a5
    | 16 => 0x6fd7bd7d8714cf1496efecdf55f000000000a300f62505ec38b0bd0002c130bbf9ace0b73790007cc000f2cd5c14500024bb870002cd31c8f26ba8749976cc39bb68eeb000701cb1526f98f10000735653873724000afa0008c1c22fd360af941d66fd852bc527f3e8000feb6755fc000fd3f56000e6247da9fb7f00055b0df23fd70dfd5bccbabde000f1165769a0b7
    | 17 => 0xf809d039060fd317b8050005cfb4100079a000a96e2a9e93b30b6b86f2c064df66a78209e0d7ffa3bff20eac049c4f4b66000d3fb3ec5d529cdd9b500051f38e000f42fb04dd3bfcfb9748afcc3314e1f96800000015123f674000997a2576b5487358df3cd0000000be000754bd9000e56e1061ee524283f305991bbca94b8051093da6e7faf0001943cc9d7000b1e
    | 18 => 0x689fad5f2a88659000aaae3c8051267dd0000000000000abffb6ea277000000000000526265000d7600026400071fb73d479b5e7359b4d80003e0455865a354d7692b1d134b0cf17000c13206b6a751000c3a000497000e334565dc05b85600047b000512c49707845a027ff0002a5188fa0000a113558ad3a4b75000da13f300700096ff49032120eed000e60be9000
    | 19 => 0x1e9000000000457614214dfb00000000000039e00001407d4da4e8b512ba42c000dbc14041808d6f29cdf19000a792ff30883f1ea0ec4c6000212fd98c70cd2f374b50439500926fb4a0004d4000e38073b8a5630920b50005911dea74583fae000cc6d94000f5ecb5bd8c7cbd80001500000004e659988e000d76000b7b760a56c683c3000dc4000eb86511a5118b34
    | 20 => 0x65bc822b2000f2d0006d2d260002aa000d732f76e5610000ec90f512000045c0c16e8f6060600ba0f00000035e9e3bb8658158000d107e268bb7f0000000006c3965620bb93e9a922fd000a9309f00000012b57500000028dc200005a02c80004296106cf00004edb7fce8479cfc74839000520d7a3b25a94c3f5950127c8389c7000f8c51dbe92c91710007d37c1bf7
    | 21 => 0xaf2df860c524ded0005b60002db67d0000fc19de9e0f5d3ef7f5b08d54b2141917dc600095b18b1f5aadb412716a1000b7eb050000000004bb000345000000321000cc16b5105000000298a6b000000dbd3aa3887704368b5ed10003b500029fa0b1c30eb1c0000af86f3913a0729600037f000ee58900000006fa00057f3ebe3f14df02fa9f24befdb39bf317
    | 22 => 0xfd36c14a2319ad80000000000004fc0009b45dd00017faef000000fee000c3f2c12a40001ea426bc41a824e4990003980000009df0002e45640006ed9fb000000000534000086685113b453113874d46ec000000101e3c0001d20001ab0004657923bdad400014b000ce871f000000b8600075500015c017cc205f0006cc62ca2900045513eac7cfb305230918dbf000
    | 23 => 0xc89c65c335aa19500000079d6e880e00077b000000b640008613ab236584e6c0006ec9cf8e124c3a63ebce90000930e4f3a6a27b0fc9b165bdb25000ba400052d00000043fbe42771358436f28ce00000039e239aad70aa47caf00097ffca662639000000c12b1797b0006ff000a044a700000000000052e47cc4800095a0002f9d9a000f8e0000003f1f9fab50007e3
    | 24 => 0x209b9f09a024dc79500000000000009ff28e372a6e418703039b0c212000e4800070cf54dbd6e1000921000a3db8757b000bc27d06a6b86f16000000151b6f338eb8311e2843413d0000000bfdbb000000874000000e176de0b450a00045f4c944dd3773b000982fd6000000bcfd6ef89502956f7234c000000c52f479db00026f05b0000009791fe81ec125d22c71ca
    | 25 => 0x74e005ea074951746302d8250003fdd0d48acf69b06cb5b5982f484ead6f27a00028a45de2d000000e1f97d000dd4000b8815dca5083a486d05dcab70eeb529c03e9000d3500000000053510e0ee7d549377298cbac80e0b8b4f000438f4f6d6f89d8c1db000576170c843edb5e000e8a08a0000005f70002440009b94ff1348a8e4ddf33b34b964fd384bc73d89a3cd
    | 26 => 0x948ce093a4f83dd0000002ae3576e9ac50006724310000005d30575b7d85ba0495b9b00057827d00038c221a3efd63ff87175c578c0d161a1500041f0000000000000007bd000422fbb000d29db75c77331ab298000000c580e3d57b24000c589fbbc8487063d70331bbd76382b000fc5b1a000000d2e0000001e4db56ce475a16000000000c131b893f21f23a9bb43e
    | 27 => 0xb0752e292b9b75b06338d5260002bc3f8c1e00098cd73000f2c051e970bc63f46e619b4d0006b2be90000005941a480d993046186000d186f803c421699d9b000000c7eb8800012918c000d9d00045bb3f00000067151235b000c879ae9e200000002ece10003c5569000202000ab0c6bdff00010b061e44000fea000effc8b000975c500000003b7612e52000dbc000
    | 28 => 0x7559dece6230c9a1a70dd000bb14b301221a1385b1675bae59a826a1e4a870551221f7bccc869b00000089a1cef9cdbf7a8338afe7f710132982b8d60005625b624f000508cd700032b95aa7a1a8000fdb8b000052324100003781500012fadc657c17378fad000d37f750000004b6000cc317d6a3653000c80000d60daa567000aef9e75591b92bf00025630166733c
    | 29 => 0x46138f2074e12da93adb0000ca658a77e6e305f9200007090008e70007d03b89f0dbc5d3b90c66d98daf6d1c1a00000a7c0e1f000e7dc969fc000682cf14e6feb419629cb4000000cacddffab9a6ed40008a4726000870179000c654440000004f190e000c3535d0d7000cd815100040cd8323ec47387000d903602a038500003beeac0a00062d7bf3730f2000e4a335
    | 30 => 0x66867000075b000000356a5b24e0008600000006bf9a6f7fa7db146603adaa8000000e7bd59c79000000bc1db1e432d2dc835225311f294419ca16b0000dc89d31c1f73101223000262000b290fd3780b0fa8cd8a0e0003d630c668d2c0001bc1e00000004fa42d4300005e3e3071f0004a10969f02f0115ef673d000dbb3ae0006508021940000951e08eb06d4aa15a
    | 31 => 0x7b4f32131310658c242e91e2b2102ce630005e30002f7744000ddd903de9658ffdeea9d50c0000000b1569f1db0005b0c76afcd1a431efebefa6ebf9000fa4000e81c9eee1000613faa0d800088a9077ae0b3000000e6ade3d660000001928fb44b000b9de269ecca0bbe0000a34c384d364d26197333eedd329ffc71695dbd984e13116a4053def08d1c8a278e70757
    | 32 => 0xe55d372719303ce007fadb2b7db098519af91731098602781e5a1a7ef0c70003af3b647750acfd9db
    | _ => 0
  fld v 12 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 1033 (hk ys)
def qPick1 (ys : List Nat) : Nat :=
  fld 0x4 2 (action2 ys/1742)
def qOri1 := quickOri 145 2 inputs qPick1 qRow qWord qBook

def J (ys : List Nat) := action2 ys % 1742
def r2 (i : Nat) := bar 145 (cutB 9 (B i) C) (cutN 9 1742) (fun _ => J) qOri1 [] 10 0
set_option maxRecDepth 10000 in
lemma rp0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp12 : span r2 1 12 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp13 : span r2 1 13 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp14 : span r2 1 14 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp15 : span r2 1 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp16 : span r2 1 16 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp17 : span r2 1 17 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp18 : span r2 1 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp19 : span r2 1 19 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp20 : span r2 1 20 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp21 : span r2 1 21 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp22 : span r2 1 22 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp23 : span r2 1 23 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp24 : span r2 1 24 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp25 : span r2 1 25 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp26 : span r2 1 26 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp27 : span r2 1 27 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp28 : span r2 1 28 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp29 : span r2 1 29 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp30 : span r2 1 30 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp31 : span r2 1 31 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp32 : span r2 1 32 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp33 : span r2 1 33 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp34 : span r2 1 34 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp35 : span r2 1 35 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp36 : span r2 1 36 = true := by decide +kernel
lemma secondRoofOK : span r2 37 0 = true := by with_reducible exact (sj (sj (sj (sj (sj rp0 rp1) (sj rp2 rp3)) (sj (sj rp4 rp5) (sj rp6 (sj rp7 rp8)))) (sj (sj (sj rp9 rp10) (sj rp11 rp12)) (sj (sj rp13 rp14) (sj rp15 (sj rp16 rp17))))) (sj (sj (sj (sj rp18 rp19) (sj rp20 rp21)) (sj (sj rp22 rp23) (sj rp24 (sj rp25 rp26)))) (sj (sj (sj rp27 rp28) (sj rp29 (sj rp30 rp31))) (sj (sj rp32 rp33) (sj rp34 (sj rp35 rp36))))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp0 : span t2 37 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp37 : span t2 82 37 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp119 : span t2 84 119 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp203 : span t2 55 203 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp258 : span t2 55 258 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp313 : span t2 22 313 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp335 : span t2 36 335 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp371 : span t2 44 371 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp415 : span t2 14 415 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp429 : span t2 31 429 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp460 : span t2 29 460 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp489 : span t2 43 489 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp532 : span t2 37 532 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp569 : span t2 38 569 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp607 : span t2 26 607 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp633 : span t2 10 633 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp643 : span t2 43 643 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp686 : span t2 71 686 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp757 : span t2 41 757 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp798 : span t2 12 798 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp810 : span t2 60 810 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp870 : span t2 15 870 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp885 : span t2 57 885 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp942 : span t2 45 942 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp987 : span t2 63 987 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1050 : span t2 28 1050 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1078 : span t2 100 1078 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1178 : span t2 53 1178 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1231 : span t2 78 1231 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1309 : span t2 79 1309 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1388 : span t2 20 1388 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1408 : span t2 70 1408 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1478 : span t2 29 1478 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1507 : span t2 36 1507 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1543 : span t2 46 1543 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1589 : span t2 16 1589 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1605 : span t2 11 1605 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1616 : span t2 12 1616 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1628 : span t2 8 1628 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1636 : span t2 12 1636 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1648 : span t2 22 1648 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1670 : span t2 24 1670 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1694 : span t2 8 1694 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1702 : span t2 18 1702 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1720 : span t2 15 1720 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1735 : span t2 7 1735 = true := by decide +kernel
lemma secondTestOK : span t2 1742 0 = true := by with_reducible exact (sj (sj (sj (sj (sj lp0 lp37) (sj lp119 (sj lp203 lp258))) (sj (sj lp313 (sj lp335 lp371)) (sj lp415 (sj lp429 lp460)))) (sj (sj (sj lp489 (sj lp532 lp569)) (sj lp607 (sj lp633 lp643))) (sj (sj lp686 (sj lp757 lp798)) (sj lp810 (sj lp870 lp885))))) (sj (sj (sj (sj lp942 lp987) (sj lp1050 (sj lp1078 lp1178))) (sj (sj lp1231 (sj lp1309 lp1388)) (sj lp1408 (sj lp1478 lp1507)))) (sj (sj (sj lp1543 (sj lp1589 lp1605)) (sj lp1616 (sj lp1628 lp1636))) (sj (sj lp1648 (sj lp1670 lp1694)) (sj lp1702 (sj lp1720 lp1735))))))
lemma upperDead (i : Nat) (hi : i < 37) : ¬NatRun (mask 145) (goal 145) 10 (B i) :=
  symCutRoot (quick_safe (k:=145) (bound:=2) (xs:=inputs) (choose:=qPick1) (row:=qRow) (word:=qWord) (book:=qBook) qCert) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => cpWith_sound stopNo closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 145) (goal 145) 11 inputs :=
  symCutRoot (quick_safe (k:=145) (bound:=2) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 145 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row28

namespace Row29
def inputs : List ℕ := [0x4b012eacb004b8e5802591f005647c1149e0000001fff80007ffc000007800001e00007,0x95ab54055009502a98ea8f100aa8852f1720007ffe000000000007ffc78000000007838,0x2ae602980a60126053205322253cc3c8f23a5fff8000000000000000000001fff1e0781c0,0x3080c2030833c818409e470416d1c10ffc0800000000000fff80007fff801fffe007fe00,0xc103040c1055d0ae872880401ae1fff0404000000000000fffffff8000001ffffff80000,0x3020c08302099e0cf07cf07ffe3001004020000000000000fffffffffffffe00000000000,0x3fc0ff03fc0fe00f004f00488bc0122288801fffffffffff0000000000000000000000000]
def vals := sampleTable inputs 290
def scs : List ℕ := [0x1d46720c9524891,0x1d4570e8bd258a5,0x1282015c9924c92,0x19c20128a524c9b,0x20c3a1d4bd25499,0x1d44a19ca524496,0x20c3a1289925895,0x19c20128bd24c9b,0x19c4a080a5264bd,0x1283a15c9624c91,0x128200e89524492,0x20c3a19c9224495,0x15c3a20ca525496]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xa368c0a3a120a52926b188e4d165344ba127e5e9308025375300d460a33403a9a4c9812449895040cb078368cb6368c1cf618080453063a120c00534262ec045e12045292469695420a6d4cd6120c3c12820ab05ea612543a994a10930e0a530e14c95f1653405e930e3a124d08b3a8928c10a808aef0c95e98120e025304368cb2368c8436970c4212440a9308085344a6120a0053463a715c102b4c98466b165308e08c16e8189c4a127e088c4516537e4a1244ba940a3c1244d693431e5340d62644981253280246d6124cdc1d451c019a36977e3c12344a8f20fac944a692000a8b4206120e04b01cf4186a9e1206368c0e0853404a120e0053449e127e4a920e0a8d9c4212571e0d5ed6120e3c1244989246106820f4180c3a930c0a5320f6180a08b01a9297084a12043a125516530e42f3b8368c52cc060a02532a02080a30686aae120e42120a0453083c121a42f34716537e5293404a8f0e3c926ece18571e8e7a368c4002124cf4b70e040daa36970e0c534cf4180e1af3549e12
    | _ => 0
  let q := fld packed 24 (i % 128)
  (prefixGates (q &&& 511) <<< 24) ||| (thirdGate ((q >>> 9) &&& 255) <<< 12) ||| fourthGate (q >>> 17)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0xee3d7b0cf6d88ebbf004a2745657afd8a9c3f307fd60e21941a083f63d84adc9ee3a4aaac43ea22db62a55c47ec0d7f3a8c42c323e61b4f9859ab56bd5522a2535337c9e712dc1e4094d637fa983dc1c466217337026c63ded03afecd39e829e5eaeec708e4154bd6dfd3e7f5eecf5e9c3ba68166a63d67e13d5b961fb5faffa
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x1d4c82ac075dcda1821090ea54042508b39b29449046d2efaea0428828e94d2a0c120d7982a54950eba12087383b261c220aaf204c2ba48250e0ab72949b38612c243a5b07341484a7960405c57283a2cc8204bead6b72443d5b9ce38d18808aea487a34103a1d498404845de5e3a6e0897849588414c904584219c7424928c08720391820ce20f3213683a555c86a6127223423241d6e96460722b899c11e60a8b063682a20a4b85e92030c358486d1826851d4925a50751e0ccb261f8333020b84b338b2952834109e0c95885b9c4b93c240cb0025812848798c10861d4d032ddd0760a402f4a482c04de20c3a29540ea507634be84238403bce20f659081b4410bae1431300d2536af19d4c22ae12
    | _ => 0
  let q := fld packed 17 (i % 128)
  (prefixGates (q &&& 511) <<< 12) ||| thirdGate (q >>> 9)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x143d165bf6d82c547c07a2b06486f557a92354f2fd2bc5374886b26d3d3ef999d03aaaaa328dd6383b8f4087f2ad7df3a8c422904d61f8f9e406b56b7e31b02530ccefd2dd6f08c393cfee7f88b3361caf41175470f6a4e7ed078e5ff04ed48bdfef8a7f8e41587a36d5918e5eb678c808b269fb8389d065133fd4d42af236cc
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 128 else 0

def board : Nat → Nat → List Nat
  | 7, i => if finger7 i = 0 then [] else cpBoard (mask 145) inputs 4 (recipe7 i)
  | 8, i => if finger8 i = 0 then [] else cpBoard (mask 145) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 128
  if table i == h / 128 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def x8 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x84804aa015b00d754062d41006a5c9a980317041940296150070e9c3e72756e1870bf86b8d8d00020c93c92b8f7ba64055d5b8082fa0a62e9000280401a20393025f7be1b8276c8018e0c9c45dcb0df1625dbc4023069ee34d837720c6067b86
    | 1 => 0xa06dd70624464c611817840c146006fb1eebfad36b02a314d57c081823ee0a046948091d29842d025c1888b452e0136d45f201002c404192335e000709fcc8afe0912c074a003e389c715d5c0203e18f307996110c27608c069861ca09a08f04
    | 2 => 0x86a901000cc519256e5800884c01a03bbaba060a2ff341808000904311f8db7182a989cae070148ec1eb580fc21e981263a5483080b56324781c13f3c1f0048a9631583004540460371543c3a7f0a2da1e5e2007ac6824b037e74d0197647a0b
    | 3 => 0x70803668620021900ba21b0290800016dc79018e1202b44580aa151841c1200fda94921866db430ca300ea96622cc34b09800e29807800d120a7d32e4624fe2e0319e6005910300b1b398d298140cd17f8898e43081a584e8eedd18d2e099a08
    | 4 => 0x7c69584bba089974001d8029040b184cf646640834625a38812942a80501e684042676832c03544c34350d643058d289622d1e0a8454513000cc15c6621f928450332222280010ba0015f02b81780f5d00cd334bd8be02209b0438881855d650
    | 5 => 0xab2230bd81600c2e387404a5f9ae14012e7d1181a8e47802aa202ece0130c060070048c6d5566d002e000852f1143c2017233c005ab9128228e12409a70e08c00c207c64ec1400029c203f228044b5a0c0070a4641c32898e040220182121bc6
    | 6 => 0xa797000035074480cd763028fbf6c7001830b512386d84c3d01432428745c60e403c30002b388641e603e380a8dc0ef51427ce18e040a3004040180ef1a0107c07642401988223d2cce2e8601120158478007209f43428a03dcac5b3c3503758
    | 7 => 0xb820f83df3d6e898a442157381c021b64c13b28c8878a38d71221808078618445500c200002a08f217c1c055a980e1f20429ba68e7920c810c4a6bb20d407af4e7fc1c18118541d9aaa900428805cf178041403ab37040390d9009c4c015d41
    | 8 => 0x9200900854ac8fcc8e6058e1c61e800fe7e0f660b15bfd1a80829000541eafe410d90a002cc041c4f0100d
    | _ => 0
  fld t 3 (i % 256)
def hint8 (h : Nat) := orbitLookup x8 0 721 h
def x9 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x3b0816a32404411c94c04961d72fe29b6676c11acd9e0a2820230c0539f08158ec430b86c102110d005020c46498344c11078085e60884376207bf548dcc30900410134789c115019e24716ac0014034b00460360502f23f023218249b60403
    | 1 => 0x8407c70c3490e6084401180004803408424877842514894808a8680422480faaf3245c2541c1a71414380d66561e76f20148068cc0876c840836860017dc72f5f1132eda01204654034c19c137803904a109817f10321d72d1a90007408155cd
    | 2 => 0x1d754967841015fe0a040be0758a097a8
    | _ => 0
  fld t 3 (i % 256)
def hint9 (h : Nat) := orbitLookup x9 0 185 h
def hint (s : Nat) (ws : List Nat) := if s = 8 then hint8 (hk ws) else hint9 (hk ws)
def labels := 0xf400000000000001ceda0000000000035c00ca0000001210031d86bd0000000bc0000000b00000000ad0044552a50000000a30027e029b00435fe837f1d4ce640000000b90034dc65700001c4ac70b1894470034800a2688e98437003158299600cc5e2d002dd6c2000279501d002ad4e19532582a1300275400f4e02d26090025524064880c0000
def cols (t : Nat) := fld 0x2e71035e811ae6055d1a22ccca163c42 21 t
def u6 := 0xd70000000ca0000000c70048586bd00000009f0028d529b00435fc757fa0cce6400349a23a00289843700315803360a645e2d00275380b5003d2609002552203490180000
def rowIx (t v : Nat) : Nat :=
  if t = 6 then fld u6 9 v else
  mkProjection labels (cols t) 9 v
def rr41 (t : Nat) := (List.range 176).map (fun i => rowIx t (fld 0xd30b289a54891850f2c2aa268d2246143c70a689634891850f0a3cc2879d4891850f8699d16571c286554d2246143c12b0e370aa869238b246143a091854860c91439249249249249249228a28a28a28a28a286186186186186186081c71c71c71c71c71861851451145145145145145141030c30a28a28a28a28a28a208104082081041 6 i))
def graphId (t : Nat) := fld 0x0 2 t
def qBook (w : Nat) : Nat :=
  let d := fld 0x152235008201010d6c910c09002821022d2d003a1d0c0977c91500023d0315070b06b90b1001042c0204150f07090105190f2700000013010b000400242100040101090a00 8 (w % 69)
  fld 0xdee7c0be7188cc9c1cf3a78108cde06b350838c09d64f0a70f8ccdc56b3a2c18c0cc04a830c1dcc8b06ebd1918619e000823430ca9c640ba0c13c00006e1b18938393020ab7410239c0411d08b4c0941231f0d7b80d47c3391478c28a223411418428b3ee2b983bcae50011718106e810022b3051d042566811548a08e6f3024d7061c46f28d1590c1dc6a313715b83dc2631d1868464515342041880d55ce150800a3de36f0a3408849e622b514d820e53e083985180de122969553c0a60212d18c8c8dc5673e2c53caee14995180000cb1574270338f837cf391818a2965659378f880c15a10605906ad45ef010211708300317041186424228218386ade7430f105b829d421000014a5455cf2304306ad30652310988f4202196b878639d0c5890812cb866c0833815ca8b521011db0c445069b90948c0853ef0270d860cd261930468c0030e08b7968a08a0231710116007 13 (((w >>> 0) + d) % 209)

def im41 (t : Nat) (i : Fin 8) : Nat :=
  if t=6 then (Fixed41.raw ++ [0, mask 88] ++ [0x3106204437470620eee304000000001fff0000ffff00,0x80000000000000000000000000000000000000]).getD (fld 0x65498120 4 i.val) 0 else
  projColumn 88 Fixed41.raw (cols t) i

def okTable (t : Nat) :=
    (decide (validCross 145 88 inputs (rr41 t) (im41 t)))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem rowsOK : ∀ t : Fin 7, okTable t.val = true := by decide +kernel
def passed (s t : Nat) (ws : List Nat) :=
  crossHit 145 88 inputs (rr41 t) (im41 t) qBook (Fixed41.index s) (Fixed41.N s) (Fixed41.S s) ws
def stop (s : Nat) (ws : List Nat) :=
  if s=8 ∨ s=9 then
    let a := hint s ws
    if a=0 ∨ 7<a then false else passed s (a-1) ws
  else false

theorem stopNo {s ws} (ok : stop s ws = true) : ¬NatRun (mask 145) (goal 145) s ws := by
  by_cases lev : s=8 ∨ s=9
  · by_cases outside : hint s ws=0 ∨ 7<hint s ws
    · simp [stop,lev,outside] at ok
    · have good : hint s ws - 1 < 7 := by omega
      have sel := rowsOK ⟨hint s ws-1,good⟩
      have hit : passed s (hint s ws-1) ws = true := by simpa only [stop,if_pos lev,if_neg outside] using ok
      exact crossHitDead (of_decide_eq_true sel) hit (fun i hi => Fixed41.atDepth s i lev hi)
  · simp [stop,lev] at ok

def ck := cpWith stop 145 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma p7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p7_64 : span (pan 7) 64 64 = true := by decide +kernel
lemma good7 : span (pan 7) 128 0 = true := by with_reducible exact (sj p7_0 p7_64)
set_option maxHeartbeats 50000000 in
lemma p8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p8_64 : span (pan 8) 64 64 = true := by decide +kernel
lemma good8 : span (pan 8) 128 0 = true := by with_reducible exact (sj p8_0 p8_64)
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def qPerm (i : Nat) : Nat := fld 0x33b023a3a42ce5056ae2074aca000000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0xf400000000000001ceda0000000000035c00ca0000001210031d86bd0000000bc0000000b00000000ad0044552a50000000a30027e029b00435fe837f1d4ce640000000b90034dc65700001c4ac70b1894470034800a2688e98437003158299600cc5e2d002dd6c2000279501d002ad4e19532582a1300275400f4e02d26090025524064880c0000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x2c688 3 (fld 0xa642008424c080416a3045606004d40410d260b00b68b011 3 (bsr 0xfb1e0242e5fbb754e4578a26dedbcf48db58da58d6f67d87d01a17a5cdcb4769cc699b04ca2bb017c75a8d58c7065f89c36964cdc06437d3bf7ea796bedd3a3cba2a6b7eb9d5cf37b9c19f56b87ddabdb8150e95b297db70afe0a9b8ad3abd9bab3198cca40fb604a33e10cda11498099ff1daf193c305ad9196233f82cdc3487bce97e879c9fd3b70d90a6c6b5bd747656919bf65250aa663039633607708f15e4112b15b37383a589afe2c5230a7b74ec3fbb14c26dc6242d98db4401a06353937667136708df531b323aa2e2779bc2b6cd9ce2a222d6b29b832402845105b238b879f1e7ebf48129b800a0eda5e770ccd94de0b2fc92f07ad7b9b06fa3e4d 32 (hk ys) 7 0 64))
def qOri0 := quickOri 145 6 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 6, i.val = 0 ∨ validQuick 145 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 145) (fld 0x506f30f31e30502f43e10403000e63f60e43105505f63106400406102e40f10e60 12 i) inputs
def I (ys : List Nat) := bsr 0xd6f67d87d01a17a5cdcb4769c75a8d58bf7ea796bedd3a3cb9d5cf37b9c19f56b8150e95a33e10cd82cdc34879c9fd3b70d90a6c6b5bd7475e4112b1589afe2c4ec3fbb136708df52b6cd9ce2a222d6b0ccd94de0b2fc92f 32 (hk ys) 5 0 22
set_option maxRecDepth 10000 in
lemma roof : bar 145 (cutB 10 inputs B) (cutN 10 22) (fun _ => I) qOri0 scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x1720839844a0e210717118b9445c622e6317298b98448000a6007300b9c014a0ce0307284b9c214c10e60508228c854204a72152802bdd55eecaf733f30abdc09ccaa00052822bd954a04af6157b1abd81480cae7657a8abd4d5ea0a405573aab9947c86a5054f2a239955e42af145789abc415ce2ae510f2a2bcc0bca8ae530732a941cdca8ae135721ab98c5c4aae6152002a9815cc0aa7067302b9c15ca02a6017300a9425ca02e5057180b901f4c0fe6017183f90254812e404508458423c208610470857842ac20fe30
    | 1 => 0x7fb0bfd81e80cfe767f9a3fcc5fe60f4037f39bf98c7c42f5034f10a38c9fea8ff427fa0bfd01dc64ce430f1097881fc620e317a839b885fc82f4000d300798274c13e606702028c01c60fe70a5285394042022b211081884144204272113b0094005ee82f7617b98bdc85ee22f7517b80901c400025011281894145ec42f6412810bd945ec62f6117b0090185cec2f4217a28bd0c5e822f4012020b9d05cc821041282084184a0c2f2517918bc845e402e7217210bd4c5ea22f5012028b9d43ca22f3012018b90c5ce62f10
    | 2 => 0x37881541ca20e0502008155000c800750038802d40162013a509f2856882bc406e108b010f8063c0536039f01869003c8106038701c8406564321028309c9c864e81276093b8494025ee72f755f289f84e5ee04e522d20494064a052f6597a2cbd0c7c631e424f20a394a1c272f5397a8cbd42480b2e759791cbc85dc04c6136709879065e6124039739979001ca325073720cb94e48015a50af281b9028c074e030910bc4082c42f1057ba83dcc1eec0f7707a803fdcdfeecbe313f21bfdc09c645a207a813fd8dea0aff64
    | 3 => 0x58815400aa085f652f9a97cc868025503288315418bea85f522fa815014bcea5f422fa015010bce814012a01150010c049e0147011f80cec060b210080804140e420f23079303c841e4a0f200000014000a02050507bb03d181e86010402820041c0a0e0f6507b183d841ec00406071303d4c1ea20f500202838941e620f3002018388c1e200400ab882c408e2055f105a811d4088a00410030000d418620d15073281a54190a0e650630834141cdea9350737a15141cde835f5037a03941cc808c50260810541c220f5f20
    | 4 => 0x72002e815640abe055b02a18153c088e053d10b04058e28c75063b81d8859e48cf265f129f8849c0a46056281b14018a02cf7667ab0f98d8a0a9e64473ab3d859ec0cf6467b1b10199c4ccf14678233c4d9e06cf1062004e9027c8116041f01c7810220a1f730fbb07dc03ee21f740a03840002a0415000fb1854143ec81f600fb0850183cec1f340f9807cc4220615030883054183ea81f400fa107d0428081e740a0002cc034601e300d38079c256602b305f01ad80cfc087604ad902acc0a2085f722fba97dc0bee84402
    | 5 => 0x5b04ad40fc0c76065f032d81914809e304720429421ca01b409882cfdd27eed3f709fb8cfdd57ea67f1427a9b7cc66a0735019a814d4027ecb35059fb04fd8a7ec33f459fa04fd087e651f434fa123d4e7ea10f149fa9cfc0e6800c7049d384f9c29ee74f75a7b82fd44fe264f522da0514068a054500a7b2d3d147e631f424fa0a3d4a9ea10f13a7a9d3d469e073f23a20031c0c16a14a70a73856d41f6802b5077b9bbdd5680a740122029d805ca04e50077b2bbd146806e5044a0221015dea0ef5377a939015de06ef02
    | 6 => 0x18000d40a36c23f501a820fd4c7ea234051f32c5c522e251f108fb8c7dda3ee0b5043a82914106a0115038fb00fc0e3e083f018f810d00228011a701f30479c234c03e508f3021c090e0a87104fb1a2dc53ec09f6138839041d20009502438a254150e2a8712478823dd11ee28f7047b91d41c8a0e80004281a14193e608f4018828d4152a0685044f80a3c093e088f054080a100114e09e60473841c0e1eeb0f7687b82fd94fec24f656fa1c14121ec1050287b0c14021ea03f438282a7d511ecb0f03820032d8214e10e70
    | 7 => 0x2ed458606cb0318814edc436641b429da14dc8c6208910585b942d4a0e46f35061a848d01e660c37091b03cd8046c0b7233b91c8dc1e6e08b10508008401e20121000db822dc16e0d1b703b831dc0d7e06bf065f91afc15680047023f821fc18fe487f263f819fc8ce800470595b83edc156e02b70278113c1488000b2001880040216c0110060805040262011b6080803ed8056c0ab6045a042d4276801b307d980ad0156a117048b8145c4236e23f651fb00fd847ec63406
    | _ => 0
  fld v 17 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 145) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x6b997e0ee21e04d79c7d8920000000988000d702b366cd6dd12123a86e46f65960002e51613b670b102cac6ed4464f00027d602ce552550000000365197e56e0000cf00017da0001f62220f0c508000000183ab575b7bc694e42d839e0819240000ca8c5fcfe0fd42750001f0fb6f0005070f001ac18e80017b2b53bce2668260a140b48f8c79a7ed7a502a9648440388901c0008ee549b465c2e8b1
    | 1 => 0x6010001af2df54ad99e68fdf047696c9421e9bc00031d8000000c9336a4478fee1b91d54fb20004d692ded460000a7998cbc000017f800000000072f55dd2301fd0fdac2000006338d013215ea0d00000023e60005be1c2050a6d95ad3d70c462bd15e3529c961974439478001b28376a171b3cd3dc1cbbb4ead8065ed18f035ec736e20208001ee92f5c7bc94089518a80010a600017403ac00008a
    | 2 => 0x23b1e94b2e86a1f58c28bc00001cf12945d091e91ea56a496c966fc383887c7d400c2df800068758e1a742e6a9c237000152628000036382381900003ffc000feb64b3f28a509cc00030940007a600053d5a9ef4ba3407eb68c20e352247c0e28ab53ab90d3485c86f34e00ff099520d33443181cbb12800001a4bc685a9dc0004040000ab932dd954019ce4001d784fa8001b0600057afd54000d69
    | 3 => 0x8a59d0c0013032040001582d591939a3872aaef5710b48a360980b93f9d7a200013e000143461f000233cb94e0b1393864e809a91dd0649928a785be23d54b26e01a80e19aa00000961d905780002313fe04a3d5b77616fcf4673185916450aa0004e3dd0040a00049d16688aa53e44ea54cdf400082318ccfa004615f1b49b8e13800d80742da5c72a52675f5aa0a00047e13741a738e0620b26bf7
    | 4 => 0x78aa7507a612503a0000d3b18d33ca1d687e0fa2e128b8000bd95ef746e99a9fc7fe8914000c722810cf40008d30833ec1d3c591d1dce6d416c3e113b35cecee4a36d0a917b654e4f38e24f9525ae808001f140007b62ba5762a9c0bd0d2418f6e982408138ca7f993ea70296634939f0a8516217570b8cc8d729092e50002ea246259cb274000a090740001988c3e0b80001008b960b935e0ce03b8
    | 5 => 0x43db4f991a0e630eaa0800021000024b000005916816e007c62a499ff44c7658548b000090e0000003854000cc46a804780007753b53db16263f326786dc24659278af7a9ad2e490ff0003d762f41b811a122c0001588769008ad1b08952c000bcecbb8844349dc16767b19cde020c2400000006a559ba85cace000ccf92f635a21200059c13eefea2d254e418842a1348bb4dedfb7000341d1c48f5
    | 6 => 0x3dfdc8896f0a79655f4a2e3000000145a59cab3ad4400036962277c1ae2e376d799e55e40004a28424001a7f6b7fa94000bf936631815642682150000308abb39aaa6c00054f6650000001871fbe15b816a3d41f14c39bc800027c892701739c00054ec000c934f0b37cce80000e01751b26b210b52559be085c556eabf4a85fa7ab9c39bfeb4469f21b00e4b5616200000000000e413242e6136
    | 7 => 0x488018b174db000164efce0005c000002282829a521b1f0200000010417640005ce9ecdb287be000341caea0005c02ed7c020003d119304a20003fdaf1c9bc65e1a7b21800046371ab0843d6e442c08b54000000240800149c8f4322000147450cf5191f9a6972c338dc7ace62162ca04980013b649593e463ea8a5058f0400058e0004d05656b8c00002bd0507a40000c38ebc6ee2832745382100
    | 8 => 0x8100000001e704d000076eb1100010dc0000de338c2929fa441611173cba485d66b09b80010ae0762699ef5c9a4b9929082e33123db9f830a7a0602e899dcc22600005a800000000027558a1bea8cbaf44474e08d4f8ea84b0cb87e60b126b69f800000000000000b2ba5c7aee497632ffcfd334d3aa08286b69538ff80005de8320001970000aa9b3aa738cf253128680008f02e54aa9abc0f2620
    | 9 => 0xc8001b5a0ab676f679f540002c8a2c0f0c64f018b4400017f33398001bea0efe8e92bc0000000000b2e81137200c0000001c0ef7380000000b50002d814f22f35b73520f065a02fc2d44436dbb4c3c151e9b6b654bcf6090ab14000393199604b2aa912c000000770c0dd5a67017d091dc000cb20000728a38e1fa0780007bbfb60c880011c2f9000000008f86d1297055860beb219f800072eb54
    | 10 => 0x2e46354c6c0007d36eac3c24ee849f9ad02ef1b31ea2807c437d065856413a00078367d483870e15e000088653df6ca1bc00014a0b00000c2657b00016481e630661e00cce000ad12aa8bcd484ce9f5bb118fc6aed60270df7e000d0207a4000845104880dd988583aeafa5fd9322916805415348e7f41f89d960000000002e38c7500012363120f10000cfcb1a38edf00d3c001d8e64f2934000283
    | 11 => 0x28649200005dcb57fb220633040d2c8de0f130613c5d02b9f66c0000bca000156a53c13e0000000000000a2c0003fa5c6ae610000058a9c0000190001e820003ba3b5194e00072c0c5c00013200000000000004a6800397c7774cf00011405110003fc4890dc04613f2885200034e000084ec4b75e375f98e2f16c1aa81f5cdca00011b9b880cb0001fb3c4a0300003ecc82a5634cc30e45ccb45
    | 12 => 0xfda8568d2e0000004f68e14f58e9db04fe90c8d5e6ae7a2fcf684f6800136e7c800024835b8cce0002720920000000000326200037fb6e00001fe35c2d14001f1b000491732032e66600003a820765e0b9c0000003aa83d0c92ea361a4cbc001f6737a04c80006501f1aab1f20acb3876d50000e2808eb2ec000f03036318e4c64a058d80003628ea24c563d25e5f55963cf849e5790001ec0001201
    | 13 => 0xfc00010d044500000001e0cc0db56da800098b5e59ddd7b0e230003948abe51135887a4000598afd9e3d09a4370005775206d9e00028a0000a0472f470e194000d8d903808048410701244af5838149b4ddf5c565b3dec000000e00019fdc4205a3751eac1e07e10003ea5ba445d0fe824d23ef626c1ab0c0000002348888fece99307aaa042e36a3b025fc0000003ae291c4607c8025976cd0a000
    | 14 => 0x1b7971000000022500007b2409bdd8001bed90b6534000178000000000000045795eeb7e5140000000eca00060a85c06e400001301002748a25c9017ccc40a86641f19a071840001f555ae92d0002670212f0265c10c41ed3292f40001c420004a82c0bb2e3fe610e8d5f6c0000259f7569a00fd71e7b18e6000c1c824c00000024bb4d8cd699600012a051a2829731f9b27ade90d500000013f3
    | 15 => 0x7cdb7800066b2ab2efcfd258628d0001e72000696427efbc07c12229b9646e302e7800346435d65431e4b2445500003417a40002db0000e420e54a0800310000045f8e3cb16d73196b43800095d7c72d4f9ca1a40941bf0ce8a641a900029268fe54524882e03983142b582dc0d5718292805c74700028e449a3cb23d9c50bd6d15198946c97471d8c100014d49c9c10654d890ba900014e1d3e000
    | 16 => 0x3633b344fe0340001db98280ff98c1114000a8f2f030342200140003254000efde93ef742f42862cb000099481d0e10003d9400076e19943b20004f28000f1e5c3299ad64000c00157968808ce6600033bd0e44251bba6586400003b0800002e5ce73c80000005000000000620e9a41e67f40000000b68654000d0071b0001b92b4c000160211bfd423e9774000180f20052c7bc000a471054000000
    | 17 => 0x640121c000bd366fa82dba2eb200009e52dabfc00045ab9e2d4104cab058420005ecf36d079902766000004c37778ebd4dc90f670c88003ca40ae0948003108933a3826840000001450000850000000000014000000005893b059e998f59917e12c00000000000007b49ffcc2a853000470c000492715918332c00036e10b996c0004a2bb7e28a4f5ea007f79202dc3051858bb2000000259c38851e
    | 18 => 0x536000000000011984700000000006e318a67621288804000d5b0000de80007faddb38f504edc25118000001fee83ca20b46cfd31bf00002000000d73a0460106928eb0b1ca844654e8a1450e133712925f37c1eb7152838b9a6a80778003bac9b0a8f264db780000000dd02872b8235213000000061a03ac000000dfc800180c0004d5cd180005b931800002849d32432d140000003deba1000126f
    | 19 => 0x1f780005a4d456638e9814e91467433c098af2faa023055f80007da9e24d920004d25ccc27aea20d296b4000db869e00006320000002e0c257c2347594e7bc07601fc9d8448ad650f687fc0000001fd1c2400042d28ca8480c000032aa029aaa11c3c4a5e1bfe7320c095900000007ef80000003e80de34b4f3a3a50003a64dde6c121cb49dada2f7000242c5328b70a70889cb4eac1d125b0001fdd
    | 20 => 0xd7e800034800000012003ff5654030001106f703199a0d73e42e00026481ba00000000010f000000019dd706c52665bc94f1ca2e532134739a9840af0000cc2000000000095011c6a7000000033714c870db90000000000293ab874da8e3c12ae520001eb4db688470a086800000006db4fee142a467d30e0b20000213000200c0802843180b74000d670001bfc4a700000000000000003788b7253d
    | 21 => 0x159e00000025d1a0e23661d88080481960000000ce7ee2ba7dedec86005
    | _ => 0
  fld v 13 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 678 (hk ys)
def qPick1 (ys : List Nat) : Nat :=
  fld 0x1ca88 3 (action2 ys/759)
def qOri1 := quickOri 145 6 inputs qPick1 qRow qWord qBook

def J (ys : List Nat) := action2 ys % 759
def r2 (i : Nat) := bar 145 (cutB 9 (B i) C) (cutN 9 759) (fun _ => J) qOri1 [] 10 0
set_option maxRecDepth 10000 in
lemma rp0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp12 : span r2 1 12 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp13 : span r2 1 13 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp14 : span r2 1 14 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp15 : span r2 1 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp16 : span r2 1 16 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp17 : span r2 1 17 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp18 : span r2 1 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp19 : span r2 1 19 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp20 : span r2 1 20 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp21 : span r2 1 21 = true := by decide +kernel
lemma secondRoofOK : span r2 22 0 = true := by with_reducible exact (sj (sj (sj (sj rp0 rp1) (sj rp2 (sj rp3 rp4))) (sj (sj rp5 (sj rp6 rp7)) (sj rp8 (sj rp9 rp10)))) (sj (sj (sj rp11 rp12) (sj rp13 (sj rp14 rp15))) (sj (sj rp16 (sj rp17 rp18)) (sj rp19 (sj rp20 rp21)))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp0 : span t2 81 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp81 : span t2 88 81 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp169 : span t2 42 169 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp211 : span t2 44 211 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp255 : span t2 25 255 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp280 : span t2 64 280 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp344 : span t2 90 344 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp434 : span t2 41 434 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp475 : span t2 66 475 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp541 : span t2 66 541 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp607 : span t2 56 607 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp663 : span t2 32 663 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp695 : span t2 39 695 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp734 : span t2 9 734 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp743 : span t2 14 743 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp757 : span t2 2 757 = true := by decide +kernel
lemma secondTestOK : span t2 759 0 = true := by with_reducible exact (sj (sj (sj (sj lp0 lp81) (sj lp169 lp211)) (sj (sj lp255 lp280) (sj lp344 lp434))) (sj (sj (sj lp475 lp541) (sj lp607 lp663)) (sj (sj lp695 lp734) (sj lp743 lp757))))
lemma upperDead (i : Nat) (hi : i < 22) : ¬NatRun (mask 145) (goal 145) 10 (B i) :=
  symCutRoot (quick_safe (k:=145) (bound:=6) (xs:=inputs) (choose:=qPick1) (row:=qRow) (word:=qWord) (book:=qBook) qCert) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => cpWith_sound stopNo closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 145) (goal 145) 11 inputs :=
  symCutRoot (quick_safe (k:=145) (bound:=6) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 145 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row29

namespace Row30
def inputs : List ℕ := [0x21770b02045f801580572b5801589f0401b29e000fff800003c0000000fffc00000780000007,0x42a115256ca8802acaea01a802a921492f517200000000fffc00003fff000000000001fff838,0x2e0c2061e083112b3008c02305330723c0261a5fff0000f00000fffc00000007ffc381e0000c0,0x9504a848314224c413104c417747843dbb8e080000000000000000000000007fffc01fffff00,0x2ea1750e0428003080c2030825b87ffc04c0041fffffff000000000000000007fffffe0000000,0x30c18609183045bf06fc1bf079c0248927004000000000000000fffffffffff80000000000000,0x3f01f80fffc07fc007001c004e0040023800801fffffffffffff0000000000000000000000000]
def vals := sampleTable inputs 306
def scs : List ℕ := [0x1fc2a230a32689b,0x1fc480e8ae2649e,0x1a84802ca3288b1,0x158480e89a2649d,0xe82a02ca2278ae,0x1580b1fcae26ca2,0x1580b230b128ca2,0x2302a158b1288a3,0x1fc2a02c9b2749a,0xe80b0a89e26c99,0xa80b158ae2749e,0x1203a1589e26899]
def target : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)
def recipe7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x5ea6131a9a1b4cd014511c0e400ede085e128e42894d1653471653963cd44d1853025212548e69541091060454044a3a020053552e525f18530e08531ea2624861314896c8692a0c3b0ce7085e91060653549e120e381563240c8038130a42894c98120c5e156ac2127e42124696124853260c0853189a1b460412023c12422d120800530a0e8a4c801a9016de4e9ae53402130e045354d0127e4a914c30904aca18325e9c46d0120404537e3cdc084a125e861d1c10c93273310e42ba083c1242ba1342861d060c9b485f300a045310a0486aa6130602539c4a956b16536406180e06534cd012983cd40636160c14c90e06d98042130a04546b185316e8184cc21220f21a0e52126aa6123c0213683e7c0642890e0053043c120600535410326cc4b36a9e125518538e18de0ee08b5e801a0e5293045213209c1b0e18de5f16530e4a12060c544c0e129c4a120000532852780e3cd4064a123602120e42120e3c1260841b9c4212043cd44cba890e52130642124326530e0253551653040253
    | _ => 0
  let q := fld packed 24 (i % 128)
  (prefixGates (q &&& 511) <<< 24) ||| (thirdGate ((q >>> 9) &&& 255) <<< 12) ||| fourthGate (q >>> 17)
def finger7 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x3f2289de6a2d42f049de6eeb9ac4789b7c4c995d1111d30431054c2c5196e3c5d87cefed46fe90250d647d81452fa4c0063e1f7057cde6d12d76ab99c0115a594cf2a23b71636e8cdf0eed19ece459f3136e78b8e480c4bd389d48c64e3a2d53969d18cf86cae78ac1fdd17853a13562b838678bdd36e19a275376cc9e698c48
    | _ => 0
  fld packed 8 (i % 128)
def recipe8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x77286379e59502cb1e6a022381d4652926819041b4d100f0490769021f4119048cf0336c312c813e56eb076e0427485aa4a91216f9aa055ceaf8490323158d4bcdaaa4d1e492e919d492928b4945038c4a47446d21e448e224f1066e9f7d264923018ba467a217581964a62238a0082e02124108c2c79041881a48a93efa4b0697c9a30cdc642e2632387ab0154606de294a91120953c5e75042f03238a4ba0e444d23c292410901ea64e2e0b48cea70a4d21d6401971ecbef2c92136c317c206e06a325700e1b4ca4efa4a7c1b0122ca868c646364f83aac14ba5e9c2272bd124bd122d24313f030ddc118064e226b191fc208e10a388270228ca53c42b557238db3cbcba3c327c3b83150a5267882
    | _ => 0
  let q := fld packed 17 (i % 128)
  (prefixGates (q &&& 511) <<< 12) ||| thirdGate (q >>> 9)
def finger8 (i : Nat) : Nat :=
  let packed : Nat := match i / 128 with
    | 0 => 0x5c228b394b2d6b719d90742a37f325927f208fb9acd536735a7e84d1c396fc81d87f3ced4619f0250d64980cae35bd679b5db910bf669ea14c456aab526e3769e7ee6c9b7d636e93732df238d0e601a29d3ca975e4bb2b898ccf5d3d803a2d38bef153256e547973c15e29ce049035b4cd97bd39ab18f09a87f976ccec880da3
    | _ => 0
  fld packed 8 (i % 128)
def count (s : Nat) : Nat := if s = 7 ∨ s = 8 then 128 else 0

def board : Nat → Nat → List Nat
  | 7, i => if finger7 i = 0 then [] else cpBoard (mask 153) inputs 4 (recipe7 i)
  | 8, i => if finger8 i = 0 then [] else cpBoard (mask 153) inputs 3 (recipe8 i)
  | _, _ => []
def atFinger (table : Nat → Nat) (ws : List Nat) : Option Nat :=
  let h := hk ws
  let i := h % 128
  if table i == h / 128 % 254 + 1 then some i else none

def lookup : Nat → List Nat → Option Nat
  | 7, ws => atFinger finger7 ws
  | 8, ws => atFinger finger8 ws
  | _, _ => none
def x8 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x145704452e04365d1dc14f1bfe406a6bb16bb7100400730d06933d072a100f63b0bb58000705dd3100140f600e9f06d60810700654d7e0d043218d97f345e4b02002439d8107a1702dbdc83c00400ec0f8d7bdf5f85adc0056104b0a89c09d80e68b002ad2f9e73000b9772a36a172f804b2ed0021216026034f47b9dfe80f3a
    | 1 => 0xba00db865782c750240f300094415af63686ed4a12e3e70fd98cd302367064020607433000db4226fa1e6746e6e6c0c6169051c440051e51b0080255a20968dc4f2030c67a50c0a002e80080c0815080fdc700072000d4045d985d8b40096db01acc9d703c69271f60c4f010df0ec0c200840ca673b0980770343f246d051fd
    | 2 => 0x465e4ec92b48709102edb4115f000162089ff81f0628defa004a1ecbc3947601e56ae59fcb70b13606647e01a1ea672a000a0d8fbe26800b955492020c328822930081d507801f14d00048a409e2c0040d6820310d9873e9611da2b63fc103b66ad14da003a6ea0f8b8124fddec080624570e0001f5010bba904d6610008b500
    | 3 => 0x1f870d8550fd06000f200599a0d16c6940062010898df95607e84801087a292592d7b1d07bbc976dceed5577e0cf294007063000c2091c0514003c0751768f80f3c44b30800dfd1047a002d050b53e8138c78b01d1130c01e9844070819c350758c00b0681000128019a510127b4120b02650c450542400004f024b0c052001a
    | 4 => 0xf308b10320819bf57f6000334eade441b03e5c2311fb002e46ca87459fc721349324a223c01241f2702aeb18ee40a5c6335002110f4091e03a0c34d70107ae2f13ad068db4f8003cf6e0ce700323ade0d210070150000103c04c0c28a52c2080ac1680eb603c40d80e04ae64455a084a0f07fa98539e409008087e5b6f0d8af0
    | 5 => 0x22705490f05a2ad8244686b00304b7990261700c0f9708f79007e67900606b9d408d2ab056af6ddd53d17406b4a404e620a558702e4059010000d5410bd0d549bf8b679f530002b470692402071d1e010f51090eea39b99ea0fe3b200773a200d6cd72a2c1862d968674190100480d0d5f263ed99f617ab8c0504f60c04b0c69
    | 6 => 0x7b8e8df099a00100055ca8b83b9af7afb00c290efa206c447260caf33dd36e1640007008060b01347c05ffc50380e95e51d10301d457893545c50891a49aea9b05f5ae60a360004700005c01a406a04a40681260980f06e3fc040c20d0c86bb604058fde5f03005038c7a040203ffc510a01601a900ce006b42f80014731c008
    | 7 => 0xc6c816e340d034aa61908000509bb0305b850b59ba0a015422d0f00008c04c0463c0509c600144040ee0704342034961530ac16950908c525210380304afc0293abff4b290009690337dbbe4bc0de4f004b6820b4d14be0dc0a7c050cf24b91e50fc00d3040c814ad42060df3d7012d10e5433000091700932cc90302007c1
    | 8 => 0xa05fbd406b46661000ebcf007f0d680180a4d3e508008b6330cd0a60a86dea50f60420a0c210a8e705900f015a9a0505a00c7e0a5773170fb00414440781a07c421a278700a045c60400b1ee0020c11e4003602c528ced400094d89093d06e05a0177b0c010a50a44ce4f00801c0053d20097d0e82800681535fc21253004304
    | 9 => 0x7b0704c0014c071000f201bc8001d5148d0400d0a8a5002fa0d657fb00060b30c0c83280750c000d4e5024300b0c000b2c0e00d8ad0253000a5f25a7900d680e909c671c01d9010fab00e080f301745c2609d6fd8900f3f505b503124aea024317ba6b720603407301861008404a2e030033c440dd28dc030595e004b01ea007
    | 10 => 0xb73f20012000609fb400cd080ad960be5f200ce5610480e0d000aad14167868056016d000272067ed587002b4001d3500b5a7a80070027e4006a90c202f92309ae6b5061aa7650072d9b7cb1ec6e00800bf4004dbc30593ac09088209e5de1c6f07e20a3a620005f6600606e070098084cb2108aecce4b63003095f20c303eeb
    | 11 => 0x80da3e11e80a0c0be7149c0000a1cdb699ea03074b0c045000008a70f5307e25ed84200041640340b3031c103572c080b060500e662080ef30b82ca0502c7366b5900de073003c10005050008a89700771080b7b300047170390b2eaa0704000540cba8ff3707045f5003b78c3a3180700f781c075a45505303e01ea00e410de
    | 12 => 0x6894311f50009006dbdd034a408e71bd57051a23c9102b2007237061037fda26d7c405f361700010b86039a09059ea029028f40d07a17b0ab0d32d1561704b002c100d97111e70f0100003100454d1e69007810203f1090acf46d46000c02728d99bd21b01058066d0018ad04600000d60070da05057996000a00334d7007090
    | 13 => 0xe5007d080994ab0008864dbe93e195003cee710452b38001f00110d9032b20a0a6e0201e50503050f320b1160e04b84403af20370500415c051b0a1700e309637c0ee00500a000b80c269a8706d4b795004b004b7f084456eca0078605d091f988908fd14a0a110d2dfe062000bdbfba88b5d051002179221aa0a1c8fe50bdc0
    | 14 => 0x8e038206c0c52b27081b59bbc000609ac58e0a06c55baf8e00fcc1cab5ca00218e71a00b08c6981a34d35e1348c08b990de074170100a61ec4426b60c06126f478f08135000a076132644205e08013804a2610cbc81003a00722904d35c0a5914
    | _ => 0
  fld t 4 (i % 256)
def hint8 (h : Nat) := orbitLookup x8 0 1259 h
def x9 (i : Nat) :=
  let t := match i/256 with
    | 0 => 0x6e8056d35f680e030b090277f106191062c55a511948ade06278c2a385f40a07fbb4723c6aa0ac93500e64cfb3000a9560baf28e670f04d08bb400a5c6f569710000620b0704106c335630a60031040173f3f83e0044d86bb0ec002065014f730006a67861da0c60d6f0054520270410eb775f02034bb6063d61a4810d2e0d01
    | 1 => 0xf10a000024936064e6300f4ab07006be0552044683150cb1800c8a00fb70b72df30cd0f59df05cc40950cae9a00562d0472243217c870f82e0b6e090730e02e72fa0b06c0270a40e6350381c020e1b410808b235403c0a5b90028cab020902bbd9215c006f400f0080060751a9088a50fa9b30d8965c604000f0759e47028b23
    | 2 => 0x16102c416084cb8494022048109060a0c070a48b960ef06b35886fef00d0556e204ff200109000350ba805ae05c50e2503920f00a098e9400850d1e3f04830104a570c04e55b47fbdc41db009711ec00a5e0256c6e300109078de502f6c8b90e0a0d048aa681000e121dc99a84687ae09b9006b728de08b2c007fe000d0cad4d
    | 3 => 0x4908050978c71003f031064b58fd0a912c08003cbb46f0c063915e058e40b203e5160a9ad8f600b129d3cb07c5100b793f0c091f040701c90be4c952db0c060a10e86d00814e920513e2f807d0dde95bdb00691c0c175d0ea0e0f1290607d002601e06841bb252046e8409721a0ac5a6061d18581fe6671e040c00c703309024
    | 4 => 0x557a4c03001005c40320041f49306700031854b0d805d0bcba5100050d97fbc21fbe0344fc46040d71f0056d4060ef20c1004860f210884475f9f5c61d006060f570d0500ed8706f0066f409322341af73b4851bf79577630a9452008ac4a0c90610001356af161fd050a00bec0990a0080cf049056961f1dd500ad259064b07
    | 5 => 0x630e009b4a356e0b150ae0404201393200004801d1f80a00bc82fa21f765ee251e5ee4b8ab20b00c518b13fb71120600c00053ff09f207510251723085d0f900013d065a499a36050080b1a900070e06b5f0680d00503b004f6ac07c0640743de5cdc03216100c050b00876036a60080b806f8bd30f040a0e133e040116000f
    | 6 => 0xee880009620502409510f100711a460f408a6d45860f0642a90085121280fd82102b040f2cc3faca00ccc40
    | _ => 0
  fld t 4 (i % 256)
def hint9 (h : Nat) := orbitLookup x9 0 541 h
def hint (s : Nat) (ws : List Nat) := if s = 8 then hint8 (hk ws) else hint9 (hk ws)
def labels := 0x1310000249170000000000000000000000000fc003b9c0b10000000ce0000244c2004ba428c90438fe7c0000000b5002c202a30042e00787f9a8cc640000000cc0000000c10000000be003ad76ae0000000b4002b5b6a20039db2566c120743700325902a002ad7426002f572235c2783e1d002a564195402d36080027534064c80c0000
def cols (t : Nat) := fld 0x2b095cb99411c257666509734415858f58d11ab881b334423858d067588c1ab 21 t
def u12 := 0x1200000000b800000010e003ad569e0000000ff003615099003b9606a569201603004919c7f002ed741f0045d847c60ab84c1d003816a665a0e93600002c54664510dc1000
def u13 := 0x1200000000b800000010e002f9569e0000000ff003615099003b9606a56920160300492447f002ed741f0045d847c60ab84c1d0038202666d8e93600002c54664510dc1000
def rowIx (t v : Nat) : Nat :=
  if t = 12 then fld u12 9 v else
  if t = 13 then fld u13 9 v else
  mkProjection labels (cols t) 9 v
def rr0 (t : Nat) := (List.range 204).map (fun i => rowIx t (fld 0xd30b289a56091850f2c2aa268d8246143c70a689636091850f0a34c28718595246143cb0a1a6164c91850f1c28658553246143c18c2ca1c60e3491850f0aa869838b246143a182461460c91439249249249249249228a28a28a28a28a286186186186186186081451451451451451449249249249249249145145145145145141030c30c30c30c30c30a28a28a28a28a28a208204102081041 6 i))
def rr41 (t : Nat) := (List.range 176).map (fun i => rowIx t (fld 0xd30b289a54891850f2c2aa268d2246143c70a689634891850f0a3cc2879d4891850f8699d16571c286554d2246143c12b0e370aa869238b246143a091854860c91439249249249249249228a28a28a28a28a286186186186186186081c71c71c71c71c71861851451145145145145145141030c30a28a28a28a28a28a208104082081041 6 i))
def graphId (t : Nat) := fld 0x5000505 2 t
def qBook (w : Nat) : Nat :=
  let d := fld 0x3806128a0904021706030000b316006700896104bcf8020b150a06030200011c0f076c002c0040024d621b062a523f48010e0018020207400009000c2b033a051c9e520315241307001c0f2904 8 (w % 77)
  fld 0x1298b940415c11b09e8c0a500000017ac64614b190d7a60c2266ba4c1020c10caa914dac08406f0a38386d843e215100008ca2e32b4df046ce0ca3e5811c0933e18314000d8a1e1420e12649d00003540001826419d0c13a8c42e732101a84c65eea3300003a60003e5008c3c68413e2d5b8ae5165862c14ca8d1458219918a8a822be0d7a80008468b38086000153000068609e1ca022838c4c46c080015dcb933e5820db180cc2e0a30591a1962661f3875ccee0eb31108863c4545a30812c545265800152ac8b54a03101860425f2a11212a09c0028731d2a0ee2a3191439a74400000120860ce8462f71b2af8a0652b7a116b843e6072839cb450222a318860cd1ce02145943c30228f5874ab9466f1f19688b46166000810429d7a206105acf93466bd0db04e450e20359a8c6c17231f0493ca466729b344860005f7032ce8c5cc0c19304000ad43eb0915b28e4324e2a4d486f810633a2e0884455670019b2d081001834cd9408b22232040008cb84200005288c36730e5873cae60571f080002cd6c68001a882952528d180802d414603700001d45a19758118acb149864df08e8104a2b74b841c214f0f51a8aa96072ba58726be652217115ac6c37452e0c6886c68453e311a818c14e0001d1a4460c08e5508624414686283828450000254fa83455cb037408ecdc152ba081ccbd5000ab315aa08d1ceba0c95cbde123072e1285cd145175099c7ca6232b3572a007365863588a4c3 13 (((w >>> 3) + d) % 331)

def im0 (t : Nat) (i : Fin 8) : Nat :=
  projColumn 102 Fixed0.raw (cols t) i
def im41 (t : Nat) (i : Fin 8) : Nat :=
  if t=12 then (Fixed41.raw ++ [0, mask 88] ++ [0x310620c436470620cea304000000001fff0000ffff00,0x10000002040000000000000000000000000,0xfc0f83f07c049c029c0200ffffffffe0000000000000,0x100000000000000000000000000000000000000000]).getD (fld 0x62140958 4 i.val) 0 else
  if t=13 then (Fixed41.raw ++ [0, mask 88] ++ [0x310620c436470620cea304000000001fff0000ffff00,0x10000002040000000000000000000000000,0xfc0f83f07c049c029c0200ffffffffe0000000000000,0x100000000000000000000000000000000000000000]).getD (fld 0x62140ba3 4 i.val) 0 else
  projColumn 88 Fixed41.raw (cols t) i

def okTable (t : Nat) :=
  if graphId t = 0 then (decide (validCross 153 102 inputs (rr0 t) (im0 t))) else
    (decide (validCross 153 88 inputs (rr41 t) (im41 t)))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 60000000 in
theorem rowsOK : ∀ t : Fin 14, okTable t.val = true := by decide +kernel
def passed (s t : Nat) (ws : List Nat) :=
  if graphId t = 0 then crossHit 153 102 inputs (rr0 t) (im0 t) qBook (Fixed0.index s) (Fixed0.N s) (Fixed0.S s) ws else
  crossHit 153 88 inputs (rr41 t) (im41 t) qBook (Fixed41.index s) (Fixed41.N s) (Fixed41.S s) ws
def stop (s : Nat) (ws : List Nat) :=
  if s=8 ∨ s=9 then
    let a := hint s ws
    if a=0 ∨ 14<a then false else passed s (a-1) ws
  else false

theorem stopNo {s ws} (ok : stop s ws = true) : ¬NatRun (mask 153) (goal 153) s ws := by
  by_cases lev : s=8 ∨ s=9
  · by_cases outside : hint s ws=0 ∨ 14<hint s ws
    · simp [stop,lev,outside] at ok
    · have good : hint s ws - 1 < 14 := by omega
      have sel := rowsOK ⟨hint s ws-1,good⟩
      have hit : passed s (hint s ws-1) ws = true := by simpa only [stop,if_pos lev,if_neg outside] using ok
      by_cases h0 : graphId (hint s ws-1) = 0
      · simp only [okTable, passed, h0, if_true, if_false] at sel hit
        exact crossHitDead (of_decide_eq_true sel) hit (fun i hi => Fixed0.atDepth s i lev hi)
      simp only [okTable, passed, h0, if_true, if_false] at sel hit
      exact crossHitDead (of_decide_eq_true sel) hit (fun i hi => Fixed41.atDepth s i lev hi)
  · simp [stop,lev] at ok

def ck := cpWith stop 153 scs count board lookup
def pan (s i : Nat) := ck s (board s i)
set_option maxHeartbeats 50000000 in
lemma p7_0 : span (pan 7) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p7_64 : span (pan 7) 64 64 = true := by decide +kernel
lemma good7 : span (pan 7) 128 0 = true := by with_reducible exact (sj p7_0 p7_64)
set_option maxHeartbeats 50000000 in
lemma p8_0 : span (pan 8) 64 0 = true := by decide +kernel
set_option maxHeartbeats 50000000 in
lemma p8_64 : span (pan 8) 64 64 = true := by decide +kernel
lemma good8 : span (pan 8) 128 0 = true := by with_reducible exact (sj p8_0 p8_64)
theorem closed : ∀ s i, i < count s → ck s (board s i) = true := by
  intro s i hi
  by_cases h7 : s=7
  · subst s
    exact spOK good7 i (Nat.zero_le _) hi
  by_cases h8 : s=8
  · subst s
    exact spOK good8 i (Nat.zero_le _) hi
  simp [count,h7,h8] at hi
def qPerm (i : Nat) : Nat := fld 0x11835600000 21 i

def qRow (i : Nat) : List Nat :=
  vals.map (fun v => fld 0x1310000249170000000000000000000000000fc003b9c0b10000000ce0000244c2004ba428c90438fe7c0000000b5002c202a30042e00787f9a8cc640000000cc0000000c10000000be003ad76ae0000000b4002b5b6a20039db2566c120743700325902a002ad7426002f572235c2783e1d002a564195402d36080027534064c80c0000 9 (orbitLabel (qPerm i) v))

def qWord (i : Nat) (t : Fin 8) : Nat :=
  inputs.getD (if t.val=7 then 7 else fld (qPerm i) 3 t.val) 0
def qPick0 (ys : List Nat) : Nat :=
  fld 0x4 2 (fld 0x601f980029169dbd 1 (bsr 0xf850a4d4f75c4219f66a85edf192b1c8f10b3d10f02621c1ea560623e90f1b50e55cc3f5e54b2f93ddd4ff26d8f36f54d4d49ed1d2f67d14d231283fd0ccea2fd0880740ccdb0224bc1e371bbbb2cc41bb977ba8b495dd75b24eca81adbe6ec1abc6d4e4aad227489fc673cb9b9d6f459b57dc8e99b8f581999c8f3592bbc11f91e295a38fd552108fd0d8ef8c393d7f873364d67a3860b979cacf55763be7b2742847757231c5d16d7e8955698f92135b61fc905a0e96be59374dbc55a040b854f78f74543a82f94f7260614b9bce66449564e73bb12cbe2e4efcb826dacc5c1f1987801e19b624116dda8f10f4dc3b0cfcfabb07417c29061259210149de88 32 (hk ys) 7 0 64))
def qOri0 := quickOri 153 2 inputs qPick0 qRow qWord qBook

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 10000 in
theorem qCert : ∀ i : Fin 2, i.val = 0 ∨ validQuick 153 inputs (qRow i) (qWord i) := by decide +kernel
def B (i : Nat) := mv (mask 153) (fld 0xe20f51e61505f62104e40e42e21400503e30e60f42504f30f52f31f23f20f40e41106105f21f10402e62506401000e10e31e51f41404103 12 i) inputs
def I (ys : List Nat) := bsr 0xf850a4d4f192b1c8f10b3d10f02621c1ea560623e90f1b50e55cc3f5e54b2f93ddd4ff26ccdb0224bc1e371bb495dd75b24eca81adbe6ec1abc6d4e4aad227489fc673cb9b9d6f459b57dc8e99b8f581999c8f3592bbc11f91e295a38fd552108c393d7f7a3860b979cacf55742847757231c5d16d7e89555b61fc9055a040b8543a82f94f7260612e4efcb81e19b62406125921 32 (hk ys) 6 0 37
set_option maxRecDepth 10000 in
lemma roof : bar 153 (cutB 10 inputs B) (cutN 10 37) (fun _ => I) qOri0 scs 11 0 = true := by decide +kernel
def nextRecipe (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x13d944f641140c450113d88450213d844f6313d804406139d84f5213d084f5313d502e5113d401e5313d044f4313d004404139d44e74139504e65139904104114104105114144106114184f2113c8c4f20139c84e52139084f1313c404e51139044e7113cc044031390c4e731394c45071041c4e621388c4e131398c3e51110022e50139c03a40739803e40929824e600e980fe600f9804e600e8c05e600f8c04a503f9404e5012901ce40139019a40939019e40128c19e30179004e306a8045a306b80566105b842161087841ce03938c08e10218405e30
    | 1 => 0x14418550617d085f4117d005404179d05e54178d05f2117c805e52178c85e7217c405e31179c45e511541c5107179905e4115000ba602f9818e707b9818e5066941ee50679405a708b80d8e30179c05a503f80dee30179400e520dc8435000fdd030000fc9035050fc843f450fd8c3f640b9843f600798c3f410fd0c3f400d0103e740f99031060d41831020d4083f510fd4c3f130fc403e610f9043e710fcc034030f90c3e730f98c35070c41c3e530f84c34008b9c04103104044b21104084721114004f7613dd44f7213dc44f7313dd04f701101c4000
    | 2 => 0x67d8d2e13439459f505f94c2e5307948ce43479059f402b9089e536795191055b948de41654193e2357884be4167cc07e423f94d9e43679cd9f10679058e51679448e523b90594005a901fe305b9008a4023900ee305980dfe025b80e36038f80d56035780c510116c84510215c840e2115d00573015d40576015dc0550017dd85f7517dd05f7217dc45f7317dc05407140005f6517d8c5501154085f64154105f6217d845f60150185e7617d505f3417d445f530b84c5f50078c85f3217cc45f301500c5e75179cc5e53179945e631440c5503144145505
    | 3 => 0x2841c8e16218588e14218508e643b94c8e763b9948e743b98ce10321410e50320418e10521418e5052041c850739418d10623d4cef4223d48ef4123d40ef4021014e40423854861523994ee5423914ee3423cc8b10723cc0ef201d41c71072398cee522390cee322384c861323c80ef1021008e40123908ee3123848861223988ee51210008101814020100229c08e703b9808a6023980ee50229408e503b9013a604f9808a30238c0ee2059809fe015b8088a2023880ee104d80d3e032e900be4064409562165d41976065dc1950067dd06e305394d9502
    | 4 => 0x4f94d5e517bd41e4057b9d5ee257b914be517bcc07e523f88dce537b9cdbe507b9058e61790018a6063981ee702580c9e03939c18e407580dde0393941ee4050401450020408e1012040ce10201418010621c40871721c58871521c4c871221c508f1023c5c8f1623c548f1323c488f1421400650623dd8ef6523dd0ef6321408e5012140ce50223dd4ef6421414e50423dccef6223dc8ef6123dc0ef602101ce406184188e172185c8f653bd508f453bcd08f603bd408f403bcc08f623bd448f643bd4c25070841c15070441c8f433041c8f423bcc48404
    | 5 => 0x63c918f201b9818f76539cd850061405850363dd5850563dcd8f7163dc184076389d8f654b9cd0e715f9cc2e7363d801e72339cd1e7163d00ae72638989e23639918e76639d181065b9c8de616141d3e73579c58f50610158e2563914be7163cc07e723f9cd8e436388d8f10639058400784050a217840c0e4141885e7707bdd9ef727bdd5ef737bdc5ef747bdc1e40705809ef625398de50079405e5037bd95ae527bd8def617bd81e4067b9d9ef254b94d0e215f88c2e2307808ce5347945ef402b949ee722798dde237b989ee64598496e1237945e506
    | 6 => 0x6d0021602378061e024980d2e0303805a6026b808c6033380e0e038180d76035f80d46035380d1221904051a219040e4730038c647405d84d162191d42476091dc24f7693dd64f7493dce4f718384e4f709101c6e2093d954e139140245019140e4f646b90a3e4393d864f609101a4e7693d512e23439057e130b90e4f5007908ce2347884ae02939d49e137784e4e6593989fe315b908de31879093e43579064f40910124e742f8c64f301f8c8fe437188dce238b90dbe309100026030b80d8b2160405810303985876061c858f2763c998f2563c8d8f21
    | 7 => 0x8bdd5ae738bdc62f708bdce24078b89e2f654b9d10e735f9d02e718bd801e73339c51e738bd00ae738b8989e24779d22e768b9d1fe625b9ccde62879cd3e718bd415e732f9ca2f031f9c0fe71739c624003e9c0fe708b980960427811ce708b900fa4077810fe40739408b200ecc04b306c40804016fdd9bf756fdd1bf726fdc1bf736d01c5b106fd9544036d401b5026fd91a4026fd89bf606d019be766fd5124034100574030900c14023100d140129009be752500dbe536f995be636c415640235005b5064d00d54016d010b4011d008f4036f8c9be72
    | 8 => 0x3f890fa623f988f1023d408de523d418ff513fd40ff532f948ff031f940f4004580d1e03838120604518114e04498112e0430885c101328840e3271d01262431885c75071d81c77073dd9cf7573dd1cf7173dcdcf7273dc1c4071b885cf6553851c50371401c50173d91ae4373d85cf6073d8dc406739d9cf544b8910e435f8502e4173d401e43338851e232b80dce7527851ce5273995c1055b90cde32714193e4173d015e432f8c9cf031f8c0fe41710022b21884040e6289c862f278bc9a2f258bc862f23838922f201b9862f76539d22503894022501
    | 9 => 0x2d8c0be302e9c0be7022cc19b30010087f761fdd47f741fdc07f721fdcc7407098047f651fd8c75021d4007f641d4107f601fd8874061fd507f341fd487f530900414031fcc07f321d00c7e751f9cc7e531c41475051c41875061fd007f421fc08740003809a6036b80e16033780a1e035d8117e044180d0e033c4042a2103908f7503dd00fb723dc9426213dd80f7703fdd8ff723fdd4ff713fdc0ff733fdd0f4070580cff623fd90f5033d400f5013fd94f5053fd84ff603fd8cf4063fc94ff453fc8cff240b8841e0333944ff403fd0cae533f9c89e64
    | 10 => 0x4bc4d0f5157d502f5307d48cf4347d04af4227d4d5e5454415550557c0cdf41554193f23550024b4062d41eb508c4023500569015e40569415e5022d405b4085814de048781546055381506054381516044781176055f81426050b814c60433811de0503c84bf762fdd4bf742fdc0bf722fdc4bf732d01c6f102fd94bf632d404b5022fd90b5002fd80b5042fd88bf612fd50bf342fd40bf512fd4c2f1307cc8bf302fcc8bf312bcc8be7527d0cbe532c414b5052fd00b1062d418bf422fd04b4003dc0e4b3062cc1eb302e940be5071c0e27032c8c0ba30
    | 11 => 0x37d45050637d4d750608418250604418150630418c50637cc5150628418a506379961e762441c95073794dd50634415f50535415650637c121f0537c061f0237c0a1f03350021400869c0de60879c21a60379421e6086900de30879013f764fdd53f704fdc93f714fdcd3f744d01c6f314fd953f644fd8135034d40535024fd853f634d4013f504fd493f404bc510f534fd502f5107d4ccf4147d0caf434f9d49f544f95131054d4153f0337d0935064d000fb5072d022b504e9c13e704e9413e504e9013e4057dd06f3053d4d550257d8d550057d415f40
    | 12 => 0x45400c1003140167107fcc1ff6318411410668415ff5248415010259c5021025bc416f405bdd011005141965055bd8d2505414096f1409408150030414c50544415150528414a505244189506598516e147fc096f037fc056f025840564000840025005c40175004040105004840125002ed02170585c0a170385c421b7137d94df6437d80df6237d84df6335018610585c59410235404d50285c54d50485c4e171287c421f7187dda1f7587dc21f7387dca05078501c650587c5945028540a15036941a1f1337d521f6537d421f6037cd1250637cc21f40
    | 13 => 0x429c10e708381a0606469c11e70469411e50498152e05329c0ce7025d80972127c846e6227dc4950527dd09f1527d8c9f610b9d09f60079d09f1427c109f1327c0c9f10250017a215d885df7677dc9df7577dd1df7377dc5df707501c160477d894e6177d81d5036b951df6477c952e5277c150e245f8842e2407810ce5277c111e5277c0cae50779c89e61750009a6027981de7069815ae0569811ae048c81a3a068d81a3e068d8123e045e9817e600a9802e60429810e604a9812e60469811e6032980ce6077981670359c09d100754009100254011100
    | 14 => 0x5001460653818bb3033dd8cf7533dc0cf7133dcccf721bc84cf6033d94cf623140cc50433d84cf5433c10cf2433d4ccf5033d482f4107d0ccf0331000fb4025c11d70432940ce5047dd91f7547dd11f7347dc11f7147dc86f2047d951f6047d891501454111f6347d511f0447c911f5043d051f520bd0c1f4247c0ccf23450019b4025c0dd70316cc18b407ad022b400ed004b402bdd8af752bdd0af732bdc8af702901c64022bd94af6029408a5042bd8caf542bc10af522bd40240405010af032bc08a400098102e04418110e045e9c17e700a9c02e70
    | 15 => 0x45c112f604bdc12f744bdcd2f721bc8d2f624940d25014bd912f054bc112f0349001d70586d012a704b9c08b6022d01070409c0d0f7043dcd0f7143dd0170243d810f6441405050543d8d0f0543c950f4543c110f03410019b5009c117f705fdc97f745fdcd7f7105c117f6053d8575035d4157f645fc157f254bd497f0343c917f045d0002f700bdc82f710bdcc2f7405c0c2f600bd882f640940c25050bd842f050bc942f450bc0c2f230bc102f2409001cb5092d405b5026d822b6062d803b6012d401f74040001f64054141f6307d141f0207c101f03
    | 16 => 0x78dc08b101040031001440191006adc17b705ad00bb7086dc0cb703edc11b7083c1a0f0483c0e04001bd89cb7092dc05b7076dc04b707adc0010032d8147060ad811b6053c154f7053dd14f711bd494f0453c194f0351001db6069c15a704529c14e7078401810090402210070400f1002c400bb6069c19a70269c0daf016bdc1af736bdd0050051415af056bc11a5026bc19af026bc0da4006a9c1ae7083dd06f518fc123f0653c923f036bd8e34003ed81cb608adc1510092d818b707ad81310022dc05b6012d81a6066b819270509c15070586d80c704
    | 17 => 0x2ecc8bb4290cc1ab0103d940f6003d91ab7103d880f6103d8c0406000000f5403d4c0f0403c0c050101409ab6103c140f0103c080400039800f5203d440405038140e656ad45210103d040f4303d08040403cc80f310100c0e640398c0e43038100e03039500e530041005040041405054c4093b5249c50f35070d01510249c4d372390d0053404ad894b614ad48cb523cd01172431c8c533041c9593505edc9772541c90272309c91c35090d40535024d8183608dc9947243cd81c36051c8e372390d81936014d80f37064dc2072481c8dc37090dc05370
    | 18 => 0x1012ed44bb313cc0dc3033ec0dcb0300408d102
    | _ => 0
  fld v 18 (i % 96)
def C (i : Nat) :=
  let d := nextRecipe i
  mv (mask 153) (d % 4096) (B (d/4096))
def nextCodes (i : Nat) : Nat :=
  let v : Nat := match i/96 with
    | 0 => 0x8c600097300000002c1cb5df6d4c6c3a37dff5a750c793f10340000000c4a6a0003a43a72cfe96b180008fe61901d9fba0f072c8bf12188064568ca43722982143cfc6a000e5b8d23c41ffa4516bd83e635dfb9e00026b41da767d3ca62a900035f000000ddf52440653ed007c0b63ebf1286804cb64943884c000a19595000464655ba3dc12edb9b00012100099e
    | 1 => 0x69cec142500024d5a51e1000e38d2d21dbeb342d750ed427000000b6e000cbc6b8e40d1aab75050003ebd5a60ed26000a4fde899a1c11c100007802a791d46a29e7578f89fc63000000f8cbc1d6bb7e0000004329a5f0cce1a6295e810fcd7ee000000206f6a46330e0007cd000e13303000230000d90000ce23346fa8461fde42000f643d50003d1000171d07256120
    | 2 => 0xd6638c50966215d692742a2000e6a889fe3fe07d62a3238bb77a500007e0960009d23ff8ce000443af600067787e9d5000000ae0000000126c9b8b7ba10008df128fc01e42ffc0dd6a0006345c631601a3a50004b20000a25315a1e6624bfac037000000000bdeb89e892b500005c0bfa53d24aacaaa0004fdd95413000b0a00066549cd7e2c10003fb323b5a000000
    | 3 => 0x9fe7cc000f383fe53b9593f3014ae39f56252a18459d6ea9cf00000006f36590007b099a5611b22f41ce9590008c1000f36a16000f95ed936ef4657300082a0e700079e98a97d15100046524d416bf3eb281c5f27ffb461988fe3b0d1ada72b282a5c985b48c82f8aa25186e99a0006200000005e3d6d000f26d6600047a0009089dd439b7d1eefdc0000006db000000
    | 4 => 0xb2de6f5bb81a4660000008406a0eb62cc5a5e3ab15fec5f325ba4238d778c820007020fe174000a3a2e005155f3978050000008d0000014ad3e864a97e81c4a21000841cf900055283d34c6ad355d9e000eec9948d1604f8219f5eb78a0005dbc1255e3f96aa0000b110b53332b0ccd7262c00000000043fea5bf0217de9f920004c318f00066700018226758271437b
    | 5 => 0x3ef000e922b84be000d6e3cabdf6bc7c75f6a7cefd000b3f000000e5b0008af2c211aae45c5973686121fa0b7f3a3be9952d881b000023b79f0000009904a05cab1946826b78773e4f7ab30004863f2000df80005f19708bb93a10f163000c150005f51cf000000000a2a083fa9f6d97f0008c2f86442120000b1df0d91227dd9202f18100000058ca2b5de2ef1afc75
    | 6 => 0xf56000000814000f534fd3659f9bd49fd41e1cd000809e75000000164000000000c5d37cfcd66c00028160d04375b42fe69000558aeef1dfd90006809d60c0bec91ff9d76200062300041bd45000c438a4f1b52f29f48197552dc925bc000000b3f00038ad4704da31602e7b000000000a1900013452ad666f870b98a73a703df000041f145b64b3190f1a9c9b
    | 7 => 0x830f400008b10009b83367ca269a7e0009a92cdb250004f4c87f63b0986500037705780d0b5c4d94b67b650a94976e5f78954e6cd9d1a370f9acea88d794380b6c8568d217000bef9110a34f4000000364e412db40bbc16dca7a3706f6c31b65f209465a0fa100000071a39d00020de63677b15611281000c2965201c0002a651e281d85b2a5e0d6c6e478f91814d199
    | 8 => 0xab700021a0b0fd47a9b31a50d852607e44b5fefc696e2ed200060db45f255412b83040263aa0ce000767954eea00003602fc8e5479a652300054a7c51dc25cd29183d5e00b4ace77000c59c3d00000061ca8d1220009dcf4bc509e829c5b718d0004960a3806e340003410000000008e51a72dbf8376987713468d8c6619000c3700042534d09c19be865ee3fb1f83b8
    | 9 => 0xea5d6232c86bc45d46f15c8e338c22afd1afd1a00000012ca82be439a60becc5840e9d577dd00054433446501f762dc1898d42bea19460e8743a6000000d4fbb760b5c1cee39500082fe652230004e70004fc46efbee080b9e08000e70c5b0000009fab45bbc0002e526a000000000c5c71797d000000b6753c00020b5896501f8c4106b0009b30e51f5dffeebcfe868
    | 10 => 0x4de000a10466000d40000dc2bc7d7b00000020540400045b57a17e4090009d0000000087c5845b000000f3ac63112942bd50009c4000000000000000382c201acb860000d90adc1f0ac9a726c000000f9e9d6599d4e00023f7ce8d0000e6200089000000e8c1c15b54df2032e1905882059afa60003e651598ccef7c80009a31db9a3926e8d2872f91b0000fae00072b
    | 11 => 0x9ad7ff67b383cd22a6bc10c20ae300006fdb39a1af96f9236cdc22e826737000023505421c85941d800795a8160573f64890d00053158e7739c600041f0000003d66028b7cb67083e050da52be8c8f000f5133514bdac9c8dc1ede00020747c0000c6caceaf44b475d4557c770624c0fe758f2a86e2071c5bb7b94ff5ea6f1000a86c0b1c10005c40001a8c2cbfa000
    | 12 => 0xaf276f000aa60000006ad2664fe07f0ae06c8175fd7a5e7c1cf5ef000000fd636300e616000076a858c0182ce2e9819e39ab9036fc4fc949367c1a3dd49285d412b2670000823dea0000006b20007ee7d2785000ff0db8d6b596f4cf4ea09ccd2f932b00030e00073767828f06f34b3ab24b1d5ad7e920005ed6568df323fd6dc3793ffc00000035ef86f1c00094f027
    | 13 => 0xc2812eb7a1c8000080f480000000005d307950a0300004ce000949ee7000000c445cf7cf000ef427f11f00080f310164063ef1b66000bc60009ee03de52b28d1f000a83a31000857ec9000503acf06aeda9e018916d2c060e9a10005077ea4e7149b6c404260aeab1fa5a06c3e0caa222c536ddc91000ba648d58408148563bab99a13941f8e6e35470aa6c243
    | 14 => 0x8dce1100076d6404027fe00054390a735dd7432762acbc936a2f6896463a00039f9bf000000000a6d000451000000853367000bb710d51251e0a84b14a760e000000000115de084b366af092f2f4f2140dc620e100016830ee6a04b000961ae8645238539a8569702f4905338b68253f53ebb16000b69cb9c0b2328f662300000000091c0a66a964a4e3ccb2383475b5
    | 15 => 0x719fd2000d29140f6e0000002b40ed53d406981a0085d2b1731837c713f8c02a0200003d110d803e344a00044f46095e351000624051730100fc38fe73c000bd955d3b3bf370c39c57682be520008c55f4000129000f5746b82c00008d6fca87000ed0d8ddf191a52e0008f0a02b90fde00066d0009850000008a600001e061124705abcf392d2b4f000000000b848c4
    | 16 => 0x903d996f32d33b697463302000000418153000000000e5425d3cfbf700000000003d63e000acf4c1a5d3780005f9bf4000000ee1e1cdbe461000e07cbc81f316e0ab639cbfb441993369b000000cc0c6378d1080006b6000d5954e6294bc790420000bf714cfb300061163f4e05822f779e005a2cb570001ed5f662c000ca449d7cf67bbef000184955e19000af16c5
    | 17 => 0xfc6000e41259000ac1b2667300091620f2e2000615c2ea5000061500095cfcadea0003e126d6a6000556c41eb106e829aab00020cc8e77a0e917c2c5a670005eb02d5a0a77a326c23e6e3899e9b5be2b816522c7af1b588b6e7e4e7a4d3beeeacdf000241bec673ad3a7c6991480d994361ef4acb40000000002c8805ca600003800000000000007ac8300062e000
    | 18 => 0x783c2000000ec20bb68a1ef15140e9da39f000ca353e00009131a42066f202000000000644bc21dde3d6e79160005ce72be3735186ffaa8a5f0242d1c50055a7aa297b346d2f000c223e28f081deb789fdc22f40008870000002c2d5cc2348c94165900086e000778000000bc3817b4ebf440beea4f71d8000b8ac12567840b892e43487a1d74aa4b730631bc413356
    | 19 => 0xaf5257000000000bea8fcce1ac4a324cbd89000df30004834b5000000018000a51000b47000c930004daa4ba440000eb8b5c6d07141963000000000040996e000a9edf3f86ec1000bc4000efa40d0001529b2000d3f0007e61a1c39e8e610379f8f5eba71d6ee2c7fd0004b3c235e0e7b65713249e00016b8da13832aa9bd0b17809c95553297af8129d9a41cadc1818
    | 20 => 0x2745dc6fcfc55cca7b1e33e8fe700003e559d36298b773dcea06f9473120297ba40005285fb0b04286c7801d427f03510000000008de70ab5b9f30a4d9c0003a430ac2174dabb2687e8d02e90000b380000004e20007da9bcf285663548ea1b165563f000ce470bab2cc2107adaaf43d92adc745242eb021000e90da3189e1f10bec521131421e31bf18db56312ba492
    | 21 => 0x462df4000a324c907d0004170005ff03a03bdd8000f4c187fd400074293c000d48af4cd75e2cbf0009c4f60cda56c7d8c82e290008451df73c48f6ee813bd2c38888087045cca16b00086a3a327a0000007734f68b8000000e3151e45473b0dcfec000a9038bbb99bb559b2f0000004560008bba18db7000607000904f1731a547bbc17eca82e4f75dae773bda01fabf
    | 22 => 0xa6f1c884a12333c827af24f77cfb1374700043d000748000646c04000f6d04b2b9fba000f5dc4527e9a326c000fcaf8470fd4b85a00094e06c00045c6986a4eef0004414cf0000000780009da0002588ee3e17aa9f497d5fa000000a6679d48bb91a569875fe0006c0d4a799a4b5b56f5c57fdc000000000e7f929000000000e7fca90001580000000007713635295b0
    | 23 => 0x56da170e1000000114b730da791e075645409362350008eb067ba7000f7a3a22710004991faeafc5d78d0004821a300097b000782565000dc70001470001f14d599c3c8a6f4e71e200076c8a5d4c7b00006ef2060009d1000c5bff0593fbc340cf4bd1287da49ea07e096b95ede0001dcb98e7a629000a673bf000b334a45a80008cabd75daee83bb21635db23253e45
    | 24 => 0x8015546870f68042d60002bda7a71fb662f9b0a32f0bfd232c1f5e0000405490002bc629d614c707376558036db295b8277c6f17c83f25f4e36ae0003460a11ae0d500075d0001d8e88cab5e1548000ce65bc00028f000aa771deff147b7f96f7060a191ab3f739993fc6063535498000ca81fe24bbc4e07ad4db70005ef0027bc5ff0000000907be000f3a0002be
    | 25 => 0x91fe82e5d9f6a31423191000a4a530681ffc00074d1c70005f5df26290004ebc505086bae08ddb000f508a900013fc4a1ac0006e321ea52000db3119bae628000ed61157e9fff4bc0004b6af85a7d502f236ccd6c18000701aef4294c13875ba94a9836a04fffb25ad509460bae471351000a553b5ee653e000000000a67f0860a00086bee75794035fa46164e4ffda9
    | 26 => 0x72efa6c62fb92fe1f0000c04000eeff73a82399000fa1fc171881d27c4ba4c400049e94200095a5e8ed10008cf8dd00064f9441863c1975caa0007857c95db00038afa5b46d2faf124000000037f7bda5eeb441a09e000483ce1000000000d4600007900000082f99ad5c0007ec3db84f2e14b1d8000098397f8cb567e21f74000de7c3e23ca3b0000007306b0000
    | 27 => 0xc07469c1f82a63ac63634232d89404dd543b28c672000000c798aaf751c9d45df23ee6203d87927a5876c451d80000009b1681d1db041f84b06b30ca645a1661e8cc5582cad0bad97f800000036c2e201b2c7252000fd400034b00084d0001c6ec8000a947369beeb42620000008c57190820009afea30000568607ec872cff000416edb9e23d891fd86f58000d6e42f
    | 28 => 0x7e4ca0c455d521259e424032610a67000a058fb00089a92b000676e474643b581600055a0008d5f3a05493b0002a659579f36aedff54000eda92876d00067c000000e863b252e3efe60000cda7b600000000000084f5216730005e2000f5b2a28deb1c8cacaf4c1aadd10422000d4659fbc381d4bcd5c5fe1c946a06d7a4abaeaf41dcecea6b886a8000535a3949f05f
    | 29 => 0x558000fa259f98c291750d563d6438a2600074ba477f5d9a8eea529232abc9a9ff8ec000ebc00086c0000005cb0f970d64615a5709cbae2b40ccc35965662fa9ad85bdb000256000000dab07f0bff4e00083d1e0000f6d00046281a3c6924ac9fc59016b8fc122200064300040092abb5b970000000008e30000000007b0ef025e0000000003f5d794a1000be4037000
    | 30 => 0x10686c961b5b4ddc58350323ba6071304000ec0657e950006f5048000762dd59b5cdd000c31822998756299768d297c15ae7ba1ec9240003c9c6aae8ad5000dbf5228081124ee000f60889000632000c02432000868be3c5f00000093a4f8409000afaa2d000379e309c06ee7051a3c72268df4747c7700012584f000862622f28000000657cd3f3207b794bb60c85f3
    | 31 => 0xce313806e8a1000000a135ec000484000f0cb43000b8b08d937a75adc0000000000000000007ad0003e33748f72fd1d800027cd2656eb56a010003e6a4400036b8385be1a61b6f84a96fb244500000000000001a0bc39e0001ed000698d63a6b000ca909492a179cf33d761ed95d6c000bd56b32ae40d00038c12c70e4f07360ad0000004b300084c5bdecdfa3480402
    | 32 => 0x8d022649d3de000465000eb38a4da184a0e50004ef510000aa4baa91f6e4641
    | _ => 0
  fld v 12 (i % 96)
def action2 (ys : List Nat) := orbitLookup nextCodes 0 1031 (hk ys)
def qPick1 (ys : List Nat) : Nat :=
  fld 0x4 2 (action2 ys/1737)
def qOri1 := quickOri 153 2 inputs qPick1 qRow qWord qBook

def J (ys : List Nat) := action2 ys % 1737
def r2 (i : Nat) := bar 153 (cutB 9 (B i) C) (cutN 9 1737) (fun _ => J) qOri1 [] 10 0
set_option maxRecDepth 10000 in
lemma rp0 : span r2 1 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp1 : span r2 1 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp2 : span r2 1 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp3 : span r2 1 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp4 : span r2 1 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp5 : span r2 1 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp6 : span r2 1 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp7 : span r2 1 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp8 : span r2 1 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp9 : span r2 1 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp10 : span r2 1 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp11 : span r2 1 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp12 : span r2 1 12 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp13 : span r2 1 13 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp14 : span r2 1 14 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp15 : span r2 1 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp16 : span r2 1 16 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp17 : span r2 1 17 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp18 : span r2 1 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp19 : span r2 1 19 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp20 : span r2 1 20 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp21 : span r2 1 21 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp22 : span r2 1 22 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp23 : span r2 1 23 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp24 : span r2 1 24 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp25 : span r2 1 25 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp26 : span r2 1 26 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp27 : span r2 1 27 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp28 : span r2 1 28 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp29 : span r2 1 29 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp30 : span r2 1 30 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp31 : span r2 1 31 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp32 : span r2 1 32 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp33 : span r2 1 33 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp34 : span r2 1 34 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp35 : span r2 1 35 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma rp36 : span r2 1 36 = true := by decide +kernel
lemma secondRoofOK : span r2 37 0 = true := by with_reducible exact (sj (sj (sj (sj (sj rp0 rp1) (sj rp2 rp3)) (sj (sj rp4 rp5) (sj rp6 (sj rp7 rp8)))) (sj (sj (sj rp9 rp10) (sj rp11 rp12)) (sj (sj rp13 rp14) (sj rp15 (sj rp16 rp17))))) (sj (sj (sj (sj rp18 rp19) (sj rp20 rp21)) (sj (sj rp22 rp23) (sj rp24 (sj rp25 rp26)))) (sj (sj (sj rp27 rp28) (sj rp29 (sj rp30 rp31))) (sj (sj rp32 rp33) (sj rp34 (sj rp35 rp36))))))
def t2 (i : Nat) := ck 9 (C i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp0 : span t2 53 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp53 : span t2 100 53 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp153 : span t2 42 153 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp195 : span t2 45 195 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp240 : span t2 40 240 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp280 : span t2 33 280 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp313 : span t2 43 313 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp356 : span t2 37 356 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp393 : span t2 51 393 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp444 : span t2 73 444 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp517 : span t2 81 517 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp598 : span t2 45 598 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp643 : span t2 11 643 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp654 : span t2 48 654 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp702 : span t2 89 702 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp791 : span t2 42 791 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp833 : span t2 8 833 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp841 : span t2 21 841 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp862 : span t2 39 862 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp901 : span t2 53 901 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp954 : span t2 14 954 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp968 : span t2 68 968 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1036 : span t2 79 1036 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1115 : span t2 54 1115 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1169 : span t2 42 1169 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1211 : span t2 49 1211 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1260 : span t2 22 1260 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1282 : span t2 100 1282 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1382 : span t2 96 1382 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1478 : span t2 71 1478 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1549 : span t2 40 1549 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1589 : span t2 41 1589 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1630 : span t2 10 1630 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1640 : span t2 11 1640 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1651 : span t2 14 1651 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1665 : span t2 16 1665 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1681 : span t2 27 1681 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1708 : span t2 22 1708 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma lp1730 : span t2 7 1730 = true := by decide +kernel
lemma secondTestOK : span t2 1737 0 = true := by with_reducible exact (sj (sj (sj (sj (sj lp0 lp53) (sj lp153 lp195)) (sj (sj lp240 lp280) (sj lp313 (sj lp356 lp393)))) (sj (sj (sj lp444 lp517) (sj lp598 (sj lp643 lp654))) (sj (sj lp702 lp791) (sj lp833 (sj lp841 lp862))))) (sj (sj (sj (sj lp901 lp954) (sj lp968 (sj lp1036 lp1115))) (sj (sj lp1169 lp1211) (sj lp1260 (sj lp1282 lp1382)))) (sj (sj (sj lp1478 lp1549) (sj lp1589 (sj lp1630 lp1640))) (sj (sj lp1651 lp1665) (sj lp1681 (sj lp1708 lp1730))))))
lemma upperDead (i : Nat) (hi : i < 37) : ¬NatRun (mask 153) (goal 153) 10 (B i) :=
  symCutRoot (quick_safe (k:=153) (bound:=2) (xs:=inputs) (choose:=qPick1) (row:=qRow) (word:=qWord) (book:=qBook) qCert) (spOK secondRoofOK i (Nat.zero_le _) hi)
    (fun j hj => cpWith_sound stopNo closed (spOK secondTestOK j (Nat.zero_le _) hj))
theorem finChk : ¬NatRun (mask 153) (goal 153) 11 inputs :=
  symCutRoot (quick_safe (k:=153) (bound:=2) (xs:=inputs) (choose:=qPick0) (row:=qRow) (word:=qWord) (book:=qBook) qCert) roof upperDead

set_option maxRecDepth 10000 in
theorem shard : ∀ t, HasCircuitSize 7 target t → 12 ≤ t := by
  refine proveAtCap 7 153 11 target vals inputs
    ⟨fun _ => false, fun _ => true, by decide⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact finChk

end Row30

end PEqualNP.Outside.L_meta_982_aux

theorem PEqualNP.Outside.L_meta_982 : (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) t → 12 ≤ t) := by
  exact ⟨
    PEqualNP.Outside.L_meta_982_aux.Row0.shard,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard01,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard02,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard03,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard04,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard05,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard06,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard07,
    PEqualNP.Outside.L_meta_982_aux.Row8.shard,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard09,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard10,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard11,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard12,
    PEqualNP.Outside.L_meta_982_aux.Row13.shard,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard14,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard15,
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard16,
    (PEqualNP.Outside.L_meta_982_aux.Reduction.row17_of_row0 PEqualNP.Outside.L_meta_982_aux.Row0.shard),
    PEqualNP.Outside.L_meta_982_aux.Row18.shard,
    PEqualNP.Outside.L_meta_982_aux.Row19.shard,
    PEqualNP.Outside.L_meta_982_aux.Row20.shard,
    (PEqualNP.Outside.L_meta_982_aux.Reduction.row21_of_row0 PEqualNP.Outside.L_meta_982_aux.Row0.shard),
    PEqualNP.Outside.L_meta_982_aux.Reduction.shard22,
    PEqualNP.Outside.L_meta_982_aux.Row23.shard,
    PEqualNP.Outside.L_meta_982_aux.Row24.shard,
    PEqualNP.Outside.L_meta_982_aux.Row25.shard,
    PEqualNP.Outside.L_meta_982_aux.Row26.shard,
    PEqualNP.Outside.L_meta_982_aux.Row27.shard,
    PEqualNP.Outside.L_meta_982_aux.Row28.shard,
    PEqualNP.Outside.L_meta_982_aux.Row29.shard,
    PEqualNP.Outside.L_meta_982_aux.Row30.shard⟩
