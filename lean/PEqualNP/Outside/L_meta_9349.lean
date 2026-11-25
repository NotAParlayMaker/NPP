import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9349

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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
      simp [wiresFrom, List.foldl_append, hw']
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
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

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [(Sum.inl b : Stat)]

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
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

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

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
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
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
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
      ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
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

def mapWire {n : ℕ} (e : Fin n → Fin n) (w : ℕ) : ℕ :=
  if h : w < n then (e ⟨w, h⟩ : ℕ) else w

def mapGate {n : ℕ} (e : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mapWire e)⟩

theorem wiresFrom_reindex {n : ℕ} (e : Fin n → Fin n) (y : Fin n → Bool) (gs : List Gate) :
    ∀ (t : List Bool),
      ∃ r : List Bool,
        wiresFrom gs (List.ofFn (fun i => y (e i)) ++ t) = List.ofFn (fun i => y (e i)) ++ t ++ r ∧
        wiresFrom (gs.map (mapGate e)) (List.ofFn y ++ t) = List.ofFn y ++ t ++ r := by
  induction gs with
  | nil => intro t; exact ⟨[], by simp [wiresFrom], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro t
    have hval : (mapGate e g).op.eval ((mapGate e g).inputs.map fun i => (List.ofFn y ++ t).getD i false)
        = g.op.eval (g.inputs.map fun i => (List.ofFn (fun k => y (e k)) ++ t).getD i false) := by
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro w _
      simp only [Function.comp_apply, mapWire]
      by_cases hw : w < n
      · rw [dif_pos hw]
        have h1 : (e ⟨w, hw⟩ : ℕ) < (List.ofFn y).length := by simp
        have h2 : w < (List.ofFn (fun k => y (e k))).length := by simp [hw]
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
        simp [List.getD_eq_getElem?_getD, hw]
      · rw [dif_neg hw]
        have h1 : (List.ofFn y).length ≤ w := by simp; omega
        have h2 : (List.ofFn (fun k => y (e k))).length ≤ w := by simp; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h1, List.getElem?_append_right h2]
    obtain ⟨r, hr1, hr2⟩ := ih (t ++ [g.op.eval (g.inputs.map fun i => (List.ofFn (fun k => y (e k)) ++ t).getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => (List.ofFn (fun k => y (e k)) ++ t).getD i false) :: r, ?_, ?_⟩
    · have s1 : wiresFrom (g :: gs) (List.ofFn (fun i => y (e i)) ++ t) =
          wiresFrom gs ((List.ofFn (fun i => y (e i)) ++ t) ++
            [g.op.eval (g.inputs.map fun i => (List.ofFn (fun k => y (e k)) ++ t).getD i false)]) := rfl
      rw [s1, List.append_assoc]
      simpa [List.append_assoc] using hr1
    · have s2 : wiresFrom ((g :: gs).map (mapGate e)) (List.ofFn y ++ t) =
          wiresFrom (gs.map (mapGate e)) ((List.ofFn y ++ t) ++
            [(mapGate e g).op.eval ((mapGate e g).inputs.map fun i => (List.ofFn y ++ t).getD i false)]) := rfl
      rw [s2, hval, List.append_assoc]
      simpa [List.append_assoc] using hr2

theorem hasCircuitSize_reindex {n s : ℕ} (e : Fin n → Fin n) (f : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n f s) : HasCircuitSize n (fun y => f (fun i => y (e i))) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  refine ⟨⟨C.gates.map (mapGate e), mapWire e C.output⟩, ?_, by simpa [Circuit.size] using hsz, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [mapGate] using (ok g0 hg0).2⟩
  · intro y
    dsimp only
    obtain ⟨r, hr1, hr2⟩ := wiresFrom_reindex e y C.gates []
    simp only [List.append_nil] at hr1 hr2
    change (wiresFrom (C.gates.map (mapGate e)) (List.ofFn y)).getD (mapWire e C.output) false = _
    rw [hr2, ← hev (fun i => y (e i))]
    change _ = (wiresFrom C.gates (List.ofFn (fun i => y (e i)))).getD C.output false
    rw [hr1]
    unfold mapWire
    by_cases ho : C.output < n
    · rw [dif_pos ho]
      have h1 : (e ⟨C.output, ho⟩ : ℕ) < (List.ofFn y).length := by simp
      have h2 : C.output < (List.ofFn (fun i => y (e i))).length := by simp [ho]
      rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
      simp [List.getD_eq_getElem?_getD, ho]
    · rw [dif_neg ho]
      have h1 : (List.ofFn y).length ≤ C.output := by simp; omega
      have h2 : (List.ofFn (fun i : Fin n => y (e i))).length ≤ C.output := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h1, List.getElem?_append_right h2]

def ext {n : ℕ} (hn : 2 < n) (h : (Fin n → Bool) → Bool) (x : Fin (n + 2) → Bool) : Bool :=
  h (fun i => x (Fin.castAdd 2 i)) ||
    (x ⟨n, by omega⟩ && x ⟨n + 1, by omega⟩) ||
    (x ⟨n, by omega⟩ && x ⟨2, by omega⟩)

theorem elim_pendant {n s : ℕ} (hn : 2 < n) (h : (Fin n → Bool) → Bool)
    (h0 : h (fun _ => false) = false)
    (hz : ∃ z : Fin n → Bool, h z = true)
    (he2 : h (fun i => decide (i.val = 2)) = false)
    (hc : HasCircuitSize (n + 2) (ext hn h) s) :
    ∃ s' : ℕ, s' + 3 ≤ s ∧ HasCircuitSize n h s' := by
  obtain ⟨z, hz⟩ := hz
  have hdep1 : ∃ x : Fin (n + 2) → Bool,
      ext hn h (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1)))) ≠ ext hn h x := by
    let x0 : Fin (n + 2) → Bool := fun i => decide (i.val = n)
    refine ⟨x0, ?_⟩
    have hL : ext hn h (Function.update x0 (Fin.last (n + 1)) (!x0 (Fin.last (n + 1)))) = true := by
      unfold ext
      have hv1 : Function.update x0 (Fin.last (n + 1)) (!x0 (Fin.last (n + 1))) ⟨n, by omega⟩ = true := by
        rw [Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this)]
        simp [x0]
      have hv2 : Function.update x0 (Fin.last (n + 1)) (!x0 (Fin.last (n + 1))) ⟨n + 1, by omega⟩ = true := by
        have eqf : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by ext; simp
        rw [eqf, Function.update_self]
        simp [x0]
      simp [hv1, hv2]
    have hR : ext hn h x0 = false := by
      unfold ext
      have hcast : (fun i : Fin n => x0 (Fin.castAdd 2 i)) = fun _ => false := by
        funext i; simp [x0]; omega
      have hv1 : x0 ⟨n + 1, by omega⟩ = false := by simp [x0]
      have hv2 : x0 ⟨2, by omega⟩ = false := by simp [x0]; omega
      rw [hcast, h0, hv1, hv2]; simp
    rw [hL, hR]; decide
  have hnc1 : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
      ext hn h (Fin.snoc y b) ≠ ext hn h (Fin.snoc y' b) := by
    intro b
    refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc z false, ?_⟩
    have hL : ext hn h (Fin.snoc (Fin.snoc (fun _ => false) false) b) = false := by
      unfold ext
      have hcast : (fun i : Fin n => (Fin.snoc (Fin.snoc (fun _ => false) false) b : Fin (n + 2) → Bool) (Fin.castAdd 2 i)) = fun _ => false := by
        funext i
        have hi1 : (Fin.castAdd 2 i : Fin (n + 2)) = Fin.castSucc (Fin.castSucc i) := by ext; rfl
        rw [hi1, Fin.snoc_castSucc, Fin.snoc_castSucc]
      have hv : (Fin.snoc (Fin.snoc (fun _ => false) false) b : Fin (n + 2) → Bool) ⟨n, by omega⟩ = false := by
        have e : (⟨n, by omega⟩ : Fin (n + 2)) = Fin.castSucc (Fin.last n) := by ext; simp
        rw [e, Fin.snoc_castSucc, Fin.snoc_last]
      rw [hcast, h0, hv]; simp
    have hR : ext hn h (Fin.snoc (Fin.snoc z false) b) = true := by
      unfold ext
      have hcast : (fun i : Fin n => (Fin.snoc (Fin.snoc z false) b : Fin (n + 2) → Bool) (Fin.castAdd 2 i)) = z := by
        funext i
        have hi1 : (Fin.castAdd 2 i : Fin (n + 2)) = Fin.castSucc (Fin.castSucc i) := by ext; rfl
        rw [hi1, Fin.snoc_castSucc, Fin.snoc_castSucc]
      rw [hcast, hz]; simp
    rw [hL, hR]; decide
  obtain ⟨b, s1, hs1, hc1⟩ := gate_elim_two (n + 1) (ext hn h) s hdep1 hnc1 hc
  have hsnoc : ∀ w : Fin n → Bool, ext hn h (Fin.snoc (Fin.snoc w false) b) = h w := by
    intro w
    unfold ext
    have hcast : (fun i : Fin n => (Fin.snoc (Fin.snoc w false) b : Fin (n + 2) → Bool) (Fin.castAdd 2 i)) = w := by
      funext i
      have hi1 : (Fin.castAdd 2 i : Fin (n + 2)) = Fin.castSucc (Fin.castSucc i) := by ext; rfl
      rw [hi1, Fin.snoc_castSucc, Fin.snoc_castSucc]
    have hv : (Fin.snoc (Fin.snoc w false) b : Fin (n + 2) → Bool) ⟨n, by omega⟩ = false := by
      have e : (⟨n, by omega⟩ : Fin (n + 2)) = Fin.castSucc (Fin.last n) := by ext; simp
      rw [e, Fin.snoc_castSucc, Fin.snoc_last]
    rw [hcast, hv]; simp
  have hdep2 : ∃ y : Fin (n + 1) → Bool,
      ext hn h (Fin.snoc (Function.update y (Fin.last n) (!y (Fin.last n))) b) ≠
        ext hn h (Fin.snoc y b) := by
    cases b with
    | false =>
      let y0 : Fin (n + 1) → Bool := Fin.snoc (fun i : Fin n => decide (i.val = 2)) false
      refine ⟨y0, ?_⟩
      have hR : ext hn h (Fin.snoc y0 false) = false := by
        dsimp only [y0]; rw [hsnoc, he2]
      have hL : ext hn h (Fin.snoc (Function.update y0 (Fin.last n) (!y0 (Fin.last n))) false) = true := by
        unfold ext
        have hv1 : (Fin.snoc (Function.update y0 (Fin.last n) (!y0 (Fin.last n))) false : Fin (n + 2) → Bool) ⟨n, by omega⟩ = true := by
          have e : (⟨n, by omega⟩ : Fin (n + 2)) = Fin.castSucc (Fin.last n) := by ext; simp
          rw [e, Fin.snoc_castSucc, Function.update_self]
          simp [y0]
        have hv2 : (Fin.snoc (Function.update y0 (Fin.last n) (!y0 (Fin.last n))) false : Fin (n + 2) → Bool) ⟨2, by omega⟩ = true := by
          have e : (⟨2, by omega⟩ : Fin (n + 2)) = Fin.castSucc (Fin.castSucc ⟨2, hn⟩) := by ext; simp
          have hne : Fin.castSucc (⟨2, hn⟩ : Fin n) ≠ Fin.last n := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          rw [e, Fin.snoc_castSucc, Function.update_of_ne hne]
          dsimp only [y0]
          rw [Fin.snoc_castSucc]
          simp
        simp [hv1, hv2]
      rw [hL, hR]; decide
    | true =>
      let y0 : Fin (n + 1) → Bool := Fin.snoc (fun _ : Fin n => false) false
      refine ⟨y0, ?_⟩
      have hR : ext hn h (Fin.snoc y0 true) = false := by
        dsimp only [y0]; rw [hsnoc, h0]
      have hL : ext hn h (Fin.snoc (Function.update y0 (Fin.last n) (!y0 (Fin.last n))) true) = true := by
        unfold ext
        have hv1 : (Fin.snoc (Function.update y0 (Fin.last n) (!y0 (Fin.last n))) true : Fin (n + 2) → Bool) ⟨n, by omega⟩ = true := by
          have e : (⟨n, by omega⟩ : Fin (n + 2)) = Fin.castSucc (Fin.last n) := by ext; simp
          rw [e, Fin.snoc_castSucc, Function.update_self]
          simp [y0]
        have hv2 : (Fin.snoc (Function.update y0 (Fin.last n) (!y0 (Fin.last n))) true : Fin (n + 2) → Bool) ⟨n + 1, by omega⟩ = true := by
          have e : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by ext; simp
          rw [e, Fin.snoc_last]
        simp [hv1, hv2]
      rw [hL, hR]; decide
  have hnc2 : ∃ w w' : Fin n → Bool,
      ext hn h (Fin.snoc (Fin.snoc w false) b) ≠ ext hn h (Fin.snoc (Fin.snoc w' false) b) := by
    refine ⟨fun _ => false, z, ?_⟩
    rw [hsnoc, hsnoc, h0, hz]; decide
  obtain ⟨s2, hs2, hc2⟩ := gate_elim_one n (fun y => ext hn h (Fin.snoc y b)) false s1 hdep2 hnc2 hc1
  refine ⟨s2, by omega, ?_⟩
  obtain ⟨C, ok, hsz, hev⟩ := hc2
  exact ⟨C, ok, hsz, fun w => by have := hev w; dsimp only at this; rw [this, hsnoc w]⟩

def maj3 (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

def NonConstOnFix (f : (Fin 3 → Bool) → Bool) : Prop :=
  ∀ (i : Fin 3) (b : Bool), ∃ x y : Fin 3 → Bool, x i = b ∧ y i = b ∧ f x ≠ f y

def AtMostOneDep (f : (Fin 3 → Bool) → Bool) : Prop :=
  ∃ i : Fin 3, ∀ x y : Fin 3 → Bool, x i = y i → f x = f y

theorem nonConst_not {f : (Fin 3 → Bool) → Bool} (h : NonConstOnFix f) :
    NonConstOnFix (fun x => !(f x)) := by
  intro i b
  obtain ⟨x, y, hx, hy, hne⟩ := h i b
  exact ⟨x, y, hx, hy, fun e => hne (Bool.not_inj e)⟩

theorem maj3_nonConst : NonConstOnFix maj3 := by
  intro i b
  fin_cases i <;> cases b
  · exact ⟨fun k => decide (k.val = 1 ∨ k.val = 2), fun _ => false, by decide, by decide, by decide⟩
  · exact ⟨fun k => decide (k.val = 0 ∨ k.val = 1), fun k => decide (k.val = 0), by decide, by decide, by decide⟩
  · exact ⟨fun k => decide (k.val = 0 ∨ k.val = 2), fun _ => false, by decide, by decide, by decide⟩
  · exact ⟨fun k => decide (k.val = 0 ∨ k.val = 1), fun k => decide (k.val = 1), by decide, by decide, by decide⟩
  · exact ⟨fun k => decide (k.val = 0 ∨ k.val = 1), fun _ => false, by decide, by decide, by decide⟩
  · exact ⟨fun k => decide (k.val = 0 ∨ k.val = 2), fun k => decide (k.val = 2), by decide, by decide, by decide⟩

theorem not_atMostOneDep_of_nonConst {f : (Fin 3 → Bool) → Bool} (h : NonConstOnFix f) :
    ¬ AtMostOneDep f := by
  rintro ⟨i, hi⟩
  obtain ⟨x, y, hx, hy, hne⟩ := h i false
  exact hne (hi x y (hx.trans hy.symm))

theorem atMostOneDep_const (c : Bool) : AtMostOneDep (fun _ : Fin 3 → Bool => c) :=
  ⟨0, fun _ _ _ => rfl⟩

theorem atMostOneDep_not {u : (Fin 3 → Bool) → Bool} (h : AtMostOneDep u) :
    AtMostOneDep (fun x => !(u x)) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, fun x y hxy => congrArg (!·) (hi x y hxy)⟩

theorem and_left_const {u v : (Fin 3 → Bool) → Bool}
    (hnc : NonConstOnFix (fun x => u x && v x)) (hu : AtMostOneDep u) :
    ∀ x, u x = true := by
  obtain ⟨i, hi⟩ := hu
  intro x
  cases hux : u x with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨a, b, ha, hb, hne⟩ := hnc i (x i)
    have hua : u a = false := (hi a x ha).trans hux
    have hub : u b = false := (hi b x hb).trans hux
    simp [hua, hub] at hne

theorem or_left_const {u v : (Fin 3 → Bool) → Bool}
    (hnc : NonConstOnFix (fun x => u x || v x)) (hu : AtMostOneDep u) :
    ∀ x, u x = false := by
  obtain ⟨i, hi⟩ := hu
  intro x
  cases hux : u x with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨a, b, ha, hb, hne⟩ := hnc i (x i)
    have hua : u a = true := (hi a x ha).trans hux
    have hub : u b = true := (hi b x hb).trans hux
    simp [hua, hub] at hne

def wval (gs : List Gate) (w : ℕ) (x : Fin 3 → Bool) : Bool :=
  (wiresFrom gs (List.ofFn x)).getD w false

theorem wval_lt3 (gs : List Gate) (w : ℕ) (hw : w < 3) (x : Fin 3 → Bool) :
    wval gs w x = x ⟨w, hw⟩ := by
  unfold wval
  rw [getD_wiresFrom _ _ _ (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]
  rcases w with _ | _ | _ | _ <;> first | rfl | omega

theorem wval_ge (gs : List Gate) (w : ℕ) (hw : 3 + gs.length ≤ w) (x : Fin 3 → Bool) :
    wval gs w x = false := by
  unfold wval
  rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]

theorem wval_gate_cons (g : Gate) (gs : List Gate) (x : Fin 3 → Bool) :
    wval (g :: gs) 3 x = g.op.eval (g.inputs.map fun i => if h : i < 3 then x ⟨i, h⟩ else false) := by
  unfold wval
  have s : wiresFrom (g :: gs) (List.ofFn x) =
      wiresFrom gs (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]) := rfl
  rw [s, getD_wiresFrom _ _ _ (by simp)]
  have e : (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]).getD 3 false =
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) :=
    getD_snoc_len _ _ _ 3 (by simp)
  rw [e]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < 3
  · rw [dif_pos hi]
    simp [List.getD_eq_getElem?_getD, hi]
    rcases i with _ | _ | _ | _ <;> first | rfl | omega
  · rw [dif_neg hi, List.getD_eq_default _ _ (by simp; omega)]

theorem wval_gate_two (g0 g1 : Gate) (gs : List Gate) (x : Fin 3 → Bool) :
    wval (g0 :: g1 :: gs) 4 x =
      g1.op.eval (g1.inputs.map fun i => if i < 4 then wval (g0 :: g1 :: gs) i x else false) := by
  unfold wval
  set v0 := g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)
  set l1 := List.ofFn x ++ [v0]
  have hl1 : l1.length = 4 := by simp [l1]
  set v1 := g1.op.eval (g1.inputs.map fun i => l1.getD i false)
  have s : wiresFrom (g0 :: g1 :: gs) (List.ofFn x) = wiresFrom gs (l1 ++ [v1]) := rfl
  rw [s, getD_wiresFrom _ _ _ (by simp [hl1])]
  rw [getD_snoc_len _ _ _ 4 hl1]
  dsimp only [v1]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < 4
  · rw [if_pos hi, getD_wiresFrom _ _ _ (by simp [hl1]; omega)]
    exact (List.getD_append _ _ _ _ (by omega)).symm
  · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]

theorem wval_gate_three (g0 g1 g2 : Gate) (x : Fin 3 → Bool) :
    wval [g0, g1, g2] 5 x =
      g2.op.eval (g2.inputs.map fun i => if i < 5 then wval [g0, g1, g2] i x else false) := by
  unfold wval
  set v0 := g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)
  set l1 := List.ofFn x ++ [v0]
  have hl1 : l1.length = 4 := by simp [l1]
  set v1 := g1.op.eval (g1.inputs.map fun i => l1.getD i false)
  set l2 := l1 ++ [v1]
  have hl2 : l2.length = 5 := by simp [l2, hl1]
  set v2 := g2.op.eval (g2.inputs.map fun i => l2.getD i false)
  have s : wiresFrom [g0, g1, g2] (List.ofFn x) = l2 ++ [v2] := rfl
  rw [s, getD_snoc_len _ _ _ 5 hl2]
  dsimp only [v2]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < 5
  · rw [if_pos hi]
    exact (List.getD_append _ _ _ _ (by omega)).symm
  · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]

theorem eval_gate_cases (g : Gate) (hnok : NOk g) (F : ℕ → (Fin 3 → Bool) → Bool) :
    (∀ x, g.op.eval (g.inputs.map fun i => F i x) = true) ∨
    (∀ x, g.op.eval (g.inputs.map fun i => F i x) = false) ∨
    (∃ a ∈ g.inputs, ∀ x, g.op.eval (g.inputs.map fun i => F i x) = F a x) ∨
    (∃ a ∈ g.inputs, ∀ x, g.op.eval (g.inputs.map fun i => F i x) = !(F a x)) ∨
    (∃ a ∈ g.inputs, ∃ b ∈ g.inputs, ∀ x, g.op.eval (g.inputs.map fun i => F i x) = (F a x && F b x)) ∨
    (∃ a ∈ g.inputs, ∃ b ∈ g.inputs, ∀ x, g.op.eval (g.inputs.map fun i => F i x) = (F a x || F b x)) := by
  obtain ⟨⟨hop, hlen⟩, hnot⟩ := hnok
  rcases hop with h | h | h
  · rw [h]
    rcases hg : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · left; intro x; simp [GateOp.eval]
    · right; right; left; exact ⟨a, by simp, fun x => by simp [GateOp.eval]⟩
    · right; right; right; right; left; exact ⟨a, by simp, b, by simp, fun x => by simp [GateOp.eval]⟩
    · simp [hg] at hlen
  · rw [h]
    rcases hg : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · right; left; intro x; simp [GateOp.eval]
    · right; right; left; exact ⟨a, by simp, fun x => by simp [GateOp.eval]⟩
    · right; right; right; right; right; exact ⟨a, by simp, b, by simp, fun x => by simp [GateOp.eval]⟩
    · simp [hg] at hlen
  · have hnl := hnot h
    rw [h]
    rcases hg : g.inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
    · left; intro x; simp [GateOp.eval]
    · right; right; right; left; exact ⟨a, by simp, fun x => by simp [GateOp.eval]⟩
    · simp [hg] at hnl

theorem no_nonConst_lt3 (gs : List Gate) (w : ℕ) (hw : w < 3) :
    ¬ NonConstOnFix (wval gs w) := by
  intro hnc
  apply not_atMostOneDep_of_nonConst hnc
  exact ⟨⟨w, hw⟩, fun x y hxy => by rw [wval_lt3 gs w hw x, wval_lt3 gs w hw y, hxy]⟩

theorem no_nonConst_1 (g0 : Gate) (gs : List Gate) (h0 : NOk g0) :
    ¬ NonConstOnFix (wval (g0 :: gs) 3) := by
  intro hnc
  let F : ℕ → (Fin 3 → Bool) → Bool := fun i x => if h : i < 3 then x ⟨i, h⟩ else false
  have hF1 : ∀ i, AtMostOneDep (F i) := fun i => by
    by_cases hi : i < 3
    · exact ⟨⟨i, hi⟩, fun x y hxy => by simp [F, hi, hxy]⟩
    · exact ⟨0, fun x y _ => by simp [F, hi]⟩
  have heq : wval (g0 :: gs) 3 = fun x => g0.op.eval (g0.inputs.map fun i => F i x) := by
    funext x; exact wval_gate_cons g0 gs x
  rw [heq] at hnc
  rcases eval_gate_cases g0 h0 F with hc | hc | ⟨a, _, hc⟩ | ⟨a, _, hc⟩ | ⟨a, _, b, _, hc⟩ | ⟨a, _, b, _, hc⟩
  · exact not_atMostOneDep_of_nonConst (by simpa [funext hc] using hnc) (atMostOneDep_const true)
  · exact not_atMostOneDep_of_nonConst (by simpa [funext hc] using hnc) (atMostOneDep_const false)
  · exact not_atMostOneDep_of_nonConst (by simpa [funext hc] using hnc) (hF1 a)
  · exact not_atMostOneDep_of_nonConst (by simpa [funext hc] using hnc) (atMostOneDep_not (hF1 a))
  · have hnc' : NonConstOnFix (fun x => F a x && F b x) := by simpa [funext hc] using hnc
    have ha := and_left_const hnc' (hF1 a)
    exact not_atMostOneDep_of_nonConst (by simpa [ha] using hnc') (hF1 b)
  · have hnc' : NonConstOnFix (fun x => F a x || F b x) := by simpa [funext hc] using hnc
    have ha := or_left_const hnc' (hF1 a)
    exact not_atMostOneDep_of_nonConst (by simpa [ha] using hnc') (hF1 b)

theorem no_nonConst_2 (g0 g1 : Gate) (gs : List Gate) (h0 : NOk g0) (h1 : NOk g1) :
    ¬ NonConstOnFix (wval (g0 :: g1 :: gs) 4) := by
  intro hnc
  let F : ℕ → (Fin 3 → Bool) → Bool := fun i x => if i < 4 then wval (g0 :: g1 :: gs) i x else false
  have hFne3 : ∀ i, i ≠ 3 → AtMostOneDep (F i) := fun i hi => by
    by_cases hlt : i < 3
    · exact ⟨⟨i, hlt⟩, fun x y hxy => by simp [F, show i < 4 by omega, wval_lt3 _ _ hlt, hxy]⟩
    · exact ⟨0, fun x y _ => by simp [F, show ¬ i < 4 by omega]⟩
  have hF3 : ¬ NonConstOnFix (F 3) := by
    have : F 3 = wval (g0 :: g1 :: gs) 3 := by funext x; simp [F]
    rw [this]; exact no_nonConst_1 g0 (g1 :: gs) h0
  have hF : ∀ i, ¬ NonConstOnFix (F i) := fun i => by
    by_cases hi : i = 3
    · subst hi; exact hF3
    · exact fun hc => not_atMostOneDep_of_nonConst hc (hFne3 i hi)
  have heq : wval (g0 :: g1 :: gs) 4 = fun x => g1.op.eval (g1.inputs.map fun i => F i x) := by
    funext x; exact wval_gate_two g0 g1 gs x
  rw [heq] at hnc
  rcases eval_gate_cases g1 h1 F with hc | hc | ⟨a, _, hc⟩ | ⟨a, _, hc⟩ | ⟨a, _, b, _, hc⟩ | ⟨a, _, b, _, hc⟩
  · exact not_atMostOneDep_of_nonConst (by simpa [funext hc] using hnc) (atMostOneDep_const true)
  · exact not_atMostOneDep_of_nonConst (by simpa [funext hc] using hnc) (atMostOneDep_const false)
  · exact hF a (by simpa [funext hc] using hnc)
  · have hfa : F a = fun x => !(g1.op.eval (g1.inputs.map fun i => F i x)) := by
      funext x; rw [hc x, Bool.not_not]
    exact hF a (hfa ▸ nonConst_not hnc)
  · have hnc' : NonConstOnFix (fun x => F a x && F b x) := by simpa [funext hc] using hnc
    by_cases ha3 : a = 3
    · by_cases hb3 : b = 3
      · subst ha3 hb3; exact hF3 (by simpa using hnc')
      · have hb := and_left_const (by simpa [Bool.and_comm] using hnc') (hFne3 b hb3)
        exact hF a (by simpa [hb] using hnc')
    · have ha := and_left_const hnc' (hFne3 a ha3)
      exact hF b (by simpa [ha] using hnc')
  · have hnc' : NonConstOnFix (fun x => F a x || F b x) := by simpa [funext hc] using hnc
    by_cases ha3 : a = 3
    · by_cases hb3 : b = 3
      · subst ha3 hb3; exact hF3 (by simpa using hnc')
      · have hb := or_left_const (by simpa [Bool.or_comm] using hnc') (hFne3 b hb3)
        exact hF a (by simpa [hb] using hnc')
    · have ha := or_left_const hnc' (hFne3 a ha3)
      exact hF b (by simpa [ha] using hnc')

theorem fin3_pair_inter (p q r s : Fin 3) (hpq : p ≠ q) (hrs : r ≠ s) :
    ∃ k : Fin 3, (k = p ∨ k = q) ∧ (k = r ∨ k = s) := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases s <;>
    first | exact absurd rfl hpq | exact absurd rfl hrs | decide

theorem no_maj3_3 (g0 g1 g2 : Gate) (h0 : NOk g0) (h1 : NOk g1) (h2 : NOk g2) :
    wval [g0, g1, g2] 5 ≠ maj3 := by
  intro hevm
  have hnc : NonConstOnFix (wval [g0, g1, g2] 5) := hevm ▸ maj3_nonConst
  let F : ℕ → (Fin 3 → Bool) → Bool := fun i x => if i < 5 then wval [g0, g1, g2] i x else false
  have hFne : ∀ i, i ≠ 3 → i ≠ 4 → AtMostOneDep (F i) := fun i h3 h4 => by
    by_cases hlt : i < 3
    · exact ⟨⟨i, hlt⟩, fun x y hxy => by simp [F, show i < 5 by omega, wval_lt3 _ _ hlt, hxy]⟩
    · exact ⟨0, fun x y _ => by simp [F, show ¬ i < 5 by omega]⟩
  have hFno : ∀ i, ¬ NonConstOnFix (F i) := fun i => by
    by_cases h3 : i = 3
    · subst h3; simpa [F] using no_nonConst_1 g0 [g1, g2] h0
    · by_cases h4 : i = 4
      · subst h4; simpa [F] using no_nonConst_2 g0 g1 [g2] h0 h1
      · exact fun hc => not_atMostOneDep_of_nonConst hc (hFne i h3 h4)
  have hF3eq : F 3 = wval [g0, g1, g2] 3 := by funext x; simp [F]
  have hF4eq : F 4 = wval [g0, g1, g2] 4 := by funext x; simp [F]
  have heq2 : wval [g0, g1, g2] 5 = fun x => g2.op.eval (g2.inputs.map fun i => F i x) := by
    funext x; exact wval_gate_three g0 g1 g2 x
  have hpair : (∀ x, (wval [g0, g1, g2] 3 x && wval [g0, g1, g2] 4 x) = maj3 x) ∨
      (∀ x, (wval [g0, g1, g2] 3 x || wval [g0, g1, g2] 4 x) = maj3 x) := by
    rw [heq2] at hnc hevm
    rcases eval_gate_cases g2 h2 F with hc | hc | ⟨a, _, hc⟩ | ⟨a, _, hc⟩ | ⟨a, _, b, _, hc⟩ | ⟨a, _, b, _, hc⟩
    · exact absurd (by simpa [funext hc] using hnc) (fun h => not_atMostOneDep_of_nonConst h (atMostOneDep_const true))
    · exact absurd (by simpa [funext hc] using hnc) (fun h => not_atMostOneDep_of_nonConst h (atMostOneDep_const false))
    · exact absurd (by simpa [funext hc] using hnc) (hFno a)
    · have hfa : F a = fun x => !(g2.op.eval (g2.inputs.map fun i => F i x)) := by
        funext x; rw [hc x, Bool.not_not]
      exact absurd (hfa ▸ nonConst_not hnc) (hFno a)
    · have hnc' : NonConstOnFix (fun x => F a x && F b x) := by simpa [funext hc] using hnc
      have hev' : ∀ x, (F a x && F b x) = maj3 x := fun x => by
        have hx := congrFun hevm x; rw [← hc x]; exact hx
      by_cases ha3 : a = 3
      · subst ha3
        by_cases hb4 : b = 4
        · subst hb4; left; intro x; have hx := hev' x; rw [hF3eq, hF4eq] at hx; exact hx
        · by_cases hb3 : b = 3
          · subst hb3
            have h3nc : NonConstOnFix (F 3) := by
              have e : (fun x => F 3 x && F 3 x) = F 3 := by funext x; simp
              rwa [e] at hnc'
            exact absurd h3nc (hFno 3)
          · have hnc_sw : NonConstOnFix (fun x => F b x && F 3 x) := by
              have e : (fun x => F 3 x && F b x) = (fun x => F b x && F 3 x) := by
                funext x; exact Bool.and_comm _ _
              rwa [e] at hnc'
            have hb := and_left_const hnc_sw (hFne b hb3 hb4)
            have h3nc : NonConstOnFix (F 3) := by
              have e : (fun x => F 3 x && F b x) = F 3 := by funext x; rw [hb x]; simp
              rwa [e] at hnc'
            exact absurd h3nc (hFno 3)
      · by_cases ha4 : a = 4
        · subst ha4
          by_cases hb3 : b = 3
          · subst hb3; left; intro x; have hx := hev' x; rw [hF3eq, hF4eq, Bool.and_comm] at hx; exact hx
          · by_cases hb4 : b = 4
            · subst hb4
              have h4nc : NonConstOnFix (F 4) := by
                have e : (fun x => F 4 x && F 4 x) = F 4 := by funext x; simp
                rwa [e] at hnc'
              exact absurd h4nc (hFno 4)
            · have hnc_sw : NonConstOnFix (fun x => F b x && F 4 x) := by
                have e : (fun x => F 4 x && F b x) = (fun x => F b x && F 4 x) := by
                  funext x; exact Bool.and_comm _ _
                rwa [e] at hnc'
              have hb := and_left_const hnc_sw (hFne b hb3 hb4)
              have h4nc : NonConstOnFix (F 4) := by
                have e : (fun x => F 4 x && F b x) = F 4 := by funext x; rw [hb x]; simp
                rwa [e] at hnc'
              exact absurd h4nc (hFno 4)
        · have ha := and_left_const hnc' (hFne a ha3 ha4)
          have hbnc : NonConstOnFix (F b) := by
            have e : (fun x => F a x && F b x) = F b := by funext x; rw [ha x]; simp
            rwa [e] at hnc'
          exact absurd hbnc (hFno b)
    · have hnc' : NonConstOnFix (fun x => F a x || F b x) := by simpa [funext hc] using hnc
      have hev' : ∀ x, (F a x || F b x) = maj3 x := fun x => by
        have hx := congrFun hevm x; rw [← hc x]; exact hx
      by_cases ha3 : a = 3
      · subst ha3
        by_cases hb4 : b = 4
        · subst hb4; right; intro x; have hx := hev' x; rw [hF3eq, hF4eq] at hx; exact hx
        · by_cases hb3 : b = 3
          · subst hb3
            have h3nc : NonConstOnFix (F 3) := by
              have e : (fun x => F 3 x || F 3 x) = F 3 := by funext x; simp
              rwa [e] at hnc'
            exact absurd h3nc (hFno 3)
          · have hnc_sw : NonConstOnFix (fun x => F b x || F 3 x) := by
              have e : (fun x => F 3 x || F b x) = (fun x => F b x || F 3 x) := by
                funext x; exact Bool.or_comm _ _
              rwa [e] at hnc'
            have hb := or_left_const hnc_sw (hFne b hb3 hb4)
            have h3nc : NonConstOnFix (F 3) := by
              have e : (fun x => F 3 x || F b x) = F 3 := by funext x; rw [hb x]; simp
              rwa [e] at hnc'
            exact absurd h3nc (hFno 3)
      · by_cases ha4 : a = 4
        · subst ha4
          by_cases hb3 : b = 3
          · subst hb3; right; intro x; have hx := hev' x; rw [hF3eq, hF4eq, Bool.or_comm] at hx; exact hx
          · by_cases hb4 : b = 4
            · subst hb4
              have h4nc : NonConstOnFix (F 4) := by
                have e : (fun x => F 4 x || F 4 x) = F 4 := by funext x; simp
                rwa [e] at hnc'
              exact absurd h4nc (hFno 4)
            · have hnc_sw : NonConstOnFix (fun x => F b x || F 4 x) := by
                have e : (fun x => F 4 x || F b x) = (fun x => F b x || F 4 x) := by
                  funext x; exact Bool.or_comm _ _
                rwa [e] at hnc'
              have hb := or_left_const hnc_sw (hFne b hb3 hb4)
              have h4nc : NonConstOnFix (F 4) := by
                have e : (fun x => F 4 x || F b x) = F 4 := by funext x; rw [hb x]; simp
                rwa [e] at hnc'
              exact absurd h4nc (hFno 4)
        · have ha := or_left_const hnc' (hFne a ha3 ha4)
          have hbnc : NonConstOnFix (F b) := by
            have e : (fun x => F a x || F b x) = F b := by funext x; rw [ha x]; simp
            rwa [e] at hnc'
          exact absurd hbnc (hFno b)
  have hnot1_3 : ¬ AtMostOneDep (wval [g0, g1, g2] 3) := by
    intro hd
    rcases hpair with hp | hp
    · have hnc' : NonConstOnFix (fun x => wval [g0, g1, g2] 3 x && wval [g0, g1, g2] 4 x) := by
        simpa [funext hp] using maj3_nonConst
      have h3t := and_left_const hnc' hd
      exact no_nonConst_2 g0 g1 [g2] h0 h1 (by simpa [h3t] using hnc')
    · have hnc' : NonConstOnFix (fun x => wval [g0, g1, g2] 3 x || wval [g0, g1, g2] 4 x) := by
        simpa [funext hp] using maj3_nonConst
      have h3f := or_left_const hnc' hd
      exact no_nonConst_2 g0 g1 [g2] h0 h1 (by simpa [h3f] using hnc')
  have hnot1_4 : ¬ AtMostOneDep (wval [g0, g1, g2] 4) := by
    intro hd
    rcases hpair with hp | hp
    · have hnc' : NonConstOnFix (fun x => wval [g0, g1, g2] 4 x && wval [g0, g1, g2] 3 x) := by
        simpa [Bool.and_comm, funext hp] using maj3_nonConst
      have h4t := and_left_const hnc' hd
      exact no_nonConst_1 g0 [g1, g2] h0 (by simpa [h4t] using hnc')
    · have hnc' : NonConstOnFix (fun x => wval [g0, g1, g2] 4 x || wval [g0, g1, g2] 3 x) := by
        simpa [Bool.or_comm, funext hp] using maj3_nonConst
      have h4f := or_left_const hnc' hd
      exact no_nonConst_1 g0 [g1, g2] h0 (by simpa [h4f] using hnc')
  let F0 : ℕ → (Fin 3 → Bool) → Bool := fun i x => if h : i < 3 then x ⟨i, h⟩ else false
  have hF0d : ∀ i, AtMostOneDep (F0 i) := fun i => by
    by_cases hi : i < 3
    · exact ⟨⟨i, hi⟩, fun x y hxy => by simp [F0, hi, hxy]⟩
    · exact ⟨0, fun x y _ => by simp [F0, hi]⟩
  have h3shape : (∃ p q : Fin 3, p ≠ q ∧ ∀ x, wval [g0, g1, g2] 3 x = (x p && x q)) ∨
      (∃ p q : Fin 3, p ≠ q ∧ ∀ x, wval [g0, g1, g2] 3 x = (x p || x q)) := by
    have heq0 : ∀ x, wval [g0, g1, g2] 3 x = g0.op.eval (g0.inputs.map fun i => F0 i x) :=
      fun x => wval_gate_cons g0 [g1, g2] x
    rcases eval_gate_cases g0 h0 F0 with hc | hc | ⟨a, _, hc⟩ | ⟨a, _, hc⟩ | ⟨a, _, b, _, hc⟩ | ⟨a, _, b, _, hc⟩
    · exact absurd (by have e : wval [g0, g1, g2] 3 = fun _ => true := funext fun x => (heq0 x).trans (hc x); rw [e]; exact atMostOneDep_const true) hnot1_3
    · exact absurd (by have e : wval [g0, g1, g2] 3 = fun _ => false := funext fun x => (heq0 x).trans (hc x); rw [e]; exact atMostOneDep_const false) hnot1_3
    · exact absurd (by have e : wval [g0, g1, g2] 3 = F0 a := funext fun x => (heq0 x).trans (hc x); rw [e]; exact hF0d a) hnot1_3
    · exact absurd (by have e : wval [g0, g1, g2] 3 = fun x => !(F0 a x) := funext fun x => (heq0 x).trans (hc x); rw [e]; exact atMostOneDep_not (hF0d a)) hnot1_3
    · by_cases ha : a < 3
      · by_cases hb : b < 3
        · by_cases hab : (⟨a, ha⟩ : Fin 3) = ⟨b, hb⟩
          · exfalso; apply hnot1_3
            refine ⟨⟨a, ha⟩, fun x y hxy => ?_⟩
            rw [heq0 x, heq0 y, hc x, hc y]; simp [F0, ha, hb, ← hab, hxy]
          · left; exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, fun x => by rw [heq0 x, hc x]; simp [F0, ha, hb]⟩
        · exfalso; apply hnot1_3
          refine ⟨0, fun x y _ => ?_⟩; rw [heq0 x, heq0 y, hc x, hc y]; simp [F0, hb]
      · exfalso; apply hnot1_3
        refine ⟨0, fun x y _ => ?_⟩; rw [heq0 x, heq0 y, hc x, hc y]; simp [F0, ha]
    · by_cases ha : a < 3
      · by_cases hb : b < 3
        · by_cases hab : (⟨a, ha⟩ : Fin 3) = ⟨b, hb⟩
          · exfalso; apply hnot1_3
            refine ⟨⟨a, ha⟩, fun x y hxy => ?_⟩
            rw [heq0 x, heq0 y, hc x, hc y]; simp [F0, ha, hb, ← hab, hxy]
          · right; exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, fun x => by rw [heq0 x, hc x]; simp [F0, ha, hb]⟩
        · exfalso; apply hnot1_3
          refine ⟨⟨a, ha⟩, fun x y hxy => ?_⟩; rw [heq0 x, heq0 y, hc x, hc y]; simp [F0, ha, hb, hxy]
      · exfalso; apply hnot1_3
        by_cases hb : b < 3
        · refine ⟨⟨b, hb⟩, fun x y hxy => ?_⟩; rw [heq0 x, heq0 y, hc x, hc y]; simp [F0, ha, hb, hxy]
        · refine ⟨0, fun x y _ => ?_⟩; rw [heq0 x, heq0 y, hc x, hc y]; simp [F0, ha, hb]
  let F1 : ℕ → (Fin 3 → Bool) → Bool := fun i x => if i < 4 then wval [g0, g1, g2] i x else false
  have hF1ne : ∀ i, i ≠ 3 → AtMostOneDep (F1 i) := fun i hi => by
    by_cases hlt : i < 3
    · exact ⟨⟨i, hlt⟩, fun x y hxy => by simp [F1, show i < 4 by omega, wval_lt3 _ _ hlt, hxy]⟩
    · exact ⟨0, fun x y _ => by simp [F1, show ¬ i < 4 by omega]⟩
  have hF1_3 : ∀ x, F1 3 x = wval [g0, g1, g2] 3 x := fun x => by simp [F1]
  have heq1 : ∀ x, wval [g0, g1, g2] 4 x = g1.op.eval (g1.inputs.map fun i => F1 i x) :=
    fun x => wval_gate_two g0 g1 [g2] x
  have h4cases :
      (∃ r s : Fin 3, r ≠ s ∧ ∀ x, wval [g0, g1, g2] 4 x = (x r && x s)) ∨
      (∃ r s : Fin 3, r ≠ s ∧ ∀ x, wval [g0, g1, g2] 4 x = (x r || x s)) := by
    rcases eval_gate_cases g1 h1 F1 with hc | hc | ⟨a, _, hc⟩ | ⟨a, _, hc⟩ | ⟨a, _, b, _, hc⟩ | ⟨a, _, b, _, hc⟩
    · exact absurd (by have e : wval [g0, g1, g2] 4 = fun _ => true := funext fun x => (heq1 x).trans (hc x); rw [e]; exact atMostOneDep_const true) hnot1_4
    · exact absurd (by have e : wval [g0, g1, g2] 4 = fun _ => false := funext fun x => (heq1 x).trans (hc x); rw [e]; exact atMostOneDep_const false) hnot1_4
    · by_cases ha3 : a = 3
      · subst ha3
        exfalso
        have h34 : ∀ x, wval [g0, g1, g2] 4 x = wval [g0, g1, g2] 3 x := fun x => by
          rw [heq1 x, hc x, hF1_3 x]
        rcases hpair with hp | hp
        · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
            have := hp x; rw [h34 x] at this; simpa using this
          exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
        · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
            have := hp x; rw [h34 x] at this; simpa using this
          exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
      · exact absurd (by have e : wval [g0, g1, g2] 4 = F1 a := funext fun x => (heq1 x).trans (hc x); rw [e]; exact hF1ne a ha3) hnot1_4
    · by_cases ha3 : a = 3
      · subst ha3
        exfalso
        have h34 : ∀ x, wval [g0, g1, g2] 4 x = !(wval [g0, g1, g2] 3 x) := fun x => by
          rw [heq1 x, hc x, hF1_3 x]
        rcases hpair with hp | hp
        · have : maj3 (fun _ => true) = false := by rw [← hp, h34]; simp
          simp [maj3] at this
        · have : maj3 (fun _ => false) = true := by rw [← hp, h34]; simp
          simp [maj3] at this
      · exact absurd (by have e : wval [g0, g1, g2] 4 = fun x => !(F1 a x) := funext fun x => (heq1 x).trans (hc x); rw [e]; exact atMostOneDep_not (hF1ne a ha3)) hnot1_4
    · by_cases ha3 : a = 3
      · subst ha3
        exfalso
        have h4eq : ∀ x, wval [g0, g1, g2] 4 x = (wval [g0, g1, g2] 3 x && F1 b x) := fun x => by
          rw [heq1 x, hc x, hF1_3 x]
        by_cases hb3 : b = 3
        · subst hb3
          rcases hpair with hp | hp
          · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
              have := hp x; rw [h4eq x, hF1_3 x] at this; simpa using this
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
          · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
              have := hp x; rw [h4eq x, hF1_3 x] at this; simpa using this
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
        · rcases hpair with hp | hp
          · have hnc' : NonConstOnFix (fun x => F1 b x && wval [g0, g1, g2] 3 x) := by
              have e : (fun x => F1 b x && wval [g0, g1, g2] 3 x) = maj3 := funext fun x => by
                rw [← hp x, h4eq x]; cases wval [g0, g1, g2] 3 x <;> cases F1 b x <;> rfl
              rw [e]; exact maj3_nonConst
            have hbt := and_left_const hnc' (hF1ne b hb3)
            have e : (fun x => F1 b x && wval [g0, g1, g2] 3 x) = wval [g0, g1, g2] 3 :=
              funext fun x => by rw [hbt x]; simp
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ hnc')
          · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
              rw [← hp x, h4eq x]; cases wval [g0, g1, g2] 3 x <;> cases F1 b x <;> rfl
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
      · by_cases hb3 : b = 3
        · subst hb3
          exfalso
          have h4eq : ∀ x, wval [g0, g1, g2] 4 x = (F1 a x && wval [g0, g1, g2] 3 x) := fun x => by
            rw [heq1 x, hc x, hF1_3 x]
          rcases hpair with hp | hp
          · have hnc' : NonConstOnFix (fun x => F1 a x && wval [g0, g1, g2] 3 x) := by
              have e : (fun x => F1 a x && wval [g0, g1, g2] 3 x) = maj3 := funext fun x => by
                rw [← hp x, h4eq x]; cases wval [g0, g1, g2] 3 x <;> cases F1 a x <;> rfl
              rw [e]; exact maj3_nonConst
            have hat := and_left_const hnc' (hF1ne a ha3)
            have e : (fun x => F1 a x && wval [g0, g1, g2] 3 x) = wval [g0, g1, g2] 3 :=
              funext fun x => by rw [hat x]; simp
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ hnc')
          · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
              rw [← hp x, h4eq x]; cases wval [g0, g1, g2] 3 x <;> cases F1 a x <;> rfl
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
        · by_cases ha : a < 3
          · by_cases hb : b < 3
            · by_cases hab : (⟨a, ha⟩ : Fin 3) = ⟨b, hb⟩
              · exfalso; apply hnot1_4
                refine ⟨⟨a, ha⟩, fun x y hxy => ?_⟩
                rw [heq1 x, heq1 y, hc x, hc y]
                simp [F1, show a < 4 by omega, show b < 4 by omega, wval_lt3 _ _ ha, wval_lt3 _ _ hb, ← hab, hxy]
              · left; refine ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, fun x => ?_⟩
                rw [heq1 x, hc x]
                simp [F1, show a < 4 by omega, show b < 4 by omega, wval_lt3 _ _ ha, wval_lt3 _ _ hb]
            · exfalso; apply hnot1_4
              refine ⟨0, fun x y _ => ?_⟩
              rw [heq1 x, heq1 y, hc x, hc y]; simp [F1, show ¬ b < 4 by omega]
          · exfalso; apply hnot1_4
            refine ⟨0, fun x y _ => ?_⟩
            rw [heq1 x, heq1 y, hc x, hc y]; simp [F1, show ¬ a < 4 by omega]
    · by_cases ha3 : a = 3
      · subst ha3
        exfalso
        have h4eq : ∀ x, wval [g0, g1, g2] 4 x = (wval [g0, g1, g2] 3 x || F1 b x) := fun x => by
          rw [heq1 x, hc x, hF1_3 x]
        by_cases hb3 : b = 3
        · subst hb3
          rcases hpair with hp | hp
          · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
              have := hp x; rw [h4eq x, hF1_3 x] at this; simpa using this
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
          · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
              have := hp x; rw [h4eq x, hF1_3 x] at this; simpa using this
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
        · rcases hpair with hp | hp
          · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
              rw [← hp x, h4eq x]; cases wval [g0, g1, g2] 3 x <;> cases F1 b x <;> rfl
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
          · have hnc' : NonConstOnFix (fun x => F1 b x || wval [g0, g1, g2] 3 x) := by
              have e : (fun x => F1 b x || wval [g0, g1, g2] 3 x) = maj3 := funext fun x => by
                rw [← hp x, h4eq x]; cases wval [g0, g1, g2] 3 x <;> cases F1 b x <;> rfl
              rw [e]; exact maj3_nonConst
            have hbf := or_left_const hnc' (hF1ne b hb3)
            have e : (fun x => F1 b x || wval [g0, g1, g2] 3 x) = wval [g0, g1, g2] 3 :=
              funext fun x => by rw [hbf x]; simp
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ hnc')
      · by_cases hb3 : b = 3
        · subst hb3
          exfalso
          have h4eq : ∀ x, wval [g0, g1, g2] 4 x = (F1 a x || wval [g0, g1, g2] 3 x) := fun x => by
            rw [heq1 x, hc x, hF1_3 x]
          rcases hpair with hp | hp
          · have e : wval [g0, g1, g2] 3 = maj3 := funext fun x => by
              rw [← hp x, h4eq x]; cases wval [g0, g1, g2] 3 x <;> cases F1 a x <;> rfl
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ maj3_nonConst)
          · have hnc' : NonConstOnFix (fun x => F1 a x || wval [g0, g1, g2] 3 x) := by
              have e : (fun x => F1 a x || wval [g0, g1, g2] 3 x) = maj3 := funext fun x => by
                rw [← hp x, h4eq x]; cases wval [g0, g1, g2] 3 x <;> cases F1 a x <;> rfl
              rw [e]; exact maj3_nonConst
            have haf := or_left_const hnc' (hF1ne a ha3)
            have e : (fun x => F1 a x || wval [g0, g1, g2] 3 x) = wval [g0, g1, g2] 3 :=
              funext fun x => by rw [haf x]; simp
            exact no_nonConst_1 g0 [g1, g2] h0 (e ▸ hnc')
        · by_cases ha : a < 3
          · by_cases hb : b < 3
            · by_cases hab : (⟨a, ha⟩ : Fin 3) = ⟨b, hb⟩
              · exfalso; apply hnot1_4
                refine ⟨⟨a, ha⟩, fun x y hxy => ?_⟩
                rw [heq1 x, heq1 y, hc x, hc y]
                simp [F1, show a < 4 by omega, show b < 4 by omega, wval_lt3 _ _ ha, wval_lt3 _ _ hb, ← hab, hxy]
              · right; refine ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, fun x => ?_⟩
                rw [heq1 x, hc x]
                simp [F1, show a < 4 by omega, show b < 4 by omega, wval_lt3 _ _ ha, wval_lt3 _ _ hb]
            · exfalso; apply hnot1_4
              refine ⟨⟨a, ha⟩, fun x y hxy => ?_⟩
              rw [heq1 x, heq1 y, hc x, hc y]
              simp [F1, show a < 4 by omega, show ¬ b < 4 by omega, wval_lt3 _ _ ha, hxy]
          · exfalso; apply hnot1_4
            by_cases hb : b < 3
            · refine ⟨⟨b, hb⟩, fun x y hxy => ?_⟩
              rw [heq1 x, heq1 y, hc x, hc y]
              simp [F1, show ¬ a < 4 by omega, show b < 4 by omega, wval_lt3 _ _ hb, hxy]
            · refine ⟨0, fun x y _ => ?_⟩
              rw [heq1 x, heq1 y, hc x, hc y]
              simp [F1, show ¬ a < 4 by omega, show ¬ b < 4 by omega]
  rcases hpair with hp | hp
  · rcases h3shape with ⟨p, q, hpq, h3⟩ | ⟨p, q, hpq, h3⟩
    · obtain ⟨x, y, hx, hy, hne⟩ := maj3_nonConst p false
      have hx' : maj3 x = false := by rw [← hp x, h3 x, hx]; simp
      have hy' : maj3 y = false := by rw [← hp y, h3 y, hy]; simp
      exact hne (hx'.trans hy'.symm)
    · rcases h4cases with ⟨r, s, hrs, h4⟩ | ⟨r, s, hrs, h4⟩
      · obtain ⟨x, y, hx, hy, hne⟩ := maj3_nonConst r false
        have hx' : maj3 x = false := by rw [← hp x, h4 x, hx]; simp
        have hy' : maj3 y = false := by rw [← hp y, h4 y, hy]; simp
        exact hne (hx'.trans hy'.symm)
      · obtain ⟨k, hk1, hk2⟩ := fin3_pair_inter p q r s hpq hrs
        have h1' := hp (fun i => decide (i = k))
        rw [h3, h4] at h1'
        have ha : (decide (p = k) || decide (q = k)) = true := by
          rcases hk1 with rfl | rfl <;> simp
        have hb : (decide (r = k) || decide (s = k)) = true := by
          rcases hk2 with rfl | rfl <;> simp
        rw [ha, hb] at h1'
        have hm : maj3 (fun i => decide (i = k)) = false := by fin_cases k <;> decide
        rw [hm] at h1'; cases h1'
  · rcases h3shape with ⟨p, q, hpq, h3⟩ | ⟨p, q, hpq, h3⟩
    · rcases h4cases with ⟨r, s, hrs, h4⟩ | ⟨r, s, hrs, h4⟩
      · obtain ⟨k, hk1, hk2⟩ := fin3_pair_inter p q r s hpq hrs
        have h1' := hp (fun i => decide (i ≠ k))
        rw [h3, h4] at h1'
        have ha : (decide (p ≠ k) && decide (q ≠ k)) = false := by
          rcases hk1 with rfl | rfl <;> simp
        have hb : (decide (r ≠ k) && decide (s ≠ k)) = false := by
          rcases hk2 with rfl | rfl <;> simp
        rw [ha, hb] at h1'
        have hm : maj3 (fun i => decide (i ≠ k)) = true := by fin_cases k <;> decide
        rw [hm] at h1'; cases h1'
      · obtain ⟨x, y, hx, hy, hne⟩ := maj3_nonConst r true
        have hx' : maj3 x = true := by rw [← hp x, h4 x, hx]; simp
        have hy' : maj3 y = true := by rw [← hp y, h4 y, hy]; simp
        exact hne (hx'.trans hy'.symm)
    · obtain ⟨x, y, hx, hy, hne⟩ := maj3_nonConst p true
      have hx' : maj3 x = true := by rw [← hp x, h3 x, hx]; simp
      have hy' : maj3 y = true := by rw [← hp y, h3 y, hy]; simp
      exact hne (hx'.trans hy'.symm)

theorem maj3_lower (t : ℕ) (h : HasCircuitSize 3 maj3 t) : 4 ≤ t := by
  by_contra hlt
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hlen : C.gates.length ≤ 3 := by have : C.size ≤ t := hsz; unfold Circuit.size at this; omega
  set gs := C.gates.map normGate with hgs
  have hgslen : gs.length ≤ 3 := by simp [hgs]; exact hlen
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : wval gs C.output = maj3 := by
    funext x; unfold wval; rw [hgs, wiresFrom_norm, ← hev x]; rfl
  by_cases ho3 : C.output < 3
  · exact no_nonConst_lt3 gs C.output ho3 (hevg ▸ maj3_nonConst)
  · by_cases hoge : 3 + gs.length ≤ C.output
    · have hc : wval gs C.output = fun _ => false := by funext x; exact wval_ge gs C.output hoge x
      exact not_atMostOneDep_of_nonConst (hc ▸ hevg ▸ maj3_nonConst) (atMostOneDep_const false)
    · rcases hlist : gs with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, rest⟩⟩⟩⟩
      · simp [hlist] at hoge; omega
      · have ho : C.output = 3 := by simp [hlist] at hoge; omega
        rw [hlist, ho] at hevg
        exact no_nonConst_1 g0 [] (hnok g0 (by simp [hlist])) (hevg ▸ maj3_nonConst)
      · have ho : C.output = 3 ∨ C.output = 4 := by simp [hlist] at hoge; omega
        rw [hlist] at hevg
        rcases ho with ho | ho
        · rw [ho] at hevg
          exact no_nonConst_1 g0 [g1] (hnok g0 (by simp [hlist])) (hevg ▸ maj3_nonConst)
        · rw [ho] at hevg
          exact no_nonConst_2 g0 g1 [] (hnok g0 (by simp [hlist])) (hnok g1 (by simp [hlist]))
            (hevg ▸ maj3_nonConst)
      · have ho : C.output = 3 ∨ C.output = 4 ∨ C.output = 5 := by simp [hlist] at hoge; omega
        rw [hlist] at hevg
        rcases ho with ho | ho | ho
        · rw [ho] at hevg
          exact no_nonConst_1 g0 [g1, g2] (hnok g0 (by simp [hlist])) (hevg ▸ maj3_nonConst)
        · rw [ho] at hevg
          exact no_nonConst_2 g0 g1 [g2] (hnok g0 (by simp [hlist])) (hnok g1 (by simp [hlist]))
            (hevg ▸ maj3_nonConst)
        · rw [ho] at hevg
          exact no_maj3_3 g0 g1 g2 (hnok g0 (by simp [hlist])) (hnok g1 (by simp [hlist]))
            (hnok g2 (by simp [hlist])) hevg
      · simp [hlist] at hgslen; omega

def fTarget (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) ||
    (x 0 && x 8) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8)

def g1 : (Fin 5 → Bool) → Bool := ext (by omega : 2 < 3) maj3
def g2 : (Fin 7 → Bool) → Bool := ext (by omega : 2 < 5) g1
def g3 : (Fin 9 → Bool) → Bool := ext (by omega : 2 < 7) g2

def perm9 : Fin 9 → Fin 9
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 7
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 8
  | ⟨6, _⟩ => 6
  | ⟨7, _⟩ => 4
  | ⟨8, _⟩ => 2

theorem target_perm_eq (y : Fin 9 → Bool) :
    fTarget (fun i => y (perm9 i)) = g3 y := by
  simp only [fTarget, g3, g2, g1, ext, maj3, perm9]
  change ((y 0 && y 1) || (y 7 && y 8) || (y 5 && y 6) || (y 3 && y 4) ||
      (y 0 && y 2) || (y 7 && y 2) || (y 5 && y 2) || (y 3 && y 2) || (y 1 && y 2)) =
    ((((((y 0 && y 1) || (y 0 && y 2) || (y 1 && y 2)) || (y 3 && y 4) || (y 3 && y 2)) ||
      (y 5 && y 6) || (y 5 && y 2)) || (y 7 && y 8)) || (y 7 && y 2))
  generalize (y 0 && y 1) = a0
  generalize (y 0 && y 2) = a1
  generalize (y 1 && y 2) = a2
  generalize (y 3 && y 4) = a3
  generalize (y 3 && y 2) = a4
  generalize (y 5 && y 6) = a5
  generalize (y 5 && y 2) = a6
  generalize (y 7 && y 8) = a7
  generalize (y 7 && y 2) = a8
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;>
    cases a5 <;> cases a6 <;> cases a7 <;> cases a8 <;> rfl

theorem main : ∀ t : ℕ, HasCircuitSize 9 fTarget t → 13 ≤ t := by
  intro t ht
  have h9 : HasCircuitSize 9 g3 t := by
    have hre := hasCircuitSize_reindex perm9 fTarget ht
    obtain ⟨C, ok, hsz, hev⟩ := hre
    exact ⟨C, ok, hsz, fun y => by have := hev y; dsimp only at this; rw [this, target_perm_eq y]⟩
  have hm0 : maj3 (fun _ => false) = false := by decide
  have hmz : maj3 (fun i => decide (i.val = 0 ∨ i.val = 1)) = true := by decide
  have hm2 : maj3 (fun i => decide (i.val = 2)) = false := by decide
  have hg1_0 : g1 (fun _ => false) = false := by decide
  have hg1_z : g1 (fun i => decide (i.val = 0 ∨ i.val = 1)) = true := by decide
  have hg1_2 : g1 (fun i => decide (i.val = 2)) = false := by decide
  have hg2_0 : g2 (fun _ => false) = false := by decide
  have hg2_z : g2 (fun i => decide (i.val = 0 ∨ i.val = 1)) = true := by decide
  have hg2_2 : g2 (fun i => decide (i.val = 2)) = false := by decide
  obtain ⟨t2, ht2, h7⟩ := elim_pendant (by omega : 2 < 7) g2 hg2_0 ⟨_, hg2_z⟩ hg2_2 h9
  obtain ⟨t1, ht1, h5⟩ := elim_pendant (by omega : 2 < 5) g1 hg1_0 ⟨_, hg1_z⟩ hg1_2 h7
  obtain ⟨t0, ht0, h3⟩ := elim_pendant (by omega : 2 < 3) maj3 hm0 ⟨_, hmz⟩ hm2 h5
  have h4 := maj3_lower t0 h3
  omega

end PEqualNP.Outside.L_meta_9349

theorem PEqualNP.Outside.L_meta_9349 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 0 && x 8) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 4 && x 8)) t → 13 ≤ t := by
  exact PEqualNP.Outside.L_meta_9349.main
