import Mathlib
import PEqualNP.Defs

-- The NatRun certificate engine is copied from L-meta-10450
-- (from L-meta-927 via L-meta-9142, Apache-2.0); the tables for this function were generated for this step.
-- Pendant-arm argument adapted from L-meta-9324 and L-meta-9129.
namespace PEqualNP.Outside.L_meta_15853

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool


def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_split (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_split gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_split gs w
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
    obtain ⟨t, ht, _⟩ := wiresFrom_split r.1.toList w'
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

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
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

def hk (zs : List Nat) : Nat := hz zs % 2305843009213693951

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
    let e := fld (PT s) 32 j
    mv (mask k) (e % 4096) (StGen k xs PT d (s + 1) (e / 4096))

def Sgen (k cap : Nat) (xs : List Nat) (PT : Nat → Nat) (s j : Nat) : List Nat :=
  StGen k xs PT (cap - s) s j

def idxGen (NN HT : Nat → Nat) (s : Nat) (zs : List Nat) : Nat :=
  bsr (HT s) 64 (hk zs) 17 0 (NN s)

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


def fT : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004178600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def rowsT : List ℕ := [1, 1, 1, 1, 2, 4, 6, 6, 6, 8, 10, 10, 10, 12, 12, 16, 18, 18, 20, 22, 22, 22, 24, 24, 28, 28, 33, 33, 33, 33, 34, 34, 36, 36, 40, 42, 42, 42, 44, 44, 48, 50, 50, 50, 52, 52, 56, 56, 60, 60, 3, 5, 9, 17, 3, 5, 7, 14, 38, 9, 11, 14, 26, 13, 14, 17, 19, 26, 21, 23, 30, 54, 25, 26, 29, 30, 35, 37, 41, 49, 35, 38, 37, 38, 41, 43, 46, 58, 45, 46, 49, 51, 54, 58, 53, 54, 57, 58, 61, 62]
def xsT : List ℕ := [0x54d35f53699fc00003c00000f, 0xabaeb1aed77440e38c03b1dd0, 0xcd34e2cf1a78b30c3033c61e0, 0xf23f04f49fa13c0fc03c07e00, 0xffc808ffe4023ff0003ff8000, 0xffffff0800403fffffc000000]
def NNT : ℕ → ℕ
  | 3 => 75
  | 4 => 397
  | 5 => 1081
  | 6 => 776
  | 7 => 54
  | 8 => 1
  | _ => 0
def HTT : ℕ → ℕ
  | 3 => 0x1fda323bdfa980871f9bb0a93f31495e1f3e2184b9b8bf131f0de459360453c21ecb2fbde954a8c91ce977194cc3462d1cbf555f829fcc5f1c5aad9c7c6f97df1b60d9270b04c3ff1b109fb4721322821b06917103b273f11b047cc15fd004131ad41561be967ee21a79716d5e82a533193d3222d2c3b01d186b2b9021bccebd183e7dba191f3603175fb6563333f87a16f16f9e25b9c7da16307ebd2054f5d116007496e29f724c15fdfd3488183df015e05bcf3a8b6806158d4fa6fadb1eb8141e0df17319462c13d9e32a5164ebeb130ac3ab68010521126ce3db500b9a681254a8dccb1ff1f811443981f5d6446f10d43e3b2ee3d0e710a60498651f2e600f179be7717bca900edd4d81e6b0c3ae0ecc87c003e274b90e26acdbd5e8bd620e091a609fe1a4890df838b25d2d06c80d9e888052c30af90d7a50e3cf8df63b0d36e4a9383900290d03bcab6cd397140c7a7e1e8fe984830bf9fe6ce26c74970baedfa7cb7276b60ad77c10977a1d7c0a23eab433edd23f0a09acb70ab9b71809e4ce06359b64cb09d49fe22c7abcc508a858afe0689379087f3f9175bcebd408198f331014e52b075421ace303c0c40665a7d231c2cf9406375f08ddbc66b3063140a532b754fd05e91c303b1019ba05978daa4c2a1af905568e4af90fded4051a594d26759f5e0440c27e2be8ab2603ab9ec699c5df3e033925446befd514028a7a7c0ca2e8a50242738f3c3f63a1023b6dab11c9e4d9022e4d2470ea10260183e41f979ee7bd0175c07dcd00ea83016d8b7afca698b60132544335abf471012ea02ce4d4653500b59835f3a26413003637ae3a603c54
  | 4 => 0x1feb0138f5c3c8bf1fe6dd3a419ccdc21fe6ae09cba100281fe35bbbcfa5d3301fdf0f8c8fd654731fca925fda93cdc51fb5bb2649dff9ec1fa4f5646711aaf71f9fa5ec0f4393d61f872f98497cbf2f1f5e937f456fb8221f5bc085895ff67d1f549c5b530324f01f43582178775a921ece04492c14c6a71ec111fb563c9d471eb5340eb6626d661eb07d86ae38fdac1ea5fb9f86def7441e5e9cb2513a61631e52be8832bd2c791e1bd0a8bea923171e143d7215b668451e1309ce2f426e521dff538cb50d4e251ddc2a4fd002cd521dc84a881904a55b1db2001363474c631db1da25d40cefb61d97af3e3e4846fd1d584c46f3b94b341d57a07269cc93981d52ebc2f318bac11d4d6868f80011a51d4973b11ad366f81d2c077058f17f8c1d09ef37dbad44b61cf11a75e5ad0de81ce721eaa5881bf81ce4da67efa3f1cb1ce45167481d265b1cded4afb6976c221cd26c11459baad51cd24a185434d9671ccb53ded7c658151cb23603b7206a321cac001eaa4aa4cf1c874d4c2ea1acf41c66a1e642732fcb1c55ba683986c4371c54f72c7cc713241c279451a3dc654c1bfb2603f44095581bc36d2f28282b4a1bafe9b4faa953ba1ba7b6a85f4652881b9bba5f2dd267a11b70e6a79ee96c1d1b3f9b7acf7c471e1b3ca55a9df6fd091afc5858971d087d1ae21a5b6de8ed561adb1b1e3e1306941ad463258f934adc1abd3baa98ca9b091aad0d868fa9f3031a9003216073b0321a861b898223bcb21a51a66108981f111a4a0421c3f5d5eb1a38aba2854a597f1a3800442c721b831a305270df3dcd291a2983417ebda0d11a22998675f16be51a1dc27f7ecb44901a0c0552f34ad5361a00300448c42bb719d42091d9090bb719b3916c00622e5a19a936c75c1e6d35199dbae24df9c989199b113225de288c198fc869f914f3731971668778707d6919517fb237500ae5192dfa4ce11b8757190fdbc0bd18e7f819074a5244eaeebd18f1fcd773441b6918b4b41dd3f4fb90189e806eb82e5e45186788d7598b944b184aea97d0dcd2741840b6f278976afa18313d65cdf8472417baa26eed87ea1817866039e60f0ae81746396f0176e60b173e157694f205d2173db161ea1ec39c173702c8f776c5aa173569491116a9e5172bf04ed8b07d21170fccad40eb9cf11709ae4995e68b3b16f592e786f9289516f4f8b77a0db32716e4671243e2fc7116c189d49e3f4ff816b3decd3daaba5d16ac632873012619166ffb4eaf5951371666f9ddff8091c4165462030058544f16123814129cf732160dfa10f9b11a0416084d462875303f16000f7fff688f1015f2c6f189a4d59c15dc8418983a44a5159a21135fce186c158efb3600a767d51574fecafb818732155fadeead215a6c15429e1663ccaf96151d9289eee29915151930228f17e1641517c7441781807c14fdf535cec36c5414ebfd2e49bfb92414e94271047cc4db14c306d89a7aefff14b0f8ce51cb03c01480e8d2b027af76147e4e2665f5f8051477600b3a6630cd147655351e9f7302146f01d7f3ea2e341466f49d30c0fcf814487bdfd65cdcd01447a9b7bfc03923141d1e2247e520f7140cefab1ca363ff140a46cf6245bbf813eb2e057ce99b0913d17c6bfcceaae2139b2c8356e33cbc1366f6273278ee9e1362e8206fd21ee31345ee0036614768132650b738672b8c131ebd594e1dc4a21317545eceee9d3d1309e5454c19ac7c12f2610146cea52512e6901b808f6a6012dff541b91e59ea12c96d976f6f534d12c4fd862fcfb9b3128fd2677189a618125c51c3face1dfb124e2e22303020c1122575967ebdde921221f21cab021bff1210c64767ebefdb12070dd148039b7311f1e5eb0057d3f011ea4fe3a5d280ab11ea20040cf99e6c11e031d3e3f2a0e811ad161ed5ec4890118e05da56d19a51118dccc93d501fc81183a5618469eb61117c99d12e4b1455116c99b79f725dca11604b0f17116de1114a7a156cd21b38112cf7f9094eb78c111c24f52ceb4085110ef47d948c3bbc110ea5529d8f729210ea411b04c86d0e109b7133bace8af2108ec7bb9a8f7bd4107dcd55c910634d107cfc587645f44610776d20a4d1e78110741e4da2607f9d106566f2f28393be10545994d6c0f39a10452187fa2ebb871034adb1e6493263101cfca666bd0133100a09b14ecd33310fe4d556e5929d210fdd4d51f38ad3cd0fcc2a39c6e01b6a0fc617e8065a96cc0fbdd1cb409395470f9353d254c9f0620f4a0e63d1f38b790f07bfee6f9b19780f01bbf51428ca1c0ecae95bc48fe04e0ebc5c71886c0fe70eba544b510d57060e9eacab6b41d8690e69b9b3695a61b20e5adb5181ff91650e3e07a26c87027e0e0d5735e1bdb8c70e03f5a5c10226130dfe536ad93c44e50dcf4d608507bfa10dcb531a9cc1a3af0daa1b795a86ea210d97c303e5cf029e0d7af9c340816eeb0d7a50e3cf8df63b0d71732e7279cb370d51d4cba2c6d1fc0d46b0d85504c1760d3df7f43d99e6a70d331b40df9ece1e0d244ac23ab55b570d1cd39e0a19edbb0d167f39310291d60cf85d3843c4ba2a0cd81c5425fd29d70cd41170c5acaa1f0ccf6e8ec7a613ef0cc9e36b20b4da890cc4b3e5bf44cd820c7bc7df32f4c6200c76cb648c5474580c5dd73188c929230c164316c54d5ecc0bf5063b8dddd9f40be72652dfbf055b0bdcea65c2ff3a520bd147df888c07b60bceeff649eae3650bc07f6b317968f30bac830621c5b5210ba8085c2fca0ec60b9fed9d3d06902e0b8dc50929d2280c0b55fc222a2558170b3a59f96d10599d0b353728629b46420b04f9fcdee6daf10acf917504f758d80ac2456192372ff80ab52a4fdeec57ef0aaa4d693bf3f26a0a8208926d647c080a57ab1dd4552cd00a44c98c85b09b510a3640a97688e8c10a33c9d8b339066c0a23217701789fbe09fcc8d32a7a567209fb7f19fcdb835809f84ad823aa898709ef4b1c4ed4e7f409d49fe22c7abcc509b1b39db430dd6b0957945ade35080b0943993484ec04fc0938623700f125a20916eb5e7c4e6c4209057ca2e588d4dd08fa19a0c286805508e91cf36345b92008e625cf80d534e508d486d0d03629b108cf6dda60d5df1b08c210684e33decb087dfb0452b147d60870b70ef4ce9b45086af5f47c2174c008668291278458e10865bcbb22380a2208582f0f02427c1d084c8edc7d240f38082d8ba4b387ce7f0824fbe35faaafbe08198f331014e52b080516c52d2ec9ad080454e8103cdb2307d16d6b5d2b8ff10793fafe57fd06cd0792ff700ba324990788561188b08e10076efb0a807ac82b076388622b2fbf790751937da259ad4b07231be7ce1a1cf20708ec6183842c100707b5581af5a9b1070515072a00853406ebc5926095a7b006d8e23b45cea88b06d66ad8eb47742f06cb2b056779061106b5816605d44dbc06a506ac2a55fd3706a43e0817be58ff067714418e79ab120665bd4b5e0a54f7063244a102e54a620631e7046df14b550630a9a41a8160d70603b8e45ab6c5f005f4b6e90dc7f37105e366e84f86239f05daf06f87febb2a05ba8ce1ec8e9a3c05798c436ada4a66055c1346433af3120549cc26e470fb7605498bb87c7ae15a0545b51d2eed0e58051baa5172dddb5e050064d4beae8c9704f052371829130804f01d9b4add038d04d7e2b3524fb15404cf5fffa97f23d604c80d1ed3860a4304c3b48b5bee59a604bbeb0a191d987104aba0b44236c70304a2330fc833fe6504824b9aebefb06404652df462cc3aef045252dc65db516f042dd9090f05baf404253aeb972785e3040d5ba8fb748f9103fbcd0f84ded28503f720ba07d5fc5403e3314fcb303b6003ddc19f5f225c4203bf1bcf4cfcc93803a5eac010e7787c0363812597d31aa40356cbf9dc167fa9034ac45308586dd50345517fb33ad0a7033bd3bf196976d5032d16812e4f283702f849c29f59505002d4a4f9464b14d002b5fe7cc87a7d500291b6d2fecb0a1b0287b36e4143c06302816ddbf9a3b334026fb7e31ad4cfe10266ddcbb8d052a70266c2fcf94fd6be025e8bf827da46fa025b0e1aa51296d2022e31fde9eeaae1022c3cb6ed4760ee02279460c9377d000224c2ec2ce014b4021dbe27d60921bd020f2a9a9746005f01f512d830fac51f01f29bc73aa1f85501f253d24c7e453001f1ba2434956afe01d77172e36def3501cdb3eec9f40e03019244a8f9ceffe6015ab3d31b9b53210144ee736f3af23d013b56937c0dc0b1012ea02ce4d465350127983a02a240cb0105d24f2b9f803700fddacf6212890300f64b9c5c8ecf0700e866e0c06143c100e46b7f935ab9e900d9f3860bbaa7f800b1dc5146b1cf7e007df7759ba808c80072a94b8c4f7cc7005f641a220a9912004f41d5e0f7faa0004c682c828c70860043bcdc2f78f6c50027b5d1782c0082
  | 5 => 0x1ff466317678673d1feadca3739094031fe5f931d6ef11a01fe1d52312f51a481fde69a747eb701b1fdd181803da27e61fc8073bee5661361fb766ae4ef656d71fb3cced5756b18d1fa90287096c8f2c1fa87802f47d5c0e1fa56ba528849d2f1f944ccb5f7d1b201f8fd431c82bbcce1f771a4fce710ea71f617745bfb234c41f5d82b2e182674f1f3348f5e52ec7a31f2976a98eb42d831f24859c1c78afe91f1e2c04debeba721f167546cfb638bc1f16398192193ad61f0e6a0277d1246b1f0784a1358b56bb1f00fae8f4fc33aa1ee5c4da44ecef051edfddfa677ee94f1edda5bf2971f18e1edba0b434f83bce1ed7d48d39a607261ed75a85bd7069e01ed6c10f3c6b7b231ecf5d3e89fae3a31ec1e3473fdc99001ebef6306b8113241ebc1329d8b240e11eba3327ec19313c1eada5d16f3b8b6e1eab8d00dc65f5ea1ea8d4f5cb7640851ea88604bc995ab81ea3c0befff0d9ed1e9fbe4b6d12e08b1e9fa0ee25c49ccc1e9cf620ac8ebe4c1e8cc48272bd62b11e8c33c56f4fb78e1e82891dbdb6205f1e8053048fffb8f21e7edb8c87202dfc1e75065e027a41ed1e74a9187bfb754a1e72eb3ece5b9d181e66ce23f015d53f1e65993960f23fb91e60a705dc4a50101e5c2938980104531e56137cdda211261e5487570afe0f061e545b7a0b4e558c1e536767a3b0a5291e52be8832bd2c791e47b3dd9585bac41e46e5b7baf2b5771e44d45801210c1b1e31dac35998583a1e20e8d4d684441e1e20b9efe095025b1e1c8b3a27a065c01e1aee9829610dd11e089c5ef99b470d1dff538cb50d4e251df541426d4923f91df357aeafc8906a1deeecdd9431c8141de165874eb507d91de135a7b5dc259a1dd7086719c3cf581dd0cadca6f3f0681dc84a881904a55b1dc49bb03dda92ab1db136ef59073c7e1db0921d061414cd1db0821510249ec71dac7f1528dbe05d1da2babb39d4d0d01d992455f1ad45221d98ce3412aaf7521d970c63b7c11fd41d95dad1f748c8451d81c3394e7f57531d70753b3ce92a761d6cd3ecbf7afda01d539546f44a60c41d4cdbc629e753ce1d47a7bf67d338d61d44a1282c045c9f1d3644d5ebf85f611d30da5fae3948d51d2b876772988af41d1b8634bde3705d1d1a67caac8daf111d1863747e0ad46d1d14b6d4bad788cf1d10dc2ac9b3655f1cfccdb490ed58451ceeb0bb287c950a1cea07449c0e03e41ce02c01707ec4c11cd5920f18ea5eec1cce1d209a4094a41cc1d1419881967b1cbf93f742ee3b991ca601c5a2fed2431c9bf58962000c151c9653beda6631db1c8a546ad9a23ded1c8688b72d6328691c810e3bfd2c74651c80760092f945041c781c695e31d66f1c781009a0a4a7f61c7389556eaccffb1c70d684681eec3d1c6f259826ee92da1c6c3aa4ac4782311c6bcb41c3eb3ab71c6976c2ed65c3cf1c5a9b1221a241ba1c55ba683986c4371c556128dcb1a3601c36a6497aa9b7ba1c35f4a4e265e69f1c31c87478fe92911c2fb098375af3701c2e69c68d548e551c19533b2e5ae8d91c12c79dd03f8fdb1c0f705f1c78c0ec1c0bcb58d6ccbf531c03736b1d31fff01c02a0828b809a7e1bfc36ff2ab6c0a21bfbfe55d0225a871bf88a6e56348f4b1befe448e6a1e2fa1bee81b39a6934461bed49d3310350581bdf6667ed16481f1bd4c4fc873068031bc33fdd6fc2a2981bbea2ddb62acd951bb5ca8dccdaeac91bb521c1411845fa1bb4e76ee9761c751bb37d6c4dec68111ba36e542c1ddf521ba28655ffe34eda1ba2460ef303e8f11b67e0941de4e5b31b4c2e0756b700cc1b4a90d7da5157d41b4120cd7fd218891b318b8b7f5bcb781b3071837c78ea111b2f501221734a541b298ec70e0b2fd41b1b7665aff08f531b1726a1000e16d91b151fcb470f08fc1b0a0f19b22752941afed592187da0a61af79e740a7f74471af2a0b16166f0d31ae70a8be25c7dfd1ae54cdb8fdf24a11adc206bf42ded7b1ad381e65ba854981ad00236b6db2b281ac7b8c0b2041e321ac77d57714117951aad0d868fa9f3031a9a9456acd48f721a9a193c7e21ac6e1a99fa3c64a11fb11a95c24f14245f971a8aa75333118e121a8a2142176013a91a7c208940770fb01a77c10cb1ce09741a64cef167e5ad621a55ac4c613755f11a51f0f52ae218931a2b45d5350e11e01a10cfdb64205be01a10b5bec4210c0c1a0781cce8c4498f19f34c61d1d04fe519e483b025cd782319df67d4659b7c5819ddea4748b80b1b19d72751e54c4d6719c268be45a42add19be9373e4046b2319be50c331956d1319b655aa33f267b119ae1593e0719a1d19a1311d0369714f199cd9c98a4cea1f1991ecb73866598919917969e8df6f021986c17fd8e39e661971668778707d69196d64107950475d195cbe1f7c8630791959264be01bf00a195668a8b5e07e1419551598c2ce2b19195434bc4dc49250194d48aa8fad304e1943c96c7d22071919436398df50aafe193dc67bfde748a4193b5b08cdd355f2193ae0111ad7342d1937602e67d355d0193587dc0da260581931d453144fedd719309cb36571b25b1924fc80e0534576191beb880b33b5de1913e941b2fc74e9190d61af2818d2b3190c246f2498f8f31905f94916b704bd18faf825983fae6e18f893eed775ee7218f1fcd773441b6918ef571ec24f993e18e7792810fd552b18dcc24293e19dd718cc4b6179839cbf18b727dec69e3e5518b39385e0431a9718afad1c8ed56f1518af2fea319e448118a628b34bb92b3d18a2900f26f6342f1892a4582483bb6118916066a0bcc6db188331ee74c580431880309adb34fcaa187f1c694740a76e1874435faf37f1391872baeea9b3e7d8186de1083536fb86186b6d146ed25ad71860c3b5ebdfc44e1854ecd531abb0511854dcfcef93424818543a422876c1f61853a85ca794ae25184768aee3a9fe691845042b32e7b87e183ad5e3787001101839333d0f5323521837199a389f2d8a1835c2195eaf3e8e182a01220588e3891829c1afe49a7a8118229158a0050408180d58ba6e2fe5fa17f8378f758c8e2617ecb35c7fd9ef7f17e4251874f51bd217dd82ab8d2fbb7217da6fe8095a38de17d64fb5d2273d3017c9c6e0979d8ab117c487b37c518d2817b7950eda5bf02117b724da983e8ce417a8cd771e9a4d5617a398a9caa83c4f17a1d00100fd5adf17a16c92283bc0f3178def0a690383fa17879a6580bc8b581784daacd2b4af3a1780f0fefda283af177cabac7aed8f3d177c93a41364bf42177b54dbb41de103177796dedfa17290176564fe024755f017620461817dbb05175ffd3393ce4b1a175f8211ade8735d175b702105937aec17534fe4e2923329174ed15e50b81ef6174d11c5d307df45174013f22cf0e00b173e850315f7efb01736208b7c98743e1717fc7e999539df1711c002bff113f5170b37f9e8865004170917487db097151707dbdb498b032b170084348776869816fe36ea9de8058e16f9b42097b118aa16f6336cf68c385c16e2f1b9516f6dbf16dfe116591ba9d316dc2688bde5fc2e16d81aa359206b9616d2740b5369d75a16d0f4c5f476c27916c07b66348528a016b35e13eb2df16816b1ee905c9ce4dc16a1630ce4d679981693545a5a1565231692fa864fbdd07a168c2093a35716fe167b1262e08ca57316736622d1afb92216725d70bbff7139166f85a3b31902ff1663bf95f2a95c0c165b1b2a0165dc4d1654283c811bbf711651f9e7ce0980a4164eeff1d1bd9fc716487b741b930e3b16449a6b85bb4ca6163fa479b24f57ca16387f5aa7e87f2b161e22c1921c4496161a371aaa5b26ec161874b5aa7c7dc416137eb141d4dd201610bc01e9c6c95f160d309563c54b00160a2f6cd9aa1d3b15fba8a6287824e715f859a32a7d92ce15f417f5d60d119c15f3de76d35cdda015e660bff7b76f2215e5ad44e467490215de6b59463fa60e15d8d27921ddc2d515d7750ad202dc5415c8bfdb7b58494615c88b3fae0c39cb15c404a9bec2af4a15c1eff8e59a078215bf7c4ecf174a7f15b5cc31d5c8c19715a8c9415d13649915a07ac336b54081159fac23d2560c5f159e9f2f889899cf159b1ae83e6f9ed71595e723c8236148159458ae7c4cceaf159348e2e447124315911f6115461cca158f7e52c7df6d40158efb3600a767d5158cccabd4aec3cb15840e58a565fd41157e80d2b5edd429157aa0b42b6334a31564955d23e4add0155a33cbdd53b14c154e5e7908253bb71546d24bd9af2d891540ef5f85504af6153c6b093402d700153ba74135834b7d152ac080c90a87ad1514cc8b1114a19e1510d1491217663d150646ad7234f13214fda88ffa56bc2114faba52bfcf595814f6f5b4a633bf8314e88b9ef3e6aef014e1c388dafaa39714c6837e09b8664914b62f43c251928014b5943d55eb961514b4f3d2baaf6ad314978973b02bff7614970f672d572ef614935bde3404bc75148adda4ca91bd49147e58647416aeba147ae25c027015eb14798b0287e8c2951470bd1f916a71b0146bf609b725824a14649c8a11a84c2614620b982503fbee145cd25ecb1a9150145c7fb0b7f47d0c1456935f8477ac0c145484a22c6f48f7142857e3c307e65514269fee170a43251424a1485c6a55ad141d1e2247e520f7141c1187088d36ec14136e97a2625c281403696c50f28e2413e006b8d456695113dbce5928a75a9313d0b7670288868e13c0d012845bead213bc3a3a371f098413b93a8fb825cd3813b4e31a4f9f1c7e13a38862edfd06831396e4e35e03ea5b138b10a200df8dfb13805280f6847940137f6bb53193153e137af1b71b3c094b136f788c58830d2213683b9dd9b9310713602112a472f6a1135c4d71185ed1e01359db805cd2e972134c4df3a5d644341348a9214b3c3479134179546706e492133f30a15c7f0cfc133a4370d84e31cf1336f99c8b097d381329107a25ba584f13251536f1b49a40131ebd594e1dc4a2131a318b76fca4201304aa5b5076972c130002052c66b33e12fd3090900f4af212f62bcc393857fb12f150b51a5d8b0512e9a9fa7c0f554012d5fb4fb834683112d5ad128aba6f8312d5a17317f2ac3e12cf6780431a625412cd807c9429fb5d12c5833fd635d74a12b4d770024701c7129b53abc0a0e02d129601fa4afb38cf128ddce82bf1f2cb12877b3399c9407b12791f9f3d21a8e5126eabe507db6406126e29e5375c3240126bb7cc1f7fd0dd126ab24d5cfe3624126347984353f7e812505ec8ab1b0390124d9943561e93cc124cb31449599df812426fa3b5cc9c741235ae7a9e388d1a123321777eca895f122b7eb143a727f312202581a738bd4e121e5b1b507a7bda121cf1ee8697385e1213c437df3cf6ef1210c64767ebefdb12070dd148039b731200543ef78ddb1d11face8803994d1e11f4dbe579ca33c111d2061330e1425811ba2558ce25064f11b8e14daf9128c4118b3b3f15636db2118383a9993f8529117f815b56403a781170a1e713bcd194116ccbe9764ad13a1163a4a86050123e115916ea274ab50a1156651347e1c780114fcaee8f5d780c11412945253b63b31138cf09133445e81137d1be8539cf50112e5314a5dc95251127af7a442730de1125cfb0efc883e01124d5d0e5bba6c4112337b670e25b0511225019ca21621e11201ada93782877111c2a8092a82d03110f26b54b47c18211002375db5b36c010fc8fad02bb8d4410fad11d91a0de8f10f77a78679113c510e767dac10b9a3610e5bf4fa9c5c23310cc6830ee233b3910c1fe0e1fa768c510bf4adea4cc040110bf22c27c68917110bd4cab5c4c633e10bbc96032d5096f10baca2f04d0e0d410b77d30f3058ab210a56b27f50f083410a300043dc3040410a17181b02d22fd109c87eeb1a25b4f109948b3711685931073c1f4b4f581d410700fb2139b71ef106bdfe3271c25ad106459d679c9142f106177311e6f2eee10605660abaeeca4105f9d3cacabf56e1051f47c3cddcc2610468023559f042e103f87e0aa76d82110342e29ec8f2cbc1030614238aa3473102e08789d055c0f102d09ffb6325b2f1027cec5a88b456a1024eeacb7e84222101e4db4668edd0b101c508f400a0d11101744e0c050a77310171bc875a064b310161c3793482fd40fee365db0b883820fe361d58ba0eeed0fc975bb422827130fc7bac0d04aba840faee5435632224f0fab98ee8bf41ef80f9d0c2bcee42f630f997f9fb96bd3860f88eb2b116833eb0f7dbaf28e3b5ff00f768cabefdf712b0f64f0f770a75cc20f5257f6a51ed6e00f41d9f6b13af5030f25388a6e8cb5eb0f1e945662ec86ce0f1c00b414296b3d0f0aa80d9f98f2f60f0a178ef253b7cc0f073694525ba6940effea359dc2b94b0efdad84be5e15c50efafc4d7a99a6d90efa7e72792c7f9a0ef2ffadcb6d34100eecab1678e59e840ee18738f57c32180ed7c1493d40c7310ed7c131183c84640ec918367fc9578f0ec67e666faf15800ec5322ed1bd6ecf0ec2f388ec9de2f00ebdd4fc3813a07e0eb6b321be07349d0eadd57ec58b12d20ea274033f7e1e900ea0b82c7c33db9a0e8a6db7c67682a20e7ca9ea4b0884490e701ce2a1777d3c0e5dd8a0a2325dec0e5adb5181ff91650e5a891e4bd9695b0e5223be4df51e000e4d4d30fe83fd460e45a87ceeb49f9c0e40d0bbb006b09c0e3dfa70f288e44d0e30b9eb56e881730e300e16ccfbc9d70e2b23500107b8cc0e25d60d5b2f47e40e23525a9629e81c0e21e1557e029d370e03493224f755810e0179344dc722080df89e76e79becce0df789856ab0076d0df55931582b80c20df0e1e028c6ca4e0def9ac1b9182cc40dee602f0301b8650de9b16ae3847f830de902beb97e0f190de436401c6ec4dd0de38d205afc539b0de25cdc3edc7af50ddb9d7c00ae93a00dc7adc204832bb20dc4cf236308c6860dc4c99272d695310dbf24da25528c120dbe0cf9b6722bf60dbd480c52d3280a0db8dfad80274fe50db7425419c6a2610dafbaabf0d26e750dabed6804c9440b0d8d063c635bf6910d8c8813e0b70e400d8b07322362e82e0d8aa3a81a4fa0710d7e7979a64c06fc0d7a50e3cf8df63b0d732d1133c241d40d6c24938b0773e30d676ebf479d41630d5b7df475f625ec0d57b5b328ca5cdc0d51f9ff95e47fd60d491f38cd9d7ed20d475cae3f1ccff50d3de37826d5165e0d2d64d0dff649630d24fdb9bb0735ca0d2457a6ff6a56f20d0001f6070b9b8b0cffbe5b6f68433b0cf4f0730af510310ce925aa2ffd13e80ce15783752a90e40cdb81233c3d41170cdabd111f061c220cd1352df11b6add0ccb246e017e3cdf0cc3fd13aeaeb7970cbce1ba9af9e7860cb81a6db79a43c70cb4c9b0e3e6f6fb0ca4be1c4d434b1a0ca3b40c82fd73580ca27a3d6e4860140c8fd546b9c220e00c8ce202b5d541c60c7a98afc179769f0c74280391019de00c625ca06cb816520c60dad0ae9f0c4b0c5f6ab46353aa2a0c5e173822705be20c56d40576fe34ec0c46577989da81ce0c3ad27fd85b7df30c2d85a5b50399db0c2343a22bed83420c2075e3620274020c1ecb75210e87b00c1763f07224c24b0c1512ff012633480c0abdcb2bcfcc2d0c087fb63e6051170c072d8f67992ab70c05b1d29c08f64b0c02def4bd1073a90be75913f70b02010be733cc4e4d787e0bddf2ddea7f54f10bddc3ad748387570bc5a38df3d69c760bb044a0d28908110bacd0c9f2c2811b0ba332133705b7530b95ea1c63a4d3600b7f5ce5068e89910b78b8b42fe8e3d30b719a2c2cb79e200b7074956a00918d0b6dc487396b0aaa0b5e892de552f2f10b5bb7b948fb8aa50b55a922ee523f510b4d246cb53ccf330b478ad10a433d4b0b2fd44f95ad0db60b2e1b813b8b6e310b2c07a54d163b100b2a14056bc755500b2271c627250c2a0b1e530004d051470b111946e8798fbe0b0da66632d4cc540b0a0c2766a160fa0b08c015426d03680afca6303dfa318b0afb072ad920a2240af77ee2ac46b8fc0aef4980ea8c44f30aecfa73366e57ad0aec4b7961a5c7a60ae472f7567a0b750ad043afe6afce880acf06caa9752dd60acca3492157cc300ac9397615ea75d70ac519ecd4f74dd60ab5a8c79d701fd80a9e60ec764ce0ca0a96bd27f6c36cbb0a904a1645cbd7c90a8ef0ce12bae0cd0a8bff10639164990a8208926d647c080a81a46bbf4da3740a7c7c3d570d67440a756e82f3c7292d0a6d538a47257efd0a68360e5c4429b20a5dbb78492cb0f30a5c05fd98e14e380a5a66f74a1710000a4e8927be3987220a49d42bdb9fb3a80a4541f617980a690a29ed569a7f41240a26df4acd1c718a0a2529ce89374aa40a1e3e9670d982dc0a177588fdcd25cb0a105c635e4b80830a0bcb0a11af44f50a03983466bd8a0c09ff6b27f210ae3509f2b77dd82fdad309e955edb774481f09cfbe7a526e5b2609cba2abfaa0895e09bf602bc1e72c8a09bc10a96b8e37f909b70131196d2abc09b690782c69544b09a9e00cd13e5b6709a9203ad8437c5709a84380eda06c6b09a3b587e122231909a28deeb2aefe87098ec4e1e72ace2c098d21c2372431cf09897a31e9387c950985352f0fda2b0f0976ee131b5d94840961cae91759dc71095a26020750bb6c094f61ea9c9bd2630948333f6bdf1882093ff67bbcbaca8a093fdd9fa2eaa5b2093e8aecc43a8da8093d25072063623e0939d8266dab01a00938b97cb4b41747093179fec91275ef093090a9be9466ae092a80acb99aeb1f0924dffb2ca4c89309243b1a71faddf00923583c340c08b309160459abf1ca65091554c49de941580913a66dd150fd0f090d74f3247e12a90909ab0a31277d630904f18f6e6a0164090104db848fcbe508f2f367186db21f08e346375a1396f108de378e4e6aa32708dde888c6e402fa08dbf00b988678fa08c5b99b5e16c2e508c08b664e604c7908b40994913749be08aaa6c3ed524d7008a94ba76002f16108a3367de375dddf089c6e89daede0c2088800d40bed5e0108806ac1dec8afc4086f599562aed7df0868e07f3b22293a0864a1fc6f01d6ff085a6e459a7c6f710859af8e964accdb08582f0f02427c1d0856893ac15c4fa10853c3470338ba6e084cd00be2694b66084cbd8669a4c335084415022d4b5789083e3cc4e473529008278ee855be81870819ab3fff274d5b0818b940b6977d5b0817f8dd6b46884a08161f064d4df9db080f706d5aa5fbe9080dd6ed7445e024080b2f7277dfa5250808eba2d3d74f6c0803469e960c2da707f7b0d7f51e2b4b07f21ac952f6018307f0c6de2cf9565607eea409346b6e9f07eb898f5ae5b1e207ea851bbc60b1cc07e7bbb1e7921cf907d7a98dac5aab8707d35d5e7b9458df07cefd4aba469ad207ce008bea285ed407cd910b291dcc5707bcd4b6a71232b007b9ee0eacdc89c507b7639f395762d607b4503e405d057107a507169ae27200078c4c71a0d9f09c0788561188b08e100782cf7833019812077f5e2337df3b4e0745fe646d7ee16a073f678262afc8030730d1ec4db8d041072d22b3406600aa072ccfa763878a8e071df0748009f39706fabea59524f82006f771a78359a1fe06e9d42cfe7d272806e667b55ce0504306e0baea8ba4667e06b4f1bcfb697ae406b401e8dceb28f406b0aae706e15db306b0342b0679083c06a9c99c7750578d069f6a69e1b77880069decb501d6ed02068b3db56361c9c90673b70381f5975706728eb7c2fd4eab066fcac20a36fcb2066768da63d69e1406656dc962cd055606496cbdb96ed2250648bc04b17aa64006448818bfddec81064119c56cd85d1a0634160e5ef187ff062fc1462e2ce0ae062e2ad4410c9ace062b284a511b078e062350bb2bc2d4e4061b0bbac6fbe5d50608d022ba269bff060832000f5369e406022d6e664ccd1f05f6002e5211cf5405f034e87ab0b6bb05eacc413f62b97e05e0ef42712027c105dcf4da4a1e16f605c46ad2aceeef6305c1b01567abfb1a05a53ae9067550e5059b747cfdaa263e0594d085f6dc50b805921a5ae572af02058ea8bb913ee9cf0585e03d6129f7da0581c9d77a417a1f0576c1336aaa240c0572201b2fb4291d0562b6c0c3ef65c1055e4019181801d10553779bc3e14fe405476f7c57196473053f624193f03337053a084bf52980ca052f509185cf5140052841174c3efc5605092948e5644482050064d4beae8c9704f58bc6ab14573604ed9dbaa0d4f36604e55d4f7fd29a3e04d034bc97ac9af504cd769f0c791c7c04a9ea105ffde12104a220cb2d6478e20497e187b26bf4f00493b4236c268a3404921834de49354c048821613b9fff4e047e4e5f3ceac61d04739a27ba1272fb0472fc6dda503ff8046b17c6915bd018046935eee7df16d80468f1e546fba4b804613f0f470ec0c9044b27414e313a0f04489a8c515ffc6e0440b9e0adfbb3260437cc962179f22904372dcda328da3c042fa001474231d1042f8e0b6ae58702042baad7ddca7f7a0429a5e173d896cf041e5ba499907da7040b57f2abaec0ce0404be09032aac7d03efc203321dd37c03ea770d23a0ebb903e76ae3f62a7dd203dd08e5ce65891a03d60c04776449c703cacea5a9fddb6403bca479bf09ebd503b4304ba73e7f0403b1b812966a714703a8aa7e9c4f2d9503a1db3bd29e898c0370807705af3fb0036cb6fd979473c3036b88fb9163d5ba036a40a501729ec703683ddbf3b55b8d0361f849ac154e5e0348d913bb73fb7a033a604fed387fff0334e4e99b49277d0330665e3db3087d032fd053314bd456032c7eecb9f93114032b3cf753089414032adc1fa45b3b310325dd8e8b1e1a6a031b7599cc91586302fe4895887abce702fa5fc10e31523e02f89a3795c9241002ecc844b17649d802eca88b2fdbafc402e9e46a96c42b2702e933ebcb1b261a02e76e6252b2f7ec02e2a81e25d540f702db7cb5ecc583a002d8b59059aa529502d3f33bfa11d11602ca538f63870a2f02c28da87028d4ab02b89f784721d72702b5d100c60d082d02aaf470e68d418c02a9174d5316678402a85b54948bf35b0299bec0b88dac1a029460bb5321a109028a66f420c81f43028948c2926cb9a80287b36e4143c063028583c3391b7ecf02816ddbf9a3b334027f294af90eeb790266ddcbb8d052a7025ebfebb1629efc025e0f81a86318f3025c1305e79921a002550775917a4a94024b77a6a93adb7e0237bff9bbdaca8402320d6c7325960a022dd7f5606499a9022a8e000ecafc4e022876d2379850600226dd0cc61429cd022578e121ac8d670222e7b9d0015177021dbe27d60921bd02081c835c85126402050fb4a293a13302048be3ff873a0802011cc132c0f8ef01faaa4f9a010b8e01f72523a84b163f01ecc5408316986701e9e85ee192849401e7f01537c0b12a01d6b006487a325101c2aebf67f7a34d01abf0538be585bd01a2974749fa487c019b071f6b5119ce01959d997ea6569d018db06c65857447018ca705d9e829140176e30b9ee794870165477921e54b520144ee736f3af23d0140fb2bd59f2400013cbeb70756e2da0139b3ba0caf36c50136f65f846bd27d012f7cf3ea180f06012f7b47f540adc10122ed35e11c3fb8011f86b0dd77a5c801153df53bccdbe50111f6844c8297ad010edce7c06407ab010d1b56497868a2010b39d6467004410100c0731f41215500ec2fcbd1e4bdd800e60299f91a96c900d46d19c2b1180200c705ca5322260900c23b57d32f892800c1bd8d85e6c11c00bd42fb48c1d36000bac5eaf129754000b5baf656ba0a0c00b368057da2159000ab57349b558b1900963f6fa3c2cb860089c8a26bf3caf400882a54c950c3a300733d71677b9966006c9be2753d70e6006bc176b7f926a10067aa73ea814d64005e0a40d9a38427005bd5f9093e1b3f0057f7bbb9fdb0070053a87b537d0b43004d4387cfc968ca0049bf81a7994359003f91837f3f63ff00398daee4c1c1b10037b3245c4d737b00323d06291920620030ce466e710dfb002dfa0915559e5100266597ae0942b6001433c5f0c7a82600092550f14a9515
  | 6 => 0x1fea2ac4dee5f4c91fde69a747eb701b1fdde9bec3e10c3b1fdd71320a70c7601fcf6a403886f1cb1fcb6d522e9c6a4e1fc450b5d393e8eb1fbe3e6af570c5a71fbc1c2dd37101771fb5221e0ef673851fa176821d2bdc9c1f9cc325c141d4bd1f8e3e30917409171f7ae1a7a2ad54ce1f6d4ef0252efddb1f64449bf8b40ebf1f4ff6af1a65a57a1f4bc0eef40e27491f475891a28770691f40d136b10e5afa1f3646450561942a1f2e395bb1e61d851f25bad561b333841f1e2c04debeba721eff9fe0b7dd2e7b1eff83b11f0ab3651efbbffef9591e5a1edfbe0e792eda8a1ed9e6d8b0f658461eccaa13ea3dc69b1ec808661c4763021ec7f74814280e911ea01b6667b261f01e914d51e35686231e8cc48272bd62b11e8c33c56f4fb78e1e7d8598727a38591e727d8c4b63f48d1e66ce23f015d53f1e6573e0c68b2ccf1e64f5b843e6447e1e52be8832bd2c791e522e3b946f5f191e37f6c50346ffb01e1c756f155a78cc1e06f8c261dd2ac61df19e9cc90f49b21dd760bf231ae8fa1dd584e88edb5c661db1a917d767cc0a1db0921d061414cd1da9a2d2544aa11b1da97798bf6cd50c1da25eced409b8501d990065411f71df1d954f5efe291dc41d88e0a304afc1441d61a4a2e2ec97411d6198a9af9e0f8f1d4e5a5cf8a74b741d40cbf5e24ec62e1d32a0e00c1d0c451d3299359dde74761d277c76e78b50801d22533887eaa6061d204a2b6aea2fc21d1ec51ded09b80c1d1340243b8ab4311d0c4091c6e02b2a1cfec2daeb3abcac1cf73919843dbdee1cf6f57af972ea2d1cda124644b0d9f11cc12b5c5096b2231cbfc6b85a3a383f1cb660824dae8b2f1cb54f6a39a2032d1cae55083b5f92b11c9e426a94da19221c94e1fa5e56a50e1c810e3bfd2c74651c7f9dee6757aa6a1c75fd525037105d1c6729795b809df21c5ba910c84375d01c50234344e5047f1c35f4a4e265e69f1c2d9318e68351b31bf4075056cede731be63b23c5e4dead1bdee598fd3bb3d31bdbc93c8bb6c10e1bd4c4fc873068031bd32b1f13d88bfd1bd24878dcbc561e1bc06774321d33961bbbfb329e3cc9721bb521c1411845fa1ba7746f0ca464141b9ed4dee15d82e91b7a6db3188749781b753479be9ddeda1b7412bc4d3d4df91b715f7bec57e5261b6fbc55aaa97f631b65da823ad8e14b1b584b7a643fa49e1b56a934b38d86da1b4a9fd48770e0ab1b49236a192783c91b3d03634feda3371b31c3551fb4c30f1b08fae04cfcb8491b07cef37d51a8641aff4cef304ba7c81afd9772ec6680e21af79e740a7f74471af4c32867409cf31af2a0b16166f0d31ac3f75cbe8767a21abe3cb209a753b71abe009480e9bc2e1abb4d2e909c2e1d1aa796b42fd847851aa71ff82f6ff20e1aa61608530fa5781a99fa3c64a11fb11a97cdd0251662c81a7c208940770fb01a77c10cb1ce09741a6931d4d0896c6a1a6732864a5a046a1a63334c946c048e1a610b3c3ebf82031a60838d3697bbde1a5fb982e1cc48331a5a2c838cfdd0f61a51f0f52ae218931a4edd90ce3dfd551a3a0160bd0ca3311a359c46542c0bd71a2e6f4583ac89b61a297ed333dcdd2f1a27cf8effcb08a11a1e5ca7dd2710271a14b3307600dcd819fe9302eb59003319f844dea615f6c519f6178f9884076219da2cea69f8670819d9727fe7bf022319d405176b18c32b19d03d808d31fb8419be844f784cf1ba19b45daffbb5af3819b3b5c6b4242db719868c002adf7fca19831a7cd967cf591981b94bc332279f197eb86df904abda1971668778707d691970d07fb36a1eef195ff59900198abd195be379d403b8131958d86641f7e60219557dc4bc9943e91953455c5c258302194bde1d82e4571719475d86668eca0d1940048db0a2c7f019309cb36571b25b191330a2f71c9aa8190d61af2818d2b318f893eed775ee7218ea682e24648fe218b9cce449a8318418a60192786de4a018a482df0ad2fec118a2900f26f6342f189ac9b02bdffa861897a923f2215e7d188c9c0831995603188c36692dea01b01889040207401f1e187e6346dc22cb1c187a69ecff1935bb1872baeea9b3e7d81864c5e2866f204b1860c3b5ebdfc44e183b99d16465a88f1837199a389f2d8a182f5bcc0329ba20180fdc935b14614f1806f80dfb03dc5218059057a39536e818055d4382ce11f617ffc9f5b48ee7c017fd32095da900ba17f1ad0fac29fcdf17e2c79ee2d5586c17e197472128e2ae17d784dd6febdefb17d453a9c28054b917b1aace6499d31d1794cd6dbe4dd3dd1787e69df65570e6177884041ccfa19f17765a5965062340175fbd566140da81175a4727b2455e0d17519eb489b9f8f1174ed15e50b81ef6173d50c7ab6b8fac1734b2aa338d5a9b172d3e2a04e6161d1724207c81833522172129a914a9dc7e171cf5bd230d22bf17198769d007935817082eea915c16ec16fd921dec8004e516e0d037bfbb14f916d81aa359206b9616b5627ead4d4d3416ae021b557245c816a52a734e4f6ce51683f2d20c14b357167da88d69a48723165fd094b38aa2b51654283c811bbf71164a704bf73c2ad51632102d8210da8c162550dd944ce9e2162179cd37c1e62015f6aaf6bba7b6f115f33823b8913f6f15f225f85261addc15d8d27921ddc2d515d36734175de19415d33013d7dfe5a115c4bad7b420d32c15b6343d11614a611591c5faab7ec4ef157d4c46a5f5f7bf15763abb95b5ab761573c40713f80998157387292333db9a1571c74cf476f3e4156c21c7cf55c072155ac94890aa440615459f71baf94d181540ef5f85504af6153bb47589ad35a61539acb3aa3df7071514e7ab069acae215063c7a706a514f14ca85ff1280fefb14b4628e0b3f83ea14935bde3404bc751492ca9b6c54f7e61486cac57ac8de16147ae25c027015eb1460263733d1704d14600afc56a18308145dd24294fae858145c7fb0b7f47d0c144d48a206687d081443f69ff4930bf8142fd37adbb3214d142b484d88ff6f34142857e3c307e655142146b81ea331b8141df55b7f4dec23141b6f73915028fb1404ec911d28675213e938ff84096cf713dc5feec722254513db1fe580d1a94113c66496583241ae13c5162f930ae60213be7a1b4f25eed013bc0895d1867cfb13b3ea5a4ff4b9de138976f59cec36811383621549bc77ca138250db5211097113602112a472f6a1135eb9947d5dcf581359db805cd2e97213534a51202cdca61353349acbdecb7d134abaf183a3629f134764a977efdd11133ac1e8faecf8f8133aa00cb85198d713372d901491d53a13367d260b924f311323e54b0c6a11bc13234b45f13e7e0312fcf8cfb30668f412f654f8de02a27b12f62bcc393857fb12e7cbf21212ee0212dd7d5905c2d77112d6a02bdc081fa812d566532c3bceeb12c5b9af0346441d12c144e180f5a91f12b55356ea13ed4612991ea50162027912911cd0b9ef2878128b8af665bea6a1128656b7b8b74854127bd199a9db48c912778b2198d318df126c9d06ebe347331268a9e680900ab3125913669348966d125786ef1c76946c124bb91dc9ef8d2c12351bf22066875012202581a738bd4e1217b08d9259131c1212e4d8b4a1eeeb1212215e6fde6d03120684b84f42e6f811ff96948549252c11f7f45540a6dc0611f4dbe579ca33c111ee8d4b56e1c26d11e949e99f2d384811e74a8c23933de911e69bd601fb5f9a11e040747c1e675211dd7c07c87a9b6011a945331263a851119b823064bfb102118917840ae07c4b1185b9d5c4c861b311767fa90bb83ed6114d55956b9ca9ab1144cd4d2daf3df611433234f14eeb2a113f9413d3c5d358113677e53cd2ba651134b79ef794b43f11270a9108109f5810fed33c113878f410f8c01be15e8f1610f7a6362811ffdd10f66d5ec242b5a810eca16a53f6de6410e192f55479cb5310d7c246b56a7a1410d5c225b8bccc0410cf83c5e48c98b510a726fcdaae1bb610a579646d49e01e10a56b27f50f0834107bf3ad5ecc4d71107b5d414dd775bf1072b3ab3ac4d458106dd257098ad0031067c405901f1fed1064bbbc6f2c9a1d10622d6a3a3e574610468023559f042e1039e4ea22e16b031031f0a59f6fb242102d266ba15764c5102c634b91621f3c102b6ad653e77681101966f67813196f10171bc875a064b30ffcf3407fa7e6280ff6afeb7faf10950ff452268c09c6840ff09f100a810b090fe6d7a6db005aaa0fd37606dedb29d60fc7bac0d04aba840fc781a9b5c9c7ef0fc1adc253863eeb0f953839e0764e4a0f8e6f5af100a3470f8e5fec77fcadfc0f8cb79eff6710ed0f8912433c20e77f0f866c558e6300340f80f3a91fc890f70f7fb0d1cd961c310f7e1560c94c22350f780e9288f3d30b0f66b6134a48569f0f64f0f770a75cc20f6182a3e4493b4b0f50eb9a400774480f41885ce860ca8a0f3f3bc853450b7e0f261a6506d8febe0f21c65adc60f4e10f171c3c3d985def0f13bdaa9b7bfe9b0f0e70c21c2c7a5b0ee3597c8dc7b0000edd903d0c448f260eda2d69b8c666af0ed813f31d21a2970ed7c131183c84640eb9a34c190b5bd90eb4c7c8398c84600eb4ac6c713667de0eadd57ec58b12d20ea55991157a61b00ea3831b03aa2eb00ea0b82c7c33db9a0ea0693b6d56f5cd0e9b5c33e6782ffa0e986c2feff357d70e925745c094028c0e88efb97353d5060e7eb06fa0c7177b0e6d90aa15cd91bb0e53639c1c68139c0e3ce0da5f30e2c00e1d0ecc8f3392de0e14ea117c3197df0e0e5c7cdaa867f30e05f96b798d9d0d0e0252367d095a6a0dfe8bc14f8ac3ee0df789856ab0076d0dda3c2d703c55cd0dd623a26707c40e0dca298fc9b6dc3e0dc4cf236308c6860da548ccd9bed8c80da1e4778513d3790d8e8d802a3f69c70d8d063c635bf6910d7e7979a64c06fc0d7c0a6879c1c79b0d7598575aa994000d6ed437777fb2b30d611e1fa4fdf3ca0d6049731b862d2b0d5f228d8b1d6b610d5b7df475f625ec0d597be0605baaa40d48236121b02e380d4438e6271a70f60d41500455b0a14b0d3810c37b2ab4a90d1e4f96fec998d00d1ab63dbec82e180d10ca9253cc3bd30d0c3daa185988f30d07b061c093842a0cff124448b54f190cf24cfa3d4b161a0cf08e49e07db5b10ce4920862646a310ce456fa4aa1522f0cdb0e26eeafd0bd0cd0f812b963c58a0cc5b777943286970cb026ed52b459d70c8d55134ca552b40c88f76f7b78ab440c7b09cb446ff9fa0c6f300b236f4dc90c6373b9d614a7050c61acf59e7db65b0c5e173822705be20c5a65677287eea70c3bbf7139426e300c2b19bdc23517fd0c249babb9e6370b0c239d584bf725b50c1ec6f4de6cb4f30c14e4d0ad7203130c12718308e0f9910c031b658a8ef51b0bf3e40a131fc5920bdce4cc6d8c445d0bcb0e55c49627120bc65e2f0e0de7c50bb48e10575d23ba0baed603389a491f0b95044ec47e8ee40b826c73c556516f0b79ee059a27aa3b0b6e2ff3775395d60b6807443a81cac10b45981853f623680b41b6c0f2ee04c40b409a55aadd9ff40b4050ca8de879640b3d2ffa531899300b376d5f90fcb5110b32cbe052be10ed0b2a5e998e114ed20b0fd6d080b089b70b06140f9ed52a240b008592988a2e140affb3c7f2fb5cd30afca6303dfa318b0aee00e67d7096c90ae7f3e0ae17ced20adfef714bf37fce0ad61027b193e5d90ad5b0f363cca6ec0ad49234451b91de0aca1a2d89edbed10a9fea997458c7b40a9ad662a8d3611c0a799ec16698a78e0a754535bb30cd390a70aa391e3209760a70a88728caacb60a6d538a47257efd0a6a1df7f2fb68ac0a6413cec27c80570a5c05fd98e14e380a49d42bdb9fb3a80a45d1b4dc7f7d9c0a44e107ad7c7e9e0a2dc82a7f9527080a2cf61e2e9b43960a131197f548d2e30a0c870b999cef960a050aa6235efd4e09f3ded0e048d12a09ec81d0c47b1c5609ec56e6162bab2809c3568bda108f1609c0ca5176a1c2f009bf602bc1e72c8a09b51273175551c20998103789aaa4870994ff0df5befa1809860b7321a2140b097e9657aee8617c097cf8f78d5f7bec097ae5025d1031cf0976719c9be6667d0963d9c19cbe29080963d0169455b16b095b5b53718f81d4095a26020750bb6c094b28930ce31e170949ec18d0f49af1093d25072063623e092d5a7994dae690092cce2f2029809e0929192e9285c3d6091d9434e106bffb091d71cf9616eebd091047d30a736aad090d74f3247e12a9090bcc7863ba0ffe08fa2f89590a1ef408f9e3680b014dd508f089b3706ce35008ed70c0a8218e3608e688cdf00691db08e5c65ed15f1c3908e4ebabaf406a3a08d509e47d632f3908cc391f65e6d4a808c0b492f32a96f908c085627d2ec95f08bcddde759282e708aebd5a3556736f08aaa6c3ed524d7008a107ef467b6caa089c6e89daede0c208931fbb3ceccb480856893ac15c4fa1085215d50032844f084cd00be2694b66083ef1441579d842083e3cc4e473529008386ad7f6fd815908273f02b3e7553508257f6a3637158408169615814895a307b7639f395762d607b68a40e9ac2ef107a7dba1dda28fde079d2fb964c0fb0f07798befc8bc982007766c5bcd26d1b1076bc1febd449b62075e66d663083d180749e783a12452650747744aa635e92507301af9e8a59ee1072c95e0e44af5b007261447a2971ab70720c6749263157a07182a74d1f79b8c0718121e157e8e090713031874e47f8506ff17390cbca8bd06f771a78359a1fe06eb04e85fc7f31e06e6793772fd73ce06d014128102f6c206bece645ae6a56106aad7d833eb471606a221e0ca926e92068faf114058308e068136e5c0429ad8067819c83585429e06718696efd61034066768da63d69e1406653a5037ddfa0a065c96acc1ac43a0064c9cdee7f2de840632239fa547146b062e2ad4410c9ace062b36e7f24850cc0626cc1d6b5471f60611d6f06a13f3950608cb84feb0978005f8e28f12698e3b05f607da1cf53f1905ed3a2f7443d7dd05ec49ed20273e5e05e61c1f1d8a39da05dc611190f09a6805d5c89d6c78e86c05d47544cc358e6c05c5cb59aae6ec5505c0f9435715e52f05beb1c0a131bb0205a118ecfbfea41605a00ad356baecd6058c0d5c68ae33690579434e1972a9ca0576c1336aaa240c0576b57a19d939630572a2a290bad0760560bb722666e70e05580bacd737f03c053a793c8833322d052c98f452a5936d052841174c3efc56050a2489eb6a066e05048d6a956c9d5804fd0eecbf998bec04f997c2a95f732504ebdc3c0591926704e54876b59c47a704d3d143bf90c7f204d17f47be9142b904cac3d186caf3d604c8dc004be6c50c04a09f550514d07104921834de49354c047651880c7e95760472e077c1eaa6a2047157415830116f046f5287c133209a04661ed3f2acebd6045b6af32ab61c730457d95994c24b7d042dca17ccf6e0c304291989ca485862042116c5ae6b6ab804156f574dbac2a70404be09032aac7d03fc00077f02f38d03ee4beaca49717803ea3963d45958ac03e7d02f573cf3d703e42b291190f23e03ccb71c303fd58903c7f2abac95c98503ae1ab6ede9a5c203acedbbe86914e603a7d524a6499893038e664a7dab7625038e3fe0f88d0314038d139a87815f470388e5c246fd8e850382623d19a395320373c15023d0166c0370807705af3fb0036e8755afae3b8903618a7af235fc800344257082af071c034149a8d9f7cd610334e4e99b49277d03345737089a5a51032b7db9ba25e8480323db7a75839f22031b7599cc915863031282fb36d822b6030cbc6d5feeac3a0303ec55a6d65e3202f95d8b61bfa0cf02ecc844b17649d802eb91d7c2d1de0702e933ebcb1b261a02d825ea1f84e74102d33c2c66c8835d02cd4989dcf96a0002ca6ac4f4bc36cb02ba96ab3559f65402aa73b79410789702a85b54948bf35b02845b8727832d900273b123adb997d2026e1f25f0af6c6f025da28aeb5d8d8f024ade0ecf17eadb02490f8b76ec07d302478c21ca14c36f022dd7f5606499a902202f8fb0baf1b301ff26a0d4db5a9601fba55ad411914401fabdbe2d50985d01ecc5408316986701e8b8aaeb022fbf01e38e0292798b2101da609dbf47779401cfe81ccac04a0401c65bae231e438601c4e2c6edbab07f01bfd57f243ad07501b43c59c6891e5f01ae246a07a7ad22019fb71eb27342c201979066df97c7b001959d997ea6569d01802826d118756c0171b657d445bbd2016e3ba406c0b065016a53a11ca64fb1016a53101e65661e015fa3d130e1e38601444d878a4b5bec013236845bbdf0810131422b103c65750125d68a6616b077011ecfe4eda0195300fd5c511b17786100fd0e15935ea5b100f4be33a339435000f44b5845f7e8c900f364cc3e85b75500dacad93927786800c338f80f83f89a00c0e1216bb4a7ce00b99337f6ecbeda009ba9e9763a34ed009479c79f15b34f008e3b1bc2f3c7100089c8a26dd9dc9a0089c8a26bf3caf400840692ef23553700701cb68fc20978004e3fb8d35fbe5e0030bab4dc72e3cc002dfa0915559e51002c4b5ca67fc2740022827aca0e771e0018e627f8d27adb0015b46519c169a5001433c5f0c7a82600126fdd2388fd8f000f40a1c2a4731c000e523cbca180b6
  | 7 => 0x1f4bc0eef40e27491e6573e0c68b2ccf1cc12b5c5096b2231b7a6db3188749781a97cdd0251662c81a610b3c3ebf820319b3b5c6b4242db7191330a2f71c9aa818ea682e24648fe21889040207401f1e183b99d16465a88f180fdc935b14614f17ffc9f5b48ee7c017d784dd6febdefb17b1aace6499d31d173d50c7ab6b8fac1734b2aa338d5a9b1654283c811bbf7115763abb95b5ab76153bb47589ad35a6135eb9947d5dcf581353349acbdecb7d12f654f8de02a27b1134b79ef794b43f10d7c246b56a7a1410a726fcdaae1bb61067c405901f1fed0ff452268c09c6840fc1adc253863eeb0d611e1fa4fdf3ca0d597be0605baaa40d48236121b02e380a49d42bdb9fb3a80a44e107ad7c7e9e0a131197f548d2e30a050aa6235efd4e09f3ded0e048d12a0976719c9be6667d0963d9c19cbe2908089c6e89daede0c2085215d50032844f08273f02b3e7553507766c5bcd26d1b1072c95e0e44af5b0052841174c3efc5604f997c2a95f732502cd4989dcf96a0002a85b54948bf35b01ae246a07a7ad22016a53101e65661e00dacad93927786800b99337f6ecbeda0089c8a26bf3caf4002c4b5ca67fc274
  | 8 => 0x89c8a26bf3caf4
  | _ => 0
def PTT : ℕ → ℕ
  | 3 => 0x763400004830200091340000903230008e3400000d34100019320000ab3410012a3310005f330000363300001d3320005a3430000e3210004d2020007e3410007c3310002f330000083030001d343000473300000134300015323000013020002830300053214000343430002d3420002b341000d2340000853210001f3120001630300122341000fa21400076321000e934000008340000a63410000020100001312000793310016c342000f6340000c73410001c31300150341000e83310005934200012301000a2341001012210001d303000fa21000045231001243310003f22100072340000c3203000053300009234100101220000c32210000b340000f733100030340000f020300007320000b13410007b340000ff303000753400000f0000004d20400078321
  | 4 => 0x6a331001883500018735000071202000683500022a352000ef342000a0204000ea33100220323000be213000537030009d231000a0205001623500020a3510018932100055b41002382320022a3510001522000065351001e7620000282140002c2120021c22400097301001eb3530001b20500139350000a6623001502020021930400043a10001a6351000b7312000e7102001da2320011b340000bc3130025c212001c53520008a340001e3251002d9332000a61020031035100018340000af31300107351001b3353000f420300051740000772010014f350003763400019d3510033225300240203001903530022e3400006b33000152351000683400022a3140007d3010006f2210017c352000cb350000c9353000a6723001612510016e351001e32130016c351002ae33200167352002fd2510008130200055a010000e221000b6323002d42040004f312000002100014f3230003d3500000d3030021b350000102020013835200135321001303530012535200090353001203510007f350000b933200395201002d3202000ff35200027314000713500027d321001b0350001b332100068353001aa304000633510005e3530005c332000cd325000102210004f3510004c3130000c33200041352000da3510003d343003ae340000d9351000d035300006221000fe2030025e2530002c351000bf353000ab22000024353001363120006e221000b9353000b73510015f3130022f20300040321001fe3150000e220000ac3410000e351000083530015b61300001352000a3323002293210006a351000a035300099352000462040015c35000055613000593510001720100087352000ab22500082352001bdf12000b93510007d352001bdf13001c3330001e03400036f340000ab22100068331000203230005432000060353001a23320005f3530005e32400043604002f2204000536010004e3520004d353001b73130002a204000443530001f3040028620400160304000a022100038352001bb341000d0203000a02030019c332001fb352002e3320001b230300019351001bde10000233520003b350001903520001a35300018353001bd10100272215000153510000e3130011e22000171203000a3221000282130009f3040007d351001bd1030001b2040006c303000a66140005360400064350001653510003f332001bd102002987240026e3020013235200043302000a72040001020300359352001253320015a34000120321001e710200050221003b93320005171000027231000f533100137303003fc30200422232000e03520010e313000e7624001183500029d3310003830300116253000ea332001e03500031c3420009d341002423410023b351002b3232003ae35100100253000b630400082202000e92510012b352002f435200015201001803300014925100037332000c1332000a6b02001bde130024e3400009b304000e76230010a341000973310002f742000b734000043703001df350001d92500034ab410027a743001bde0200416203001bde12001c8251000b52200024a321001e762300265301000a6a0200068330000a9253000e7724001e03300034a34100086331000803020009f3500028b351000b825000097231001a12030022032100281351001f8303002773420008625100196302000fc221002da331000ab243002d834100319352000573420026b351001bd5010023b3010012f3300001b31500303321000bc2130041b2040001230500053a02000a6713001e7624002253040010b214003193510000e2250019222100043702000a6724002d23530001a313001ab32000230352000e8350001bdf03000ca25100227331003092040036c35000006331000a6624000e7b020000920400256a02002113530036c3400018a2050018a20400298a020002f643000072510005f330003e3340000cc330000da340002643230029f3320002f6400012522100050220000530000012f35000051000001e835200041351001e5352000a6a01001dc35000277353002763240004300000255b410000e243001ce250000b6303000e22100038c350001ca350001963520010ab410002f00000257353002553410012f340003fc340000ef35200256a0100079340001ab35200382613002822310010b2150041b22100002250001973500012622100196350000e7723
  | 5 => 0x9f7140014f65100038340001b8360000a2301001c720400237205001b0321001bd2160010b331000303610003634000089340001d62030011b34000198364001c023200112360001f9613000e2720000122210021a604001c03600018d363000df724001af226001e76040016fb5100267f02001f9703000d87420018bb20002a5350001bd214000aa7500009535000267f030023f3500017b3600005e360001053600017b32000104340001383320017f3620001b341001063030003f7020010335000176360001f7350000c9743000363500023f360000c7754000703410002a22100284330001932500017e221001fe650002056530009f3200029830300074260000a73500002d203000c57530002d221001af221001a1b40000c17540016f351000f13600017e2600016e30300254332000ee6130009a624000c1714000ee350000d8a14000953600012333000163312001c023000071361001b736000289b4000005340002cc2300004f243002abb04000ff604001842260009a6230018e2600015e361000de3610009d340000e2724001b333100219260000d5321000d73510004122100095313000d135200091332000d8a120024134000229604000aa742000fa33100205752000fe3060017f360000a73210001d2030004e3010012436100032650002ad350000677200012e750001842250027d350001453610012333100071341000c33510018526000077232000892100009f75100054350000be36300082202000c5603000633320006231300026750001383530023f331000782210009a720002403600026120300136362000992600001423000257251002dc3210001d2600007233000003b51000af260002936030014f740000523600015a2310012a361000172610004c362000df721002aa2300016f750001d42050012435300013261000ed260000fc6500022c204000202020007f7530008660300080203001203320006b3610005d203000a6352002d82050025d340001997050010f361000486020011b351001a2250000a2352000cc2300006f330001d9360002103400001830100136232001da7030025ba510010a363000a3250000ae31200127206002eb2600004432100104351002dee02001272320029c360001d732100003714000d9331000ae303002d2204000d636300003301000fa36200151332002b83400018ba4000108360002877030017a2600019f32100081363000a63600002020300056751000723310015e36000205751000466020001a32100017331000f133100002230000b33320007c35200127204000133010016f30300000205000303320002a2030025e3500004875300003723001fa203000e3231000e9361000d430100202703001e336100073651001dc26000287b020029c3400003f7530016b651002242600006c350000c3b0200280360001c5330002a820500229605000a02210025b612002056500002a220001fa250000693500001c3210009a721000d136300037752000bb360000b9305002c433000036321000ca3620027c3510001b3610015865400032742002f5230000a634000086a04000312210016fb03002a236000154653000c62320005736000148703002a7360000022210006e3600014f750000c0351000eb206001cd33000283205000bf352000182210017e303001342310008a36000065350001ec2500004d75000182260002af230001b8321002af2600028a360000e2650002953500006e321000443130002d202000de221001bd2150016b75200040330001cf340000d1360000b636300046b4000091231000eb20400199624000a73400009fb51000c3751000ce2020000d742000393630025e3400000f33200065360000ad353000942060012e653001dc263000d63500028a350000db302001b735000158752002d820600008753000a6321001d7263000a63630000f351000922040002e302001547540002b323000a6350002623500005436000032a02002d1330000a236100027352000a1321002b8350000677500008d350002def03002992310007d361001c92200009f3510009e3310022e260000df75000024330002d2205001b03130009836200038360000132030018ba3000165205000ff7210004f2210027b3500001a3230001836300057321000922060004e313000d8a13001b8263002bd2060019275200260250002bd204000e9360000363200025e3600009f720000752100006636000062361000266510021b36000081324001b0263000b72030024d72400060363000c7603000ff7030007c36300003352001ac2610007a3610017d752002d2206000c3b510005331300188312002bb360000802120029c350000252500006f331000f1212000d8a15000036120009b36200248203000567040005f21000237206000433620015a360000693610001326000168723001b3350001d836000033230002fa3500008620300044304002def43000d1304000813600002432000046b52002ad34000086a050005f363000632310005d363000d86520010631300217205000573310015875100274360002832060008b203000fc7520017b26200053362000c9653001547510010926000094204000f8360001b8350001926530025db400004a3210003c301001a2240000b624300124260000463520016f3400004c243000443240004335100040361000703610019960400249650002312610013e360000393240001c30600031203002cb2200027d3400001436100199723001c6603001ac260000d8730002c5363000c97500009f7210003435200033353000d8753002c4353002752600024b71300127205002916200002e3630002b3640001d2500011d36000293752001686240000310100009361001a1a30001eb360000aa652000162100016f740001dd340000623600002436100129330000632500001f362002897530002432100200203000443030015f2600001022000070332000867140009a650000782030009f6040000f3610001a3640026e36000003b0100013231000b92100015865300081340001546520011f332000042100010d7040000c3210007a2210015e350001e9b40002c2360000a3240000a93010002f3600012a231001c72050019970300196231001d5321001c5340002ab7500001f360002923410025d751000fc75100267101002dee400001b3510024db520001f210001302200012136000020221001b2340001d4206001ea3210008b220000012120005330300138260000eb20500168625000ee7130027e3520023720400039321000cd2120017e3230005a3600008f2040021a6130006f260000037520019126000110261000a1340000c6305000db312000e275300031220000ca33200263350002e1a210003633100271260002172060006e350002c23400024b10100005360001802030000f301000676530001e360002497400021ab51001bf614000b62020020cb0200127221001500000008b2210008d3600021a1010004322100267341002e1620002a53320017635000077210001fc350001b0360000c9751000566030025d750002dee0300158623000aa623001c6604002ea3600005165200154721002f136000027260000c361400150603000143600029531300150b40000677400008e26000011321000ca36100172360000ce20300220350000fc653002a660400174304001083400001d240000622100006d331000dc261000db2610015e3210009d3600008f20300267f120005a321000d1350002d5603002c2350002012200009d350002a82060004c32100199b52000cd241000cc231000383500025a6500003265200003b52000aa751002d8204000e2654002c7260000d8750001b33600001f304000df653000c0261001d232100051754001b73400004d754000eb221001687240022d353001513610021a713002163510011c221002d5604000ae302000e9350002b8360000103210014c33000280361002de5000008d340002a536300005350000c9652000ba223001fe740000282500001f3210017d75100140341001372600009f3210010d6030015f350002fe26000078220001df3020009b35200060220000913600007d3500000d6520011026200081330002953510023465100227321002ad36000202705000fc7400009220500032753001f9754002e9360001663310008933000010203001d4204001282500014a32100037b400001b33200026753002b174000135351000a02310016fb40000fc62300289a41000da36000051623000303010009b26100272230002f13040009f6130008f26000014301001b83310025db51000a736000073752001e975200165206001e77520009f703000aa653001102030029a215000b7221000866040000936000267501000a32600026b3600008c261000602210008b261000b3261001da751001b8340000093010008826100005321000022010027b36000088212002403610024bb520015c2310011a34100086a030025d351000c5000001652040006c3600009a6530029d260000c100000215260000ed23100139331002a82040027125000138361001f5350002832040006023000026730001a4221000aa72100184220000f736000210331001b2360002ab7040017435000051751000c9721001f03500011d303001ed3500004d752000bc0000009f7500020c7030018d2210024b352001513510015065100058221001df350000ce2430004c341001de330001b3340000f0360000aa000001a2260001d8361000486030025b604002bd2050012d26100073702001162600004036000238313000327510012836000033360000012620009f0000017c332001382310004f2410022e351000036140010e3610004c2610001b301001d935000067652001c3350000472310027c332002853610022c221001bc350002733200021ab520016d2040002b203002a53040013e340002e46030022c260000882620005434000036360001ff3600007f7040000f341000953040002524000051653002de100001af3500004d6530013e32100005310001833210021a352001a8350001ec260002def4000287705002af240002def02000036240011a3510020f36200073000000df620000e03310001f350002ff36000168751000dc2030003d320001bf65100174360001ee361000267400022d3600027d360002b326000051721002af25000193260000ad260000ed261000670000018d3210004c2020020e26000099250000022310007a323000822430002665200010223000377030025d740000273200021720400155204000e2623001e9b52001d6363001f835100056a0500051000000b22030008935000001261002e5723002b92300014875400023220001d626200046a21000267200004800000003613000b22210004600000032721001e7a02001ed361000c8260001763400001a3300016862300081350002c9260001eb363000ad3500000c310002803050027b3400020f36000094205001e93520007a203001bf352002a426000086204000ee703001df3610016f703002f135000003a51001cf3300028665000012260002002210012e74300028360002bb30500278330001bf2510009fb21001d83230006e3400007035100093360002c4340000320000006921200108350002283600007c2210006b341001f73600002f25000026000002ca260001fa260001f734000071351002ab3040008f25000045231001c3361000252600006336000178360001c7232001c0362001e4215001f9b5100003713001686200005a35000108330000c371300014231000893610010d7530003b232000c636100198202000d87200004660300017360002bc36000134330000002010028a340001bb2600020336000046b310012eb02001af361000df6230010f341001ef206001fa24000249753000393400009b302000ff751001d9340001e4214000080000009b3120000300000194330
  | 6 => 0xe504000313210000271300013753000127520001510000027721000117530000c10000014b20000336050000310400008b3000014a3000031b600000ef050000ee13000011040000ef5400010753000236240000f75100017a6000002221000196600002310200015f530001f72400020b3000030a400000ee0400009f030002f60500007604000313600000670200012b40000095000000e75400001e420001a60500015340000237260000ee050000d753000336030000c7520000ef020001b75000009e540001b36000017a5000029a600000270300006e5200034b50000237250002110000017b520000ef530000b75300019b5000007b5000009e520002cb4000014a2000015f5200015e320002560400008a4000015f020000a7500000910400001f52000077030001f62400016a500000940400009f420000f603000173520001f1020000950300030b600001bb3000023625000162210000ba05000321000001a6040002560300009e420001625000009f530001f72600024f0200028a20000263600001766000024f0300001e4000025605000207400000ef52000187050000ee3200017b5000010a300000b6060000ba030003170400006e540001f725000181000000b6030000c6600001236000015101000097530000876400028760000131030000fb6000006e510002c703000226030000960200001e520002526000017350000286500001c62500009f040000150500014660000216050000610400015b5100008a500001b74000008a60000064040000cb6000015e4200006f410000940000026100000226050000650300009f5200015500000231000001f62500002a4000015f5400001f54000251000001c721000155040002f6040001535100002a500000510300006e4100019a4000019a3000006f5300028b400000e1040001ba300000960300001e4300006b400003233000001f530001c7260002410000010b600001c32100031760000077510000310300027b2100001e41000065000000ee120000675300029a500001574000001103000203300000cb52000014030000ef510000772300018a2100001f3100009f5100009e2100028a4000016604000015020000e50100001e530001f7230000f750000057420000ca5000009f0200006f510001ab600000c35200001e3100001f42000267210000bb420001862400010b3000015e1300015f420002b104000216030002e3600002d6050000ee02000037420000275200026b400001f1000000174200000b1000030a600002d6060000b60500000714000081000002210000015b400002e7040000910300016b600002076000014b3000006f5200001f500001872500014a5000006e120000ee430000ef120001c7230000b20500001f41000076600000640000009e4100016b500001c7040001b33000009f5400000a2000022260000095040000bb5200010a200000b20300034b6000029604000256210001b1000000e6030000762100012a500001e750000146630003273000030b500000e1000001e6400001266200028b6000016a21000116630002e10000015e4000030b200000c26000001f40000073620000610300001e100000ba040000f76000020b6000014b6000031703000106630000f6610002e62300024f0400001e510000726000012a3000015e5000024e0300007b510001c6240000b70600000a300002c62300008b5000024f5100006e4200002a600000b62100013a2000026760000051020000e50200006f5000016760000323600000ee4200006f540000d6630000e4020001872300009e320000735100021a600000ba060000c66200009f410000650400025b6000024e0200010a500000e503000031020000ee1400007603000256230001076000024e040000b66300001102000256600001bb4000006f020001aa21000036500000a66000030b40000014050000ba210000ef0400001e5400000b300001426000008b2100009e040001274000000a4000001e300000d76400024e51000246500000c764000126230001fb6000031b2100024505000311000001a2210002e7050001e10400001f4300014b4000015f4000019a50000192600001c703000015030001b62300030b300000fb5000019b200000b76400009e0200000b400001862100025b6200006e3100006f42000263210002e7600002450000019b400000a764000021000001a6140001a60300009f050000f60400009501000256250001f7030001bb5000006a300000862400024f5400008b600000f35000020b5000009e310003135000035b300002d6030000b7050000940100007a5000013a3000025a21000256240001610000009e0300009502000277040002410400009e430001bb600001b350000244040001aa6000024f43000203500002f606000245010001b760000252210000722100024e54000277030002162100001f5100006e5000030a200002926000001e2100001f300002770500010b5000016723000271000001c706000327600000872500024e430002440000000a600000940200022625000186030001770300032b4000009f3100012750000076610000ee0300000b500002cb5000006502000187060000b204000226210000e50000006e4000008b4000006e320001710000009f210000640200026b6000017b40000236050000940300029100000347030000f7030000650100006e4300006f40000056520001273000012b600001c604000237640001a70400002b60000051050002c1000000466400027b6000022724000207300000c6210000b20600019b60000236030000776200002b400000b1000001c10000025a6000025a61000036520000266200021b600001a10000006f100000f3600001c606000031050001b3400000165200006f320000150000028a3000014a40000011050001fa5000001e200000140000026b50000006640000fa600000575300024a5100012b300000872100006f12000091000002360400004765000057500000150100001e3200028a600001fb500002e305000064030002f6030003235000015f500002266000021724000207530001c605000186050000b221000151050000761400009e050001cb21000037530001e10300015e0300028b5000013105000027640001f7640001c70500007b60000317500002034000034704000017530001665000010360000014010001575000000765000273210000ca2100001f2000015e5100016a600001822100019a2000024f500001a6210002b65000001f10000077630000e10500010a600001775000021723000014020002eb600000f704000086230000c6030001a624000241010001234000026b21000026210000260300015e020002cb600001d76400019b30000317210000ee540001c7150000e6040002160400020a50000057510001b754000323400000f10000031b50000061000000476200026a500000cb50000186040000b7040002e70300030a500002010000002b5000010a4000002a210001a72500010b200001662100019754000091010000970400017b6000022a21000186060000276300015e5200016b520000175000006f3000007a2100015f0300001e5000006f4300021a210002d725000296600000076200022a6000014b50000222210002d604000127600001b7300002260400006e020002360600015400000327500002d1000003061400012b500002122100028a500000ca4000009105000267030000b60400006101000077130000ca600000fa5000007b6200013b400002f1000000ee52000046630000ef030002f62500028360000331000001ba5000007a60000071000001235000013b100001876400017752000282500001675400000b2000009e5300003651000203600001fb40000157020000266100015e5400001f320003360600030a300002d62500001651000336040002d10200032b60000026600000066300015e5300008a300000226000029603000031010001510400007624000123300001a7230002eb0500028b20000154040002d7260001310400015f43000027230000110100010b40000155010000c22100028b30000276250003410000006105000001000002372400006e3000000a50000121000000ee510003274000015e430000e40000015f510001660300014a600000110000032b5000032b3000001f210000ee5300024e500002075000000a100000100000006e53000051040000e10100020b4000008321000000000000e40100009e5100019a60000157510000ef130001475300000b60
  | 7 => 0x10400000e4200000f5200000e4000000e520000050500000f5400000e4300000f5300000e41000001030000040300000f310000050200000e5300000e3100000f420000074200000f5000000f4100000f4000000e1000000e51000001020000040500000e5400000e3000000f430000050300000f5100000e2100000f3000000652000005000000010500000e20000004000000050100000e32000007530000040100000f2000000f10000004020000075000000e5000000f320000065100000101000004040000010000000f210000000000000504
  | _ => 0
def ZT (s : ℕ) := bar 50 (Sgen 50 8 xsT PTT) NNT (idxGen NNT HTT) id [] s
theorem zT_0 : span (ZT 0) 0 0 = true := rfl
theorem zT_1 : span (ZT 1) 0 0 = true := rfl
theorem zT_2 : span (ZT 2) 0 0 = true := rfl
theorem hT_3_0 : span (ZT 3) 10 0 = true := by decide +kernel
theorem hT_3_10 : span (ZT 3) 10 10 = true := by decide +kernel
theorem hT_3_20 : span (ZT 3) 10 20 = true := by decide +kernel
theorem hT_3_30 : span (ZT 3) 10 30 = true := by decide +kernel
theorem hT_3_40 : span (ZT 3) 10 40 = true := by decide +kernel
theorem hT_3_50 : span (ZT 3) 10 50 = true := by decide +kernel
theorem hT_3_60 : span (ZT 3) 10 60 = true := by decide +kernel
theorem hT_3_70 : span (ZT 3) 5 70 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem zT_3 : span (ZT 3) 75 0 = true := (@span_join (ZT 3) 70 0 5 (@span_join (ZT 3) 60 0 10 (@span_join (ZT 3) 50 0 10 (@span_join (ZT 3) 40 0 10 (@span_join (ZT 3) 30 0 10 (@span_join (ZT 3) 20 0 10 (@span_join (ZT 3) 10 0 10 hT_3_0 hT_3_10) hT_3_20) hT_3_30) hT_3_40) hT_3_50) hT_3_60) hT_3_70)
theorem hT_4_0 : span (ZT 4) 10 0 = true := by decide +kernel
theorem hT_4_10 : span (ZT 4) 10 10 = true := by decide +kernel
theorem hT_4_20 : span (ZT 4) 10 20 = true := by decide +kernel
theorem hT_4_30 : span (ZT 4) 10 30 = true := by decide +kernel
theorem hT_4_40 : span (ZT 4) 10 40 = true := by decide +kernel
theorem hT_4_50 : span (ZT 4) 10 50 = true := by decide +kernel
theorem hT_4_60 : span (ZT 4) 10 60 = true := by decide +kernel
theorem hT_4_70 : span (ZT 4) 10 70 = true := by decide +kernel
theorem hT_4_80 : span (ZT 4) 10 80 = true := by decide +kernel
theorem hT_4_90 : span (ZT 4) 10 90 = true := by decide +kernel
theorem hT_4_100 : span (ZT 4) 10 100 = true := by decide +kernel
theorem hT_4_110 : span (ZT 4) 10 110 = true := by decide +kernel
theorem hT_4_120 : span (ZT 4) 10 120 = true := by decide +kernel
theorem hT_4_130 : span (ZT 4) 10 130 = true := by decide +kernel
theorem hT_4_140 : span (ZT 4) 10 140 = true := by decide +kernel
theorem hT_4_150 : span (ZT 4) 10 150 = true := by decide +kernel
theorem hT_4_160 : span (ZT 4) 10 160 = true := by decide +kernel
theorem hT_4_170 : span (ZT 4) 10 170 = true := by decide +kernel
theorem hT_4_180 : span (ZT 4) 10 180 = true := by decide +kernel
theorem hT_4_190 : span (ZT 4) 10 190 = true := by decide +kernel
theorem hT_4_200 : span (ZT 4) 10 200 = true := by decide +kernel
theorem hT_4_210 : span (ZT 4) 10 210 = true := by decide +kernel
theorem hT_4_220 : span (ZT 4) 10 220 = true := by decide +kernel
theorem hT_4_230 : span (ZT 4) 10 230 = true := by decide +kernel
theorem hT_4_240 : span (ZT 4) 10 240 = true := by decide +kernel
theorem hT_4_250 : span (ZT 4) 10 250 = true := by decide +kernel
theorem hT_4_260 : span (ZT 4) 10 260 = true := by decide +kernel
theorem hT_4_270 : span (ZT 4) 10 270 = true := by decide +kernel
theorem hT_4_280 : span (ZT 4) 10 280 = true := by decide +kernel
theorem hT_4_290 : span (ZT 4) 10 290 = true := by decide +kernel
theorem hT_4_300 : span (ZT 4) 10 300 = true := by decide +kernel
theorem hT_4_310 : span (ZT 4) 10 310 = true := by decide +kernel
theorem hT_4_320 : span (ZT 4) 10 320 = true := by decide +kernel
theorem hT_4_330 : span (ZT 4) 10 330 = true := by decide +kernel
theorem hT_4_340 : span (ZT 4) 10 340 = true := by decide +kernel
theorem hT_4_350 : span (ZT 4) 10 350 = true := by decide +kernel
theorem hT_4_360 : span (ZT 4) 10 360 = true := by decide +kernel
theorem hT_4_370 : span (ZT 4) 10 370 = true := by decide +kernel
theorem hT_4_380 : span (ZT 4) 10 380 = true := by decide +kernel
theorem hT_4_390 : span (ZT 4) 7 390 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem zT_4 : span (ZT 4) 397 0 = true := (@span_join (ZT 4) 390 0 7 (@span_join (ZT 4) 380 0 10 (@span_join (ZT 4) 370 0 10 (@span_join (ZT 4) 360 0 10 (@span_join (ZT 4) 350 0 10 (@span_join (ZT 4) 340 0 10 (@span_join (ZT 4) 330 0 10 (@span_join (ZT 4) 320 0 10 (@span_join (ZT 4) 310 0 10 (@span_join (ZT 4) 300 0 10 (@span_join (ZT 4) 290 0 10 (@span_join (ZT 4) 280 0 10 (@span_join (ZT 4) 270 0 10 (@span_join (ZT 4) 260 0 10 (@span_join (ZT 4) 250 0 10 (@span_join (ZT 4) 240 0 10 (@span_join (ZT 4) 230 0 10 (@span_join (ZT 4) 220 0 10 (@span_join (ZT 4) 210 0 10 (@span_join (ZT 4) 200 0 10 (@span_join (ZT 4) 190 0 10 (@span_join (ZT 4) 180 0 10 (@span_join (ZT 4) 170 0 10 (@span_join (ZT 4) 160 0 10 (@span_join (ZT 4) 150 0 10 (@span_join (ZT 4) 140 0 10 (@span_join (ZT 4) 130 0 10 (@span_join (ZT 4) 120 0 10 (@span_join (ZT 4) 110 0 10 (@span_join (ZT 4) 100 0 10 (@span_join (ZT 4) 90 0 10 (@span_join (ZT 4) 80 0 10 (@span_join (ZT 4) 70 0 10 (@span_join (ZT 4) 60 0 10 (@span_join (ZT 4) 50 0 10 (@span_join (ZT 4) 40 0 10 (@span_join (ZT 4) 30 0 10 (@span_join (ZT 4) 20 0 10 (@span_join (ZT 4) 10 0 10 hT_4_0 hT_4_10) hT_4_20) hT_4_30) hT_4_40) hT_4_50) hT_4_60) hT_4_70) hT_4_80) hT_4_90) hT_4_100) hT_4_110) hT_4_120) hT_4_130) hT_4_140) hT_4_150) hT_4_160) hT_4_170) hT_4_180) hT_4_190) hT_4_200) hT_4_210) hT_4_220) hT_4_230) hT_4_240) hT_4_250) hT_4_260) hT_4_270) hT_4_280) hT_4_290) hT_4_300) hT_4_310) hT_4_320) hT_4_330) hT_4_340) hT_4_350) hT_4_360) hT_4_370) hT_4_380) hT_4_390)
theorem hT_5_0 : span (ZT 5) 10 0 = true := by decide +kernel
theorem hT_5_10 : span (ZT 5) 10 10 = true := by decide +kernel
theorem hT_5_20 : span (ZT 5) 10 20 = true := by decide +kernel
theorem hT_5_30 : span (ZT 5) 10 30 = true := by decide +kernel
theorem hT_5_40 : span (ZT 5) 10 40 = true := by decide +kernel
theorem hT_5_50 : span (ZT 5) 10 50 = true := by decide +kernel
theorem hT_5_60 : span (ZT 5) 10 60 = true := by decide +kernel
theorem hT_5_70 : span (ZT 5) 10 70 = true := by decide +kernel
theorem hT_5_80 : span (ZT 5) 10 80 = true := by decide +kernel
theorem hT_5_90 : span (ZT 5) 10 90 = true := by decide +kernel
theorem hT_5_100 : span (ZT 5) 10 100 = true := by decide +kernel
theorem hT_5_110 : span (ZT 5) 10 110 = true := by decide +kernel
theorem hT_5_120 : span (ZT 5) 10 120 = true := by decide +kernel
theorem hT_5_130 : span (ZT 5) 10 130 = true := by decide +kernel
theorem hT_5_140 : span (ZT 5) 10 140 = true := by decide +kernel
theorem hT_5_150 : span (ZT 5) 10 150 = true := by decide +kernel
theorem hT_5_160 : span (ZT 5) 10 160 = true := by decide +kernel
theorem hT_5_170 : span (ZT 5) 10 170 = true := by decide +kernel
theorem hT_5_180 : span (ZT 5) 10 180 = true := by decide +kernel
theorem hT_5_190 : span (ZT 5) 10 190 = true := by decide +kernel
theorem hT_5_200 : span (ZT 5) 10 200 = true := by decide +kernel
theorem hT_5_210 : span (ZT 5) 10 210 = true := by decide +kernel
theorem hT_5_220 : span (ZT 5) 10 220 = true := by decide +kernel
theorem hT_5_230 : span (ZT 5) 10 230 = true := by decide +kernel
theorem hT_5_240 : span (ZT 5) 10 240 = true := by decide +kernel
theorem hT_5_250 : span (ZT 5) 10 250 = true := by decide +kernel
theorem hT_5_260 : span (ZT 5) 10 260 = true := by decide +kernel
theorem hT_5_270 : span (ZT 5) 10 270 = true := by decide +kernel
theorem hT_5_280 : span (ZT 5) 10 280 = true := by decide +kernel
theorem hT_5_290 : span (ZT 5) 10 290 = true := by decide +kernel
theorem hT_5_300 : span (ZT 5) 10 300 = true := by decide +kernel
theorem hT_5_310 : span (ZT 5) 10 310 = true := by decide +kernel
theorem hT_5_320 : span (ZT 5) 10 320 = true := by decide +kernel
theorem hT_5_330 : span (ZT 5) 10 330 = true := by decide +kernel
theorem hT_5_340 : span (ZT 5) 10 340 = true := by decide +kernel
theorem hT_5_350 : span (ZT 5) 10 350 = true := by decide +kernel
theorem hT_5_360 : span (ZT 5) 10 360 = true := by decide +kernel
theorem hT_5_370 : span (ZT 5) 10 370 = true := by decide +kernel
theorem hT_5_380 : span (ZT 5) 10 380 = true := by decide +kernel
theorem hT_5_390 : span (ZT 5) 10 390 = true := by decide +kernel
theorem hT_5_400 : span (ZT 5) 10 400 = true := by decide +kernel
theorem hT_5_410 : span (ZT 5) 10 410 = true := by decide +kernel
theorem hT_5_420 : span (ZT 5) 10 420 = true := by decide +kernel
theorem hT_5_430 : span (ZT 5) 10 430 = true := by decide +kernel
theorem hT_5_440 : span (ZT 5) 10 440 = true := by decide +kernel
theorem hT_5_450 : span (ZT 5) 10 450 = true := by decide +kernel
theorem hT_5_460 : span (ZT 5) 10 460 = true := by decide +kernel
theorem hT_5_470 : span (ZT 5) 10 470 = true := by decide +kernel
theorem hT_5_480 : span (ZT 5) 10 480 = true := by decide +kernel
theorem hT_5_490 : span (ZT 5) 10 490 = true := by decide +kernel
theorem hT_5_500 : span (ZT 5) 10 500 = true := by decide +kernel
theorem hT_5_510 : span (ZT 5) 10 510 = true := by decide +kernel
theorem hT_5_520 : span (ZT 5) 10 520 = true := by decide +kernel
theorem hT_5_530 : span (ZT 5) 10 530 = true := by decide +kernel
theorem hT_5_540 : span (ZT 5) 10 540 = true := by decide +kernel
theorem hT_5_550 : span (ZT 5) 10 550 = true := by decide +kernel
theorem hT_5_560 : span (ZT 5) 10 560 = true := by decide +kernel
theorem hT_5_570 : span (ZT 5) 10 570 = true := by decide +kernel
theorem hT_5_580 : span (ZT 5) 10 580 = true := by decide +kernel
theorem hT_5_590 : span (ZT 5) 10 590 = true := by decide +kernel
theorem hT_5_600 : span (ZT 5) 10 600 = true := by decide +kernel
theorem hT_5_610 : span (ZT 5) 10 610 = true := by decide +kernel
theorem hT_5_620 : span (ZT 5) 10 620 = true := by decide +kernel
theorem hT_5_630 : span (ZT 5) 10 630 = true := by decide +kernel
theorem hT_5_640 : span (ZT 5) 10 640 = true := by decide +kernel
theorem hT_5_650 : span (ZT 5) 10 650 = true := by decide +kernel
theorem hT_5_660 : span (ZT 5) 10 660 = true := by decide +kernel
theorem hT_5_670 : span (ZT 5) 10 670 = true := by decide +kernel
theorem hT_5_680 : span (ZT 5) 10 680 = true := by decide +kernel
theorem hT_5_690 : span (ZT 5) 10 690 = true := by decide +kernel
theorem hT_5_700 : span (ZT 5) 10 700 = true := by decide +kernel
theorem hT_5_710 : span (ZT 5) 10 710 = true := by decide +kernel
theorem hT_5_720 : span (ZT 5) 10 720 = true := by decide +kernel
theorem hT_5_730 : span (ZT 5) 10 730 = true := by decide +kernel
theorem hT_5_740 : span (ZT 5) 10 740 = true := by decide +kernel
theorem hT_5_750 : span (ZT 5) 10 750 = true := by decide +kernel
theorem hT_5_760 : span (ZT 5) 10 760 = true := by decide +kernel
theorem hT_5_770 : span (ZT 5) 10 770 = true := by decide +kernel
theorem hT_5_780 : span (ZT 5) 10 780 = true := by decide +kernel
theorem hT_5_790 : span (ZT 5) 10 790 = true := by decide +kernel
theorem hT_5_800 : span (ZT 5) 10 800 = true := by decide +kernel
theorem hT_5_810 : span (ZT 5) 10 810 = true := by decide +kernel
theorem hT_5_820 : span (ZT 5) 10 820 = true := by decide +kernel
theorem hT_5_830 : span (ZT 5) 10 830 = true := by decide +kernel
theorem hT_5_840 : span (ZT 5) 10 840 = true := by decide +kernel
theorem hT_5_850 : span (ZT 5) 10 850 = true := by decide +kernel
theorem hT_5_860 : span (ZT 5) 10 860 = true := by decide +kernel
theorem hT_5_870 : span (ZT 5) 10 870 = true := by decide +kernel
theorem hT_5_880 : span (ZT 5) 10 880 = true := by decide +kernel
theorem hT_5_890 : span (ZT 5) 10 890 = true := by decide +kernel
theorem hT_5_900 : span (ZT 5) 10 900 = true := by decide +kernel
theorem hT_5_910 : span (ZT 5) 10 910 = true := by decide +kernel
theorem hT_5_920 : span (ZT 5) 10 920 = true := by decide +kernel
theorem hT_5_930 : span (ZT 5) 10 930 = true := by decide +kernel
theorem hT_5_940 : span (ZT 5) 10 940 = true := by decide +kernel
theorem hT_5_950 : span (ZT 5) 10 950 = true := by decide +kernel
theorem hT_5_960 : span (ZT 5) 10 960 = true := by decide +kernel
theorem hT_5_970 : span (ZT 5) 10 970 = true := by decide +kernel
theorem hT_5_980 : span (ZT 5) 10 980 = true := by decide +kernel
theorem hT_5_990 : span (ZT 5) 10 990 = true := by decide +kernel
theorem hT_5_1000 : span (ZT 5) 10 1000 = true := by decide +kernel
theorem hT_5_1010 : span (ZT 5) 10 1010 = true := by decide +kernel
theorem hT_5_1020 : span (ZT 5) 10 1020 = true := by decide +kernel
theorem hT_5_1030 : span (ZT 5) 10 1030 = true := by decide +kernel
theorem hT_5_1040 : span (ZT 5) 10 1040 = true := by decide +kernel
theorem hT_5_1050 : span (ZT 5) 10 1050 = true := by decide +kernel
theorem hT_5_1060 : span (ZT 5) 10 1060 = true := by decide +kernel
theorem hT_5_1070 : span (ZT 5) 10 1070 = true := by decide +kernel
theorem hT_5_1080 : span (ZT 5) 1 1080 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem zT_5 : span (ZT 5) 1081 0 = true := (@span_join (ZT 5) 1080 0 1 (@span_join (ZT 5) 1070 0 10 (@span_join (ZT 5) 1060 0 10 (@span_join (ZT 5) 1050 0 10 (@span_join (ZT 5) 1040 0 10 (@span_join (ZT 5) 1030 0 10 (@span_join (ZT 5) 1020 0 10 (@span_join (ZT 5) 1010 0 10 (@span_join (ZT 5) 1000 0 10 (@span_join (ZT 5) 990 0 10 (@span_join (ZT 5) 980 0 10 (@span_join (ZT 5) 970 0 10 (@span_join (ZT 5) 960 0 10 (@span_join (ZT 5) 950 0 10 (@span_join (ZT 5) 940 0 10 (@span_join (ZT 5) 930 0 10 (@span_join (ZT 5) 920 0 10 (@span_join (ZT 5) 910 0 10 (@span_join (ZT 5) 900 0 10 (@span_join (ZT 5) 890 0 10 (@span_join (ZT 5) 880 0 10 (@span_join (ZT 5) 870 0 10 (@span_join (ZT 5) 860 0 10 (@span_join (ZT 5) 850 0 10 (@span_join (ZT 5) 840 0 10 (@span_join (ZT 5) 830 0 10 (@span_join (ZT 5) 820 0 10 (@span_join (ZT 5) 810 0 10 (@span_join (ZT 5) 800 0 10 (@span_join (ZT 5) 790 0 10 (@span_join (ZT 5) 780 0 10 (@span_join (ZT 5) 770 0 10 (@span_join (ZT 5) 760 0 10 (@span_join (ZT 5) 750 0 10 (@span_join (ZT 5) 740 0 10 (@span_join (ZT 5) 730 0 10 (@span_join (ZT 5) 720 0 10 (@span_join (ZT 5) 710 0 10 (@span_join (ZT 5) 700 0 10 (@span_join (ZT 5) 690 0 10 (@span_join (ZT 5) 680 0 10 (@span_join (ZT 5) 670 0 10 (@span_join (ZT 5) 660 0 10 (@span_join (ZT 5) 650 0 10 (@span_join (ZT 5) 640 0 10 (@span_join (ZT 5) 630 0 10 (@span_join (ZT 5) 620 0 10 (@span_join (ZT 5) 610 0 10 (@span_join (ZT 5) 600 0 10 (@span_join (ZT 5) 590 0 10 (@span_join (ZT 5) 580 0 10 (@span_join (ZT 5) 570 0 10 (@span_join (ZT 5) 560 0 10 (@span_join (ZT 5) 550 0 10 (@span_join (ZT 5) 540 0 10 (@span_join (ZT 5) 530 0 10 (@span_join (ZT 5) 520 0 10 (@span_join (ZT 5) 510 0 10 (@span_join (ZT 5) 500 0 10 (@span_join (ZT 5) 490 0 10 (@span_join (ZT 5) 480 0 10 (@span_join (ZT 5) 470 0 10 (@span_join (ZT 5) 460 0 10 (@span_join (ZT 5) 450 0 10 (@span_join (ZT 5) 440 0 10 (@span_join (ZT 5) 430 0 10 (@span_join (ZT 5) 420 0 10 (@span_join (ZT 5) 410 0 10 (@span_join (ZT 5) 400 0 10 (@span_join (ZT 5) 390 0 10 (@span_join (ZT 5) 380 0 10 (@span_join (ZT 5) 370 0 10 (@span_join (ZT 5) 360 0 10 (@span_join (ZT 5) 350 0 10 (@span_join (ZT 5) 340 0 10 (@span_join (ZT 5) 330 0 10 (@span_join (ZT 5) 320 0 10 (@span_join (ZT 5) 310 0 10 (@span_join (ZT 5) 300 0 10 (@span_join (ZT 5) 290 0 10 (@span_join (ZT 5) 280 0 10 (@span_join (ZT 5) 270 0 10 (@span_join (ZT 5) 260 0 10 (@span_join (ZT 5) 250 0 10 (@span_join (ZT 5) 240 0 10 (@span_join (ZT 5) 230 0 10 (@span_join (ZT 5) 220 0 10 (@span_join (ZT 5) 210 0 10 (@span_join (ZT 5) 200 0 10 (@span_join (ZT 5) 190 0 10 (@span_join (ZT 5) 180 0 10 (@span_join (ZT 5) 170 0 10 (@span_join (ZT 5) 160 0 10 (@span_join (ZT 5) 150 0 10 (@span_join (ZT 5) 140 0 10 (@span_join (ZT 5) 130 0 10 (@span_join (ZT 5) 120 0 10 (@span_join (ZT 5) 110 0 10 (@span_join (ZT 5) 100 0 10 (@span_join (ZT 5) 90 0 10 (@span_join (ZT 5) 80 0 10 (@span_join (ZT 5) 70 0 10 (@span_join (ZT 5) 60 0 10 (@span_join (ZT 5) 50 0 10 (@span_join (ZT 5) 40 0 10 (@span_join (ZT 5) 30 0 10 (@span_join (ZT 5) 20 0 10 (@span_join (ZT 5) 10 0 10 hT_5_0 hT_5_10) hT_5_20) hT_5_30) hT_5_40) hT_5_50) hT_5_60) hT_5_70) hT_5_80) hT_5_90) hT_5_100) hT_5_110) hT_5_120) hT_5_130) hT_5_140) hT_5_150) hT_5_160) hT_5_170) hT_5_180) hT_5_190) hT_5_200) hT_5_210) hT_5_220) hT_5_230) hT_5_240) hT_5_250) hT_5_260) hT_5_270) hT_5_280) hT_5_290) hT_5_300) hT_5_310) hT_5_320) hT_5_330) hT_5_340) hT_5_350) hT_5_360) hT_5_370) hT_5_380) hT_5_390) hT_5_400) hT_5_410) hT_5_420) hT_5_430) hT_5_440) hT_5_450) hT_5_460) hT_5_470) hT_5_480) hT_5_490) hT_5_500) hT_5_510) hT_5_520) hT_5_530) hT_5_540) hT_5_550) hT_5_560) hT_5_570) hT_5_580) hT_5_590) hT_5_600) hT_5_610) hT_5_620) hT_5_630) hT_5_640) hT_5_650) hT_5_660) hT_5_670) hT_5_680) hT_5_690) hT_5_700) hT_5_710) hT_5_720) hT_5_730) hT_5_740) hT_5_750) hT_5_760) hT_5_770) hT_5_780) hT_5_790) hT_5_800) hT_5_810) hT_5_820) hT_5_830) hT_5_840) hT_5_850) hT_5_860) hT_5_870) hT_5_880) hT_5_890) hT_5_900) hT_5_910) hT_5_920) hT_5_930) hT_5_940) hT_5_950) hT_5_960) hT_5_970) hT_5_980) hT_5_990) hT_5_1000) hT_5_1010) hT_5_1020) hT_5_1030) hT_5_1040) hT_5_1050) hT_5_1060) hT_5_1070) hT_5_1080)
theorem hT_6_0 : span (ZT 6) 10 0 = true := by decide +kernel
theorem hT_6_10 : span (ZT 6) 10 10 = true := by decide +kernel
theorem hT_6_20 : span (ZT 6) 10 20 = true := by decide +kernel
theorem hT_6_30 : span (ZT 6) 10 30 = true := by decide +kernel
theorem hT_6_40 : span (ZT 6) 10 40 = true := by decide +kernel
theorem hT_6_50 : span (ZT 6) 10 50 = true := by decide +kernel
theorem hT_6_60 : span (ZT 6) 10 60 = true := by decide +kernel
theorem hT_6_70 : span (ZT 6) 10 70 = true := by decide +kernel
theorem hT_6_80 : span (ZT 6) 10 80 = true := by decide +kernel
theorem hT_6_90 : span (ZT 6) 10 90 = true := by decide +kernel
theorem hT_6_100 : span (ZT 6) 10 100 = true := by decide +kernel
theorem hT_6_110 : span (ZT 6) 10 110 = true := by decide +kernel
theorem hT_6_120 : span (ZT 6) 10 120 = true := by decide +kernel
theorem hT_6_130 : span (ZT 6) 10 130 = true := by decide +kernel
theorem hT_6_140 : span (ZT 6) 10 140 = true := by decide +kernel
theorem hT_6_150 : span (ZT 6) 10 150 = true := by decide +kernel
theorem hT_6_160 : span (ZT 6) 10 160 = true := by decide +kernel
theorem hT_6_170 : span (ZT 6) 10 170 = true := by decide +kernel
theorem hT_6_180 : span (ZT 6) 10 180 = true := by decide +kernel
theorem hT_6_190 : span (ZT 6) 10 190 = true := by decide +kernel
theorem hT_6_200 : span (ZT 6) 10 200 = true := by decide +kernel
theorem hT_6_210 : span (ZT 6) 10 210 = true := by decide +kernel
theorem hT_6_220 : span (ZT 6) 10 220 = true := by decide +kernel
theorem hT_6_230 : span (ZT 6) 10 230 = true := by decide +kernel
theorem hT_6_240 : span (ZT 6) 10 240 = true := by decide +kernel
theorem hT_6_250 : span (ZT 6) 10 250 = true := by decide +kernel
theorem hT_6_260 : span (ZT 6) 10 260 = true := by decide +kernel
theorem hT_6_270 : span (ZT 6) 10 270 = true := by decide +kernel
theorem hT_6_280 : span (ZT 6) 10 280 = true := by decide +kernel
theorem hT_6_290 : span (ZT 6) 10 290 = true := by decide +kernel
theorem hT_6_300 : span (ZT 6) 10 300 = true := by decide +kernel
theorem hT_6_310 : span (ZT 6) 10 310 = true := by decide +kernel
theorem hT_6_320 : span (ZT 6) 10 320 = true := by decide +kernel
theorem hT_6_330 : span (ZT 6) 10 330 = true := by decide +kernel
theorem hT_6_340 : span (ZT 6) 10 340 = true := by decide +kernel
theorem hT_6_350 : span (ZT 6) 10 350 = true := by decide +kernel
theorem hT_6_360 : span (ZT 6) 10 360 = true := by decide +kernel
theorem hT_6_370 : span (ZT 6) 10 370 = true := by decide +kernel
theorem hT_6_380 : span (ZT 6) 10 380 = true := by decide +kernel
theorem hT_6_390 : span (ZT 6) 10 390 = true := by decide +kernel
theorem hT_6_400 : span (ZT 6) 10 400 = true := by decide +kernel
theorem hT_6_410 : span (ZT 6) 10 410 = true := by decide +kernel
theorem hT_6_420 : span (ZT 6) 10 420 = true := by decide +kernel
theorem hT_6_430 : span (ZT 6) 10 430 = true := by decide +kernel
theorem hT_6_440 : span (ZT 6) 10 440 = true := by decide +kernel
theorem hT_6_450 : span (ZT 6) 10 450 = true := by decide +kernel
theorem hT_6_460 : span (ZT 6) 10 460 = true := by decide +kernel
theorem hT_6_470 : span (ZT 6) 10 470 = true := by decide +kernel
theorem hT_6_480 : span (ZT 6) 10 480 = true := by decide +kernel
theorem hT_6_490 : span (ZT 6) 10 490 = true := by decide +kernel
theorem hT_6_500 : span (ZT 6) 10 500 = true := by decide +kernel
theorem hT_6_510 : span (ZT 6) 10 510 = true := by decide +kernel
theorem hT_6_520 : span (ZT 6) 10 520 = true := by decide +kernel
theorem hT_6_530 : span (ZT 6) 10 530 = true := by decide +kernel
theorem hT_6_540 : span (ZT 6) 10 540 = true := by decide +kernel
theorem hT_6_550 : span (ZT 6) 10 550 = true := by decide +kernel
theorem hT_6_560 : span (ZT 6) 10 560 = true := by decide +kernel
theorem hT_6_570 : span (ZT 6) 10 570 = true := by decide +kernel
theorem hT_6_580 : span (ZT 6) 10 580 = true := by decide +kernel
theorem hT_6_590 : span (ZT 6) 10 590 = true := by decide +kernel
theorem hT_6_600 : span (ZT 6) 10 600 = true := by decide +kernel
theorem hT_6_610 : span (ZT 6) 10 610 = true := by decide +kernel
theorem hT_6_620 : span (ZT 6) 10 620 = true := by decide +kernel
theorem hT_6_630 : span (ZT 6) 10 630 = true := by decide +kernel
theorem hT_6_640 : span (ZT 6) 10 640 = true := by decide +kernel
theorem hT_6_650 : span (ZT 6) 10 650 = true := by decide +kernel
theorem hT_6_660 : span (ZT 6) 10 660 = true := by decide +kernel
theorem hT_6_670 : span (ZT 6) 10 670 = true := by decide +kernel
theorem hT_6_680 : span (ZT 6) 10 680 = true := by decide +kernel
theorem hT_6_690 : span (ZT 6) 10 690 = true := by decide +kernel
theorem hT_6_700 : span (ZT 6) 10 700 = true := by decide +kernel
theorem hT_6_710 : span (ZT 6) 10 710 = true := by decide +kernel
theorem hT_6_720 : span (ZT 6) 10 720 = true := by decide +kernel
theorem hT_6_730 : span (ZT 6) 10 730 = true := by decide +kernel
theorem hT_6_740 : span (ZT 6) 10 740 = true := by decide +kernel
theorem hT_6_750 : span (ZT 6) 10 750 = true := by decide +kernel
theorem hT_6_760 : span (ZT 6) 10 760 = true := by decide +kernel
theorem hT_6_770 : span (ZT 6) 6 770 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem zT_6 : span (ZT 6) 776 0 = true := (@span_join (ZT 6) 770 0 6 (@span_join (ZT 6) 760 0 10 (@span_join (ZT 6) 750 0 10 (@span_join (ZT 6) 740 0 10 (@span_join (ZT 6) 730 0 10 (@span_join (ZT 6) 720 0 10 (@span_join (ZT 6) 710 0 10 (@span_join (ZT 6) 700 0 10 (@span_join (ZT 6) 690 0 10 (@span_join (ZT 6) 680 0 10 (@span_join (ZT 6) 670 0 10 (@span_join (ZT 6) 660 0 10 (@span_join (ZT 6) 650 0 10 (@span_join (ZT 6) 640 0 10 (@span_join (ZT 6) 630 0 10 (@span_join (ZT 6) 620 0 10 (@span_join (ZT 6) 610 0 10 (@span_join (ZT 6) 600 0 10 (@span_join (ZT 6) 590 0 10 (@span_join (ZT 6) 580 0 10 (@span_join (ZT 6) 570 0 10 (@span_join (ZT 6) 560 0 10 (@span_join (ZT 6) 550 0 10 (@span_join (ZT 6) 540 0 10 (@span_join (ZT 6) 530 0 10 (@span_join (ZT 6) 520 0 10 (@span_join (ZT 6) 510 0 10 (@span_join (ZT 6) 500 0 10 (@span_join (ZT 6) 490 0 10 (@span_join (ZT 6) 480 0 10 (@span_join (ZT 6) 470 0 10 (@span_join (ZT 6) 460 0 10 (@span_join (ZT 6) 450 0 10 (@span_join (ZT 6) 440 0 10 (@span_join (ZT 6) 430 0 10 (@span_join (ZT 6) 420 0 10 (@span_join (ZT 6) 410 0 10 (@span_join (ZT 6) 400 0 10 (@span_join (ZT 6) 390 0 10 (@span_join (ZT 6) 380 0 10 (@span_join (ZT 6) 370 0 10 (@span_join (ZT 6) 360 0 10 (@span_join (ZT 6) 350 0 10 (@span_join (ZT 6) 340 0 10 (@span_join (ZT 6) 330 0 10 (@span_join (ZT 6) 320 0 10 (@span_join (ZT 6) 310 0 10 (@span_join (ZT 6) 300 0 10 (@span_join (ZT 6) 290 0 10 (@span_join (ZT 6) 280 0 10 (@span_join (ZT 6) 270 0 10 (@span_join (ZT 6) 260 0 10 (@span_join (ZT 6) 250 0 10 (@span_join (ZT 6) 240 0 10 (@span_join (ZT 6) 230 0 10 (@span_join (ZT 6) 220 0 10 (@span_join (ZT 6) 210 0 10 (@span_join (ZT 6) 200 0 10 (@span_join (ZT 6) 190 0 10 (@span_join (ZT 6) 180 0 10 (@span_join (ZT 6) 170 0 10 (@span_join (ZT 6) 160 0 10 (@span_join (ZT 6) 150 0 10 (@span_join (ZT 6) 140 0 10 (@span_join (ZT 6) 130 0 10 (@span_join (ZT 6) 120 0 10 (@span_join (ZT 6) 110 0 10 (@span_join (ZT 6) 100 0 10 (@span_join (ZT 6) 90 0 10 (@span_join (ZT 6) 80 0 10 (@span_join (ZT 6) 70 0 10 (@span_join (ZT 6) 60 0 10 (@span_join (ZT 6) 50 0 10 (@span_join (ZT 6) 40 0 10 (@span_join (ZT 6) 30 0 10 (@span_join (ZT 6) 20 0 10 (@span_join (ZT 6) 10 0 10 hT_6_0 hT_6_10) hT_6_20) hT_6_30) hT_6_40) hT_6_50) hT_6_60) hT_6_70) hT_6_80) hT_6_90) hT_6_100) hT_6_110) hT_6_120) hT_6_130) hT_6_140) hT_6_150) hT_6_160) hT_6_170) hT_6_180) hT_6_190) hT_6_200) hT_6_210) hT_6_220) hT_6_230) hT_6_240) hT_6_250) hT_6_260) hT_6_270) hT_6_280) hT_6_290) hT_6_300) hT_6_310) hT_6_320) hT_6_330) hT_6_340) hT_6_350) hT_6_360) hT_6_370) hT_6_380) hT_6_390) hT_6_400) hT_6_410) hT_6_420) hT_6_430) hT_6_440) hT_6_450) hT_6_460) hT_6_470) hT_6_480) hT_6_490) hT_6_500) hT_6_510) hT_6_520) hT_6_530) hT_6_540) hT_6_550) hT_6_560) hT_6_570) hT_6_580) hT_6_590) hT_6_600) hT_6_610) hT_6_620) hT_6_630) hT_6_640) hT_6_650) hT_6_660) hT_6_670) hT_6_680) hT_6_690) hT_6_700) hT_6_710) hT_6_720) hT_6_730) hT_6_740) hT_6_750) hT_6_760) hT_6_770)
theorem hT_7_0 : span (ZT 7) 10 0 = true := by decide +kernel
theorem hT_7_10 : span (ZT 7) 10 10 = true := by decide +kernel
theorem hT_7_20 : span (ZT 7) 10 20 = true := by decide +kernel
theorem hT_7_30 : span (ZT 7) 10 30 = true := by decide +kernel
theorem hT_7_40 : span (ZT 7) 10 40 = true := by decide +kernel
theorem hT_7_50 : span (ZT 7) 4 50 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem zT_7 : span (ZT 7) 54 0 = true := (@span_join (ZT 7) 50 0 4 (@span_join (ZT 7) 40 0 10 (@span_join (ZT 7) 30 0 10 (@span_join (ZT 7) 20 0 10 (@span_join (ZT 7) 10 0 10 hT_7_0 hT_7_10) hT_7_20) hT_7_30) hT_7_40) hT_7_50)
theorem hT_8_0 : span (ZT 8) 1 0 = true := by decide +kernel
set_option maxRecDepth 200000 in
theorem zT_8 : span (ZT 8) 1 0 = true := hT_8_0
theorem baseT : ∀ s : ℕ, HasCircuitSize 6 fT s → 9 ≤ s := by
  refine prove_base 6 50 8 fT rowsT xsT [] NNT HTT PTT
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok zT_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_7 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_8 i (Nat.zero_le i) hi
    )
def upperT : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [2, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [11, 13]⟩]
theorem upperT_ok : ∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨upperT, 14⟩ (List.ofFn x) = fT x := by
  decide +kernel
end PEqualNP.Outside.L_meta_15853

open PEqualNP.Outside.L_meta_15853 in
theorem PEqualNP.Outside.L_meta_15853 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004178600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4004178600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  have hM := baseT s hs
  refine ⟨⟨upperT, 14⟩, ?_, ?_, fun x => upperT_ok x⟩
  · intro g hg
    simp only [upperT, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · show upperT.length ≤ s
    simp only [upperT, List.length_cons, List.length_nil]
    omega
