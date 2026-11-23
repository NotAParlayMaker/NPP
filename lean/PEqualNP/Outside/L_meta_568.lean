import Mathlib
import PEqualNP.Defs

namespace Gap568

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
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

theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [normGate]

theorem normGate_eq_self_of_ne_not (g : Gate) (h : g.op ≠ GateOp.not) :
    normGate g = g := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp_all [normGate]

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

def Reads (a : ℕ) (g : Gate) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some a ∨ g.op ≠ GateOp.not ∧ a ∈ g.inputs

theorem reads_iff (a : ℕ) (g : Gate) : Reads a g ↔ a ∈ (normGate g).inputs := by
  obtain ⟨o, l⟩ := g
  cases o <;> cases l <;> simp [Reads, normGate, eq_comm]

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

theorem wires_gate_eval (m : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = m)
    (j : Fin C.gates.length)
    (hlt : ∀ a, Reads a (C.gates.get j) → a < m + j.val) :
    (C.wires x).getD (m + j.val) false =
      (normGate (C.gates.get j)).op.eval
        ((normGate (C.gates.get j)).inputs.map fun a => (C.wires x).getD a false) := by
  set g₀ := C.gates.get j with hg₀
  have hgj : C.gates[j.val]? = some g₀ := by
    rw [hg₀]
    simp [List.getElem?_eq_getElem j.isLt]
  obtain ⟨pre, post, hsp, hpl⟩ := split_at C.gates j.val g₀ hgj
  set Wpre := wiresFrom pre x with hWpre
  have hlen : Wpre.length = m + j.val := by rw [hWpre, length_wiresFrom, hx, hpl]
  have hw : C.wires x = wiresFrom (g₀ :: post) Wpre := by
    rw [wires_eq, hsp, wiresFrom_append]
  have hw2 : C.wires x =
      wiresFrom post (Wpre ++ [g₀.op.eval (g₀.inputs.map fun a => Wpre.getD a false)]) := hw
  have hlhs : (C.wires x).getD (m + j.val) false =
      (normGate g₀).op.eval ((normGate g₀).inputs.map fun a => Wpre.getD a false) := by
    rw [hw2, getD_wiresFrom post _ (m + j.val) (by simp [hlen]), ← hlen, getD_snoc_eq,
      ← normGate_eval]
  rw [hlhs]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal : a < Wpre.length := by
    rw [hlen]
    exact hlt a ((reads_iff a g₀).2 ha)
  rw [hw, getD_wiresFrom (g₀ :: post) Wpre a hal]

abbrev Stat := Sum Bool ℕ

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
      have h2 := elimStep_none n acc g (hok g List.mem_cons_self) k hkg c hc
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

def hit (k : ℕ) (g : Gate) : Bool := decide (k ∈ g.inputs)

theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + gs.countP (hit k) ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    obtain ⟨c, hc⟩ := hc
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    change (elim n gs (elimStep n acc g)).2.length + _ ≤ _
    rw [List.countP_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · have h2 := elimStep_none n acc g (hok g List.mem_cons_self) k hkg c hc
      simp only [hit, hkg, decide_true, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hit, hkg, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]
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
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_ext r.1.toList w'
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

def seed (m h : ℕ) : List Stat :=
  List.ofFn fun i : Fin m => if i.val = h then Sum.inl false else Sum.inr i.val

theorem seed_inv (w : List Bool) (m h : ℕ) (hw : w.length = m)
    (hz : w.getD h false = false) : Inv m w w (seed m h, []) := by
  refine ⟨by simp [seed, hw], fun i => ?_⟩
  by_cases hi : i < m
  · by_cases e : i = h
    · subst i; simpa [seed, hi, Stat.Valid, Stat.val] using hz
    · simp [seed, hi, e, Stat.Valid, Stat.val, wiresFrom]
  · have : m ≤ i := by omega
    simpa [seed, hi, Stat.Valid, Stat.val] using (List.getD_eq_default w false (by omega : w.length ≤ i))

def finish (h : ℕ) : Stat → Gate
  | Sum.inl true => ⟨GateOp.and, []⟩
  | Sum.inl false => ⟨GateOp.or, [h]⟩
  | Sum.inr j => ⟨GateOp.or, [h, j]⟩

theorem finish_ok (h : ℕ) (s : Stat) : Ok (finish h s) := by
  cases s with
  | inl b => cases b <;> simp [finish, Ok]
  | inr j => simp [finish, Ok]

theorem finish_eval (w : List Bool) (h : ℕ) (s : Stat) :
    (wiresFrom [finish h s] w).getD w.length false = (w.getD h false || s.val w) := by
  cases s with
  | inl b => cases b <;> simp [finish, wiresFrom, GateOp.eval, Stat.val]
  | inr j => simp [finish, wiresFrom, GateOp.eval, Stat.val]

theorem minimal_output_last (m : ℕ) (C : Circuit)
    (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x')
    (hpos : 0 < C.gates.length) :
    C.output = m + (C.gates.length - 1) := by
  have hlt : C.output < m + C.gates.length := by
    by_contra hge
    obtain ⟨x, x', hne⟩ := hnc
    apply hne
    have h1 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      rw [wires_eq, length_wiresFrom]; simp
    have h2 : (C.wires (List.ofFn x')).length = m + C.gates.length := by
      rw [wires_eq, length_wiresFrom]; simp
    show (C.wires (List.ofFn x)).getD C.output false =
      (C.wires (List.ofFn x')).getD C.output false
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  by_contra hne_last
  have hout_lt : C.output < m + (C.gates.length - 1) := by omega
  let pre := C.gates.take (C.gates.length - 1)
  let rest := C.gates.drop (C.gates.length - 1)
  have hsp : pre ++ rest = C.gates := List.take_append_drop ..
  have hpl : pre.length = C.gates.length - 1 := by simp [pre]
  let D : Circuit := ⟨pre, C.output⟩
  have hDok : FanInTwo D := fun g hg => hmin.1 g (hsp ▸ List.mem_append_left _ hg)
  have hDeq : circuitFun m D = circuitFun m C := by
    funext x
    show (wiresFrom pre (List.ofFn x)).getD C.output false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    rw [← hsp, wiresFrom_append, getD_wiresFrom rest _ C.output
      (by rw [length_wiresFrom]; simp [hpl]; omega)]
  have hsz := hmin.2 D hDok hDeq
  change C.gates.length ≤ pre.length at hsz
  omega

theorem minimal_reads_lt (m : ℕ) (C : Circuit)
    (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x')
    (j : Fin C.gates.length) (a : ℕ) (hread : Reads a (C.gates.get j)) :
    a < m + j.val := by
  by_contra hge
  set gs := C.gates.map normGate with hgs
  have hgl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g' ∈ gs, NOk g' := by
    intro g' hg'
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg'
    exact normGate_nok g1 (hmin.1 g1 hg1)
  set g := normGate (C.gates.get j) with hg
  have hgj : gs[j.val]? = some g := by
    rw [hgs, hg]
    simp [List.getElem?_eq_getElem j.isLt]
  obtain ⟨pre, post, hsp, hpl⟩ := split_at gs j.val g hgj
  have hgn : NOk g := hnok g (by rw [hsp]; simp)
  have hpreok : ∀ g' ∈ pre, Ok g' := fun g' h =>
    (hnok g' (by rw [hsp]; exact List.mem_append_left _ h)).1
  have hpostok : ∀ g' ∈ post, Ok g' := fun g' h =>
    (hnok g' (by rw [hsp]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h))).1
  let s_pre : List Stat := List.ofFn fun i : Fin (m + j.val) => Sum.inr i.val
  let B := elimStep m (s_pre, pre) g
  let acc := elim m post B
  have ha_mem : a ∈ g.inputs := (reads_iff a (C.gates.get j)).1 hread
  have ha_def : s_pre.getD a (Sum.inl false) = Sum.inl false :=
    List.getD_eq_default _ _ (by simp [s_pre]; omega)
  have hB2 : B.2.length = pre.length :=
    elimStep_none m (s_pre, pre) g hgn a ha_mem false ha_def
  have hacc2 : acc.2.length ≤ pre.length + post.length := by
    have h1 : acc.2.length ≤ B.2.length + post.length := elim_len m post B
    omega
  have hlen : gs.length = pre.length + post.length + 1 := by
    rw [hsp]; simp only [List.length_append, List.length_cons]; omega
  have hinv_pre : ∀ x : Fin m → Bool,
      Inv m (List.ofFn x) (wiresFrom pre (List.ofFn x)) (s_pre, pre) := by
    intro x
    have hwl : (wiresFrom pre (List.ofFn x)).length = m + j.val := by
      rw [length_wiresFrom]; simp [hpl]
    refine ⟨by simp [s_pre, hwl], ?_⟩
    intro i
    by_cases hi : i < m + j.val
    · simp [s_pre, hi, Stat.Valid, Stat.val, hpl]
    · rw [List.getD_eq_default s_pre _ (by simp [s_pre]; omega),
        List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin m → Bool, Inv m (List.ofFn x) (C.wires (List.ofFn x)) acc := by
    intro x
    have hw : C.wires (List.ofFn x) = wiresFrom (g :: post) (wiresFrom pre (List.ofFn x)) := by
      rw [wires_eq, ← wiresFrom_norm, ← hgs, hsp, wiresFrom_append]
    rw [hw]
    exact inv_elim m (List.ofFn x) (by simp) (g :: post) (wiresFrom pre (List.ofFn x))
      (s_pre, pre) (fun g' hg' => by
        rcases List.mem_cons.1 hg' with rfl | h
        · exact hgn.1
        · exact hpostok g' h)
      (hinv_pre x)
  have hval : ∀ x : Fin m → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        circuitFun m C x := fun x => ((hinv x).2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    apply hne
    rw [← hval x, ← hval x', hst]; rfl
  | inr out' =>
    let D : Circuit := ⟨acc.2, out'⟩
    have hDok : FanInTwo D := elim_ok m (g :: post) (s_pre, pre) hpreok
    have hDeq : circuitFun m D = circuitFun m C := by
      funext x
      have hx := hval x
      rw [hst] at hx
      exact hx
    have hsz := hmin.2 D hDok hDeq
    change C.gates.length ≤ acc.2.length at hsz
    omega

def shiftWire (k w : ℕ) : ℕ := if w < k then w else w - 1

def shiftGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftWire k)⟩

def ShiftInv (k : ℕ) (W W' : List Bool) : Prop :=
  k < W.length ∧ W'.length + 1 = W.length ∧
    ∀ w : ℕ, w ≠ k → W'.getD (shiftWire k w) false = W.getD w false

theorem shift_step (k : ℕ) (W W' : List Bool) (g : Gate)
    (hinv : ShiftInv k W W') (hno : k ∉ g.inputs) :
    ShiftInv k
      (W ++ [g.op.eval (g.inputs.map fun a => W.getD a false)])
      (W' ++ [(shiftGate k g).op.eval ((shiftGate k g).inputs.map fun a => W'.getD a false)]) := by
  obtain ⟨hk, hl, heq⟩ := hinv
  have hv : (shiftGate k g).op.eval ((shiftGate k g).inputs.map fun a => W'.getD a false) =
      g.op.eval (g.inputs.map fun a => W.getD a false) := by
    simp only [shiftGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact heq a (fun e => hno (e ▸ ha))
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro w hw
  rw [hv]
  by_cases hlt : w < k
  · simp only [shiftWire, hlt, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    simpa [shiftWire, hlt] using heq w hw
  · simp only [shiftWire, hlt, ite_false]
    rcases Nat.lt_trichotomy w W.length with h1 | h1 | h1
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ h1]
      simpa [shiftWire, hlt] using heq w hw
    · have h2 : w - 1 = W'.length := by omega
      rw [h2, h1, getD_snoc_eq, getD_snoc_eq]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem shift_fold (k : ℕ) (gs : List Gate) : ∀ (W W' : List Bool),
    (∀ g ∈ gs, k ∉ g.inputs) → ShiftInv k W W' →
    ShiftInv k (wiresFrom gs W) (wiresFrom (gs.map (shiftGate k)) W') := by
  induction gs with
  | nil => intro W W' _ h; exact h
  | cons g gs ih =>
    intro W W' hno hinv
    exact ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
      (shift_step k W W' g hinv (hno g List.mem_cons_self))

theorem shift_init (k : ℕ) (Wpre : List Bool) (v : Bool) (hl : Wpre.length = k) :
    ShiftInv k (Wpre ++ [v]) Wpre := by
  refine ⟨by simp [hl], by simp, ?_⟩
  intro w hw
  by_cases hlt : w < k
  · simp only [shiftWire, hlt, ite_true]
    rw [List.getD_append _ _ _ _ (by omega)]
  · simp only [shiftWire, hlt, ite_false]
    rw [List.getD_eq_default Wpre _ (by omega), List.getD_eq_default (Wpre ++ [v]) _ (by simp; omega)]

theorem minimal_dead_gate (m : ℕ) (C : Circuit) (hmin : IsMinimalCircuit m C)
    (j : Fin C.gates.length) (hne : C.output ≠ m + j.val) :
    ∃ j' : Fin C.gates.length, j.val < j'.val ∧ Reads (m + j.val) (C.gates.get j') := by
  by_contra! hno
  set gs := C.gates.map normGate with hgs
  have hgl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g' ∈ gs, NOk g' := by
    intro g' hg'
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg'
    exact normGate_nok g1 (hmin.1 g1 hg1)
  set g := normGate (C.gates.get j) with hg
  have hgj : gs[j.val]? = some g := by
    rw [hgs, hg]
    simp [List.getElem?_eq_getElem j.isLt]
  obtain ⟨pre, post, hsp, hpl⟩ := split_at gs j.val g hgj
  let k := m + j.val
  have hno_post : ∀ g' ∈ post, k ∉ g'.inputs := by
    intro g' hg' hk
    obtain ⟨r, rfl⟩ := List.mem_iff_get.1 hg'
    have hidx : j.val + 1 + r.val < C.gates.length := by
      have : gs.length = pre.length + 1 + post.length := by rw [hsp]; simp; omega
      omega
    let j' : Fin C.gates.length := ⟨j.val + 1 + r.val, hidx⟩
    have heq : post.get r = normGate (C.gates.get j') := by
      have h1 : gs[j.val + 1 + r.val]? = some (post.get r) := by
        rw [hsp, List.getElem?_append_right (by omega)]
        have : j.val + 1 + r.val - pre.length = r.val + 1 := by omega
        rw [this]
        simp [List.getElem?_eq_getElem r.isLt]
      have h2 : gs[j.val + 1 + r.val]? = some (normGate (C.gates.get j')) := by
        rw [hgs]
        simp [j', List.getElem?_eq_getElem hidx]
      exact Option.some.inj (h1.symm.trans h2)
    rw [heq] at hk
    exact hno j' (by simp [j']; omega) ((reads_iff k (C.gates.get j')).2 hk)
  let D : Circuit := ⟨pre ++ post.map (shiftGate k), shiftWire k C.output⟩
  have hDok : FanInTwo D := by
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact (hnok g' (by rw [hsp]; exact List.mem_append_left _ h1)).1
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
      have hok0 := (hnok g0 (by rw [hsp]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))).1
      exact ⟨hok0.1, by simpa [shiftGate] using hok0.2⟩
  have hDeq : circuitFun m D = circuitFun m C := by
    funext x
    let Wpre := wiresFrom pre (List.ofFn x)
    have hWlen : Wpre.length = k := by simp [Wpre, length_wiresFrom, hpl, k]
    have hC : C.wires (List.ofFn x) =
        wiresFrom post (Wpre ++ [g.op.eval (g.inputs.map fun a => Wpre.getD a false)]) := by
      rw [wires_eq, ← wiresFrom_norm, ← hgs, hsp, wiresFrom_append]; rfl
    have hD : D.wires (List.ofFn x) = wiresFrom (post.map (shiftGate k)) Wpre := by
      rw [wires_eq]; exact wiresFrom_append pre (post.map (shiftGate k)) (List.ofFn x)
    have hs := shift_fold k post _ Wpre hno_post
      (shift_init k Wpre (g.op.eval (g.inputs.map fun a => Wpre.getD a false)) hWlen)
    show (D.wires (List.ofFn x)).getD (shiftWire k C.output) false =
      (C.wires (List.ofFn x)).getD C.output false
    rw [hD, hC]
    exact hs.2.2 C.output hne
  have hsz := hmin.2 D hDok hDeq
  have hlen : gs.length = pre.length + post.length + 1 := by
    rw [hsp]; simp only [List.length_append, List.length_cons]; omega
  change C.gates.length ≤ (pre ++ post.map (shiftGate k)).length at hsz
  simp only [List.length_append, List.length_map] at hsz
  omega

theorem absorb_step (m : ℕ) (C : Circuit) (h : ℕ)
    (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x')
    (hlt : h < m + C.gates.length)
    (habs : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD h false = true →
      circuitFun m C x = true)
    (hneed : ∃ j : Fin C.gates.length, Reads h (C.gates.get j)) :
    ∃ j : Fin C.gates.length,
      h < m + j.val ∧
      (∀ j' : Fin C.gates.length, Reads h (C.gates.get j') → j' = j) ∧
      (C.gates.get j).op = GateOp.or ∧
      (C.gates.get j).inputs.length = 2 ∧
      h ∈ (C.gates.get j).inputs ∧
      ∃ w ∈ (C.gates.get j).inputs, w ≠ h ∧ w < m + j.val := by
  obtain ⟨j, hjread⟩ := hneed
  have hjlt : h < m + j.val := minimal_reads_lt m C hmin hnc j h hjread
  let t := h + 1 - m
  let pre := C.gates.take t
  let rest := C.gates.drop t
  have hsplit : pre ++ rest = C.gates := List.take_append_drop ..
  have hpl : pre.length = t := by simp [pre, t]; omega
  let M := m + pre.length
  have hM : h < M := by dsimp [M]; omega
  have hpre_le_j : pre.length ≤ j.val := by omega
  have hpre_lt : pre.length < C.gates.length := by omega
  have hpreOk : ∀ g' ∈ pre, Ok g' := fun g' hg' => hmin.1 g' (hsplit ▸ List.mem_append_left _ hg')
  have hrestOk : ∀ g' ∈ rest, Ok g' := fun g' hg' => hmin.1 g' (hsplit ▸ List.mem_append_right _ hg')
  set gs_rest := rest.map normGate with hgs_rest
  have hgs_len : gs_rest.length = rest.length := by simp [hgs_rest]
  have hnok_rest : ∀ g' ∈ gs_rest, NOk g' := by
    intro g' hg'
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg'
    exact normGate_nok g1 (hrestOk g1 hg1)
  let init : List Stat × List Gate := (seed M h, [])
  set pass := elim M gs_rest init with hpass
  let s := pass.1.getD C.output (Sum.inl false)
  let D : Circuit := ⟨(pre ++ pass.2) ++ [finish h s], M + pass.2.length⟩
  have hDok : FanInTwo D := by
    intro g' hg'
    change g' ∈ (pre ++ pass.2) ++ [finish h s] at hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with ((hp | hr) | rfl)
    · exact hpreOk g' hp
    · exact elim_ok M gs_rest init (by simp [init]) g' hr
    · exact finish_ok h s
  have hDeval : ∀ x : Fin m → Bool,
      circuitFun m C x =
        ((wiresFrom pre (List.ofFn x)).getD h false ||
          s.val (wiresFrom pass.2 (wiresFrom pre (List.ofFn x)))) := by
    intro x
    let y := List.ofFn x
    let w := wiresFrom pre y
    let v := wiresFrom pass.2 w
    have lw : w.length = M := by simp [w, y, length_wiresFrom, M]
    have hh : h < w.length := lw ▸ hM
    have hold : C.wires y = wiresFrom rest w := by rw [wires_eq, ← hsplit, wiresFrom_append]
    have horigH : (C.wires y).getD h false = w.getD h false := by
      rw [hold, getD_wiresFrom _ _ _ hh]
    cases hc : w.getD h false with
    | true => simpa using habs x (horigH.trans hc)
    | false =>
      have hi := inv_elim M w lw gs_rest w init
        (fun g' hg' => (hnok_rest g' hg').1) (seed_inv w M h lw hc)
      have eq := (hi.2 C.output).2
      rw [hgs_rest, wiresFrom_norm, ← hold] at eq
      simpa [s, v, hpass, circuitFun, Circuit.eval, y] using eq.symm
  have hDeq : circuitFun m D = circuitFun m C := by
    funext x
    let y := List.ofFn x
    let w := wiresFrom pre y
    let v := wiresFrom pass.2 w
    have lw : w.length = M := by simp [w, y, length_wiresFrom, M]
    have lv : v.length = M + pass.2.length := by simp [v, length_wiresFrom, lw]
    have hh : h < w.length := lw ▸ hM
    have hout : circuitFun m D x = (w.getD h false || s.val v) := by
      change (wiresFrom ((pre ++ pass.2) ++ [finish h s]) y).getD (M + pass.2.length) false = _
      rw [wiresFrom_append, wiresFrom_append]
      change (wiresFrom [finish h s] v).getD _ false = _
      rw [← lv, finish_eval, getD_wiresFrom _ _ _ hh]
    rw [hout, hDeval x]
  have hsz := hmin.2 D hDok hDeq
  have hC_len : C.gates.length = pre.length + rest.length := by
    rw [← hsplit, List.length_append]
  have hgs_le : gs_rest.length ≤ pass.2.length + 1 := by
    change C.gates.length ≤ ((pre ++ pass.2) ++ [finish h s]).length at hsz
    simp only [List.length_append, List.length_cons, List.length_nil] at hsz
    omega
  have hinit_h : init.1.getD h (Sum.inl false) = Sum.inl false := by
    simp [init, seed, hM]
  have hcount : gs_rest.countP (hit h) ≤ 1 := by
    have hel := elim_count M h gs_rest init hnok_rest (by simp [init, seed, hM]) ⟨false, hinit_h⟩
    change pass.2.length + gs_rest.countP (hit h) ≤ 0 + gs_rest.length at hel
    omega
  have huniq : ∀ j' : Fin C.gates.length, Reads h (C.gates.get j') → j' = j := by
    let S := Finset.univ.filter (fun r : Fin gs_rest.length => hit h (gs_rest.get r))
    have hS : S.card ≤ 1 := by
      have e : List.ofFn (fun r : Fin gs_rest.length => gs_rest.get r) = gs_rest := List.ofFn_get _
      rwa [← e, List.countP_ofFn] at hcount
    have toRest : ∀ j' : Fin C.gates.length, Reads h (C.gates.get j') →
        ∃ r : Fin gs_rest.length, r.val = j'.val - pre.length ∧ r ∈ S := by
      intro j' hj'
      have hj'lt := minimal_reads_lt m C hmin hnc j' h hj'
      have hidx : j'.val - pre.length < gs_rest.length := by omega
      refine ⟨⟨j'.val - pre.length, hidx⟩, rfl, ?_⟩
      have hget : gs_rest.get ⟨j'.val - pre.length, hidx⟩ = normGate (C.gates.get j') := by
        have h1 : rest[j'.val - pre.length]? = some (C.gates.get j') := by
          have hC : (pre ++ rest)[j'.val]? = some (C.gates.get j') := by
            rw [hsplit]; simp
          rw [List.getElem?_append_right (by omega)] at hC
          exact hC
        have h2 : gs_rest[j'.val - pre.length]? = some (normGate (C.gates.get j')) := by
          rw [hgs_rest, List.getElem?_map, h1]; rfl
        have h3 : gs_rest[j'.val - pre.length]? = some (gs_rest.get ⟨j'.val - pre.length, hidx⟩) := by
          simp
        exact Option.some.inj (h3.symm.trans h2)
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hget, hit, decide_eq_true_eq]
      exact (reads_iff h (C.gates.get j')).1 hj'
    intro j' hj'
    obtain ⟨r', hr'v, hr'S⟩ := toRest j' hj'
    obtain ⟨r, hrv, hrS⟩ := toRest j hjread
    have hr_eq : r' = r := Finset.card_le_one.mp hS r' hr'S r hrS
    have hj'lt := minimal_reads_lt m C hmin hnc j' h hj'
    apply Fin.ext
    have : r'.val = r.val := congrArg Fin.val hr_eq
    omega
  set g₀ := C.gates.get j with hg₀
  set g := normGate g₀ with hg
  have hng : h ∈ g.inputs := (reads_iff h g₀).1 hjread
  let p := j.val - pre.length
  have hp_lt : p < gs_rest.length := by omega
  have hgp : gs_rest[p]? = some g := by
    have hC : (pre ++ rest)[j.val]? = some g₀ := by rw [hsplit, hg₀]; simp
    rw [List.getElem?_append_right hpre_le_j] at hC
    rw [hgs_rest, List.getElem?_map, hC]; rfl
  obtain ⟨mid, tail, hsp_rest, hmid_len⟩ := split_at gs_rest p g hgp
  have hgn : NOk g := hnok_rest g (by rw [hsp_rest]; simp)
  have htailn : ∀ g' ∈ tail, NOk g' := fun g' hg' =>
    hnok_rest g' (by rw [hsp_rest]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg'))
  set A := elim M mid init with hA
  set B := elimStep M A g with hB
  have hpass_eq : pass = elim M tail B := by
    rw [hpass, hsp_rest, elim_append, elim_cons]
  have hAh : A.1.getD h (Sum.inl false) = Sum.inl false := by
    rw [hA, elim_getD M h _ mid init (by simp [init, seed, hM])]
    exact hinit_h
  have hAl : A.1.length = m + j.val := by
    rw [hA, elim_fst_len]
    simp only [init, seed, List.length_ofFn, hmid_len, M, p]
    omega
  have hA2 : A.2.length ≤ mid.length := by
    have := elim_len M mid init
    simpa [init] using this
  have hB2 : B.2.length = A.2.length := elimStep_none M A g hgn h hng false hAh
  have hBl : B.1.length = m + j.val + 1 := by
    simp [hB, elimStep, hAl]
  have hgs_split_len : gs_rest.length = mid.length + tail.length + 1 := by
    rw [hsp_rest]; simp only [List.length_append, List.length_cons]; omega
  have hsg_not_const : ∀ c : Bool, B.1.getD (m + j.val) (Sum.inl false) ≠ Sum.inl c := by
    intro c hc
    by_cases htail_hit : ∃ g' ∈ tail, (m + j.val) ∈ g'.inputs
    · have a1 : pass.2.length + 1 ≤ B.2.length + tail.length := by
        rw [hpass_eq]
        exact elim_len_lt M (m + j.val) tail B htailn (by rw [hBl]; omega) ⟨c, hc⟩ htail_hit
      omega
    · push Not at htail_hit
      by_cases hout_eq : C.output = m + j.val
      · have hs_eq : s = Sum.inl c := by
          dsimp [s]
          rw [hout_eq, hpass_eq, elim_getD M (m + j.val) _ tail B (by rw [hBl]; omega)]
          exact hc
        cases c with
        | true =>
          obtain ⟨x, x', hne⟩ := hnc
          apply hne
          rw [hDeval x, hDeval x', hs_eq]
          simp [Stat.val]
        | false =>
          let D' : Circuit := ⟨pre, h⟩
          have hD'ok : FanInTwo D' := hpreOk
          have hD'eq : circuitFun m D' = circuitFun m C := by
            funext x
            have hx := hDeval x
            rw [hs_eq] at hx
            simpa [D', circuitFun, Circuit.eval, wires_eq, Stat.val] using hx.symm
          have hsz' := hmin.2 D' hD'ok hD'eq
          change C.gates.length ≤ pre.length at hsz'
          omega
      · obtain ⟨j', hj'gt, hj'read⟩ := minimal_dead_gate m C hmin j hout_eq
        have hidx : j'.val - pre.length - (p + 1) < tail.length := by omega
        have hg'_mem : normGate (C.gates.get j') ∈ tail := by
          have hC : (pre ++ rest)[j'.val]? = some (C.gates.get j') := by
            rw [hsplit]; simp
          rw [List.getElem?_append_right (by omega)] at hC
          have hgr : gs_rest[j'.val - pre.length]? = some (normGate (C.gates.get j')) := by
            rw [hgs_rest, List.getElem?_map, hC]; rfl
          rw [hsp_rest, List.getElem?_append_right (by omega)] at hgr
          have hsub : j'.val - pre.length - mid.length = (j'.val - pre.length - (p + 1)) + 1 := by omega
          rw [hsub] at hgr
          simp only [List.getElem?_cons_succ] at hgr
          exact List.mem_of_getElem? hgr
        exact htail_hit _ hg'_mem ((reads_iff (m + j.val) (C.gates.get j')).1 hj'read)
  have hsimp_not_const : ∀ c : Bool,
      (simplify g.op (M + A.2.length)
        (g.inputs.map fun i => A.1.getD i (Sum.inl false))).2 ≠ Sum.inl c := by
    intro c hc
    apply hsg_not_const c
    show (A.1 ++ [_]).getD (m + j.val) (Sum.inl false) = Sum.inl c
    rw [getD_snoc_len _ _ _ _ hAl]
    exact hc
  have hne_not : g₀.op ≠ GateOp.not := by
    intro hop
    have hop' : g.op = GateOp.not := (normGate_op g₀).trans hop
    have hlen1 : g.inputs.length ≤ 1 := hgn.2 hop'
    rcases hgi : g.inputs with _ | ⟨a, _ | ⟨a', l⟩⟩
    · rw [hgi] at hng; simp at hng
    · rw [hgi] at hng
      have hah : h = a := by simpa using hng
      subst hah
      apply hsimp_not_const true
      simp only [hop', hgi, List.map_cons, List.map_nil, hAh, simplify, simpNot, Bool.not_false]
    · rw [hgi] at hlen1; simp at hlen1
  have hgeq : g = g₀ := normGate_eq_self_of_ne_not g₀ hne_not
  rw [hgeq] at hsimp_not_const hgn hng
  have hop_ao : g₀.op = GateOp.and ∨ g₀.op = GateOp.or := by
    rcases hgn.1.1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hne_not
  have hlen2 : g₀.inputs.length ≤ 2 := hgn.1.2
  refine ⟨j, hjlt, huniq, ?_⟩
  rcases hgi : g₀.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨w, l⟩⟩⟩
  · rw [hgi] at hng; simp at hng
  · rw [hgi] at hng
    have huh : h = u := by simpa using hng
    subst huh
    exfalso
    apply hsimp_not_const false
    rcases hop_ao with hop | hop <;>
      simp only [hop, hgi, List.map_cons, List.map_nil, hAh, simplify, simpAnd, simpOr]
  · rw [hgi] at hng
    have hhuv : h = u ∨ h = v := by simpa using hng
    rcases hhuv with rfl | rfl
    · cases hsv : A.1.getD v (Sum.inl false) with
      | inl d =>
        exfalso
        rcases hop_ao with hop | hop
        · exact hsimp_not_const (false && d)
            (by simp only [hop, hgi, List.map_cons, List.map_nil, hAh, hsv, simplify, simpAnd])
        · exact hsimp_not_const (false || d)
            (by simp only [hop, hgi, List.map_cons, List.map_nil, hAh, hsv, simplify, simpOr])
      | inr w' =>
        have hop_eq : g₀.op = GateOp.or := by
          rcases hop_ao with hop | hop
          · exact absurd
              (by simp only [hop, hgi, List.map_cons, List.map_nil, hAh, hsv, simplify, simpAnd]; rfl)
              (hsimp_not_const false)
          · exact hop
        refine ⟨hop_eq, by simp, by simp, v, by simp, ?_, ?_⟩
        · intro e; rw [e, hAh] at hsv; cases hsv
        · by_contra hge
          have hdef : A.1.getD v (Sum.inl false) = Sum.inl false :=
            List.getD_eq_default _ _ (by omega)
          rw [hdef] at hsv; cases hsv
    · cases hsu : A.1.getD u (Sum.inl false) with
      | inl d =>
        exfalso
        rcases hop_ao with hop | hop
        · exact hsimp_not_const (d && false)
            (by simp only [hop, hgi, List.map_cons, List.map_nil, hAh, hsu, simplify, simpAnd])
        · exact hsimp_not_const (d || false)
            (by simp only [hop, hgi, List.map_cons, List.map_nil, hAh, hsu, simplify, simpOr])
      | inr w' =>
        have hop_eq : g₀.op = GateOp.or := by
          rcases hop_ao with hop | hop
          · exact absurd
              (by simp only [hop, hgi, List.map_cons, List.map_nil, hAh, hsu, simplify, simpAnd]; rfl)
              (hsimp_not_const false)
          · exact hop
        refine ⟨hop_eq, by simp, by simp, u, by simp, ?_, ?_⟩
        · intro e; rw [e, hAh] at hsu; cases hsu
        · by_contra hge
          have hdef : A.1.getD u (Sum.inl false) = Sum.inl false :=
            List.getD_eq_default _ _ (by omega)
          rw [hdef] at hsu; cases hsu
  · rw [hgi] at hlen2; simp at hlen2

theorem getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : Fin m) :
    (List.ofFn x).getD i.val false = x i := by simp

theorem wires_agree_outside (n : ℕ) (C : Circuit) (y : Fin n → Bool)
    (hlt : ∀ (j : Fin C.gates.length) (a : ℕ), Reads a (C.gates.get j) → a < n + 1 + j.val)
    (S : ℕ → Prop) (hnS : S n)
    (hclosed : ∀ j : Fin C.gates.length, ¬ S (n + 1 + j.val) →
      (C.wires (List.ofFn (Fin.snoc y false))).getD (n + 1 + j.val) false =
        (C.wires (List.ofFn (Fin.snoc y true))).getD (n + 1 + j.val) false ∨
      ∀ a, Reads a (C.gates.get j) → ¬ S a) :
    ∀ a : ℕ, ¬ S a →
      (C.wires (List.ofFn (Fin.snoc y false))).getD a false =
        (C.wires (List.ofFn (Fin.snoc y true))).getD a false := by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro haS
    set W₀ := C.wires (List.ofFn (Fin.snoc y false)) with hW₀
    set W₁ := C.wires (List.ofFn (Fin.snoc y true)) with hW₁
    by_cases h1 : a < n
    · have hw0 : W₀.getD a false = (List.ofFn (Fin.snoc y false)).getD a false :=
        getD_wiresFrom C.gates _ a (by simp; omega)
      have hw1 : W₁.getD a false = (List.ofFn (Fin.snoc y true)).getD a false :=
        getD_wiresFrom C.gates _ a (by simp; omega)
      let idx : Fin (n + 1) := ⟨a, by omega⟩
      have hi0 := getD_ofFn (Fin.snoc y false : Fin (n + 1) → Bool) idx
      have hi1 := getD_ofFn (Fin.snoc y true : Fin (n + 1) → Bool) idx
      rw [hw0, hw1]
      change (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool)).getD idx.val false =
        (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool)).getD idx.val false
      rw [hi0, hi1]
      have hcast : idx = (⟨a, h1⟩ : Fin n).castSucc := rfl
      rw [hcast, Fin.snoc_castSucc, Fin.snoc_castSucc]
    · by_cases h2 : a = n
      · exact absurd (h2 ▸ hnS) haS
      · by_cases h3 : a < n + 1 + C.gates.length
        · let j : Fin C.gates.length := ⟨a - (n + 1), by omega⟩
          have ha_eq : a = n + 1 + j.val := by dsimp [j]; omega
          rw [ha_eq] at haS ⊢
          rcases hclosed j haS with heq | hnoS
          · exact heq
          · rw [wires_gate_eval (n + 1) C _ (by simp) j (hlt j),
              wires_gate_eval (n + 1) C _ (by simp) j (hlt j)]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hru : Reads u (C.gates.get j) := (reads_iff u (C.gates.get j)).2 hu
            exact ih u (by rw [ha_eq]; exact hlt j u hru) (hnoS u hru)
        · have hl0 : W₀.length = n + 1 + C.gates.length := by
            rw [hW₀, wires_eq, length_wiresFrom]; simp
          have hl1 : W₁.length = n + 1 + C.gates.length := by
            rw [hW₁, wires_eq, length_wiresFrom]; simp
          rw [List.getD_eq_default W₀ _ (by omega), List.getD_eq_default W₁ _ (by omega)]

theorem or_gate_true (m : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = m)
    (j : Fin C.gates.length)
    (hlt : ∀ a, Reads a (C.gates.get j) → a < m + j.val)
    (hop : (C.gates.get j).op = GateOp.or)
    (a : ℕ) (ha : a ∈ (C.gates.get j).inputs)
    (htrue : (C.wires x).getD a false = true) :
    (C.wires x).getD (m + j.val) false = true := by
  rw [wires_gate_eval m C x hx j hlt]
  have hnorm : normGate (C.gates.get j) = C.gates.get j :=
    normGate_eq_self_of_ne_not _ (by rw [hop]; intro h; cases h)
  rw [hnorm, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  exact ⟨true, ⟨a, ha, htrue⟩, rfl⟩

theorem exists_false_of_ne {α : Type} {f : α → Bool} (h : ∃ a b, f a ≠ f b) :
    ∃ a, f a = false := by
  obtain ⟨a, b, hne⟩ := h
  cases ha : f a with
  | false => exact ⟨a, ha⟩
  | true =>
    cases hb : f b with
    | false => exact ⟨b, hb⟩
    | true => exact absurd (ha.trans hb.symm) hne

theorem getD_ofFn_last {n : ℕ} (x : Fin (n + 1) → Bool) :
    (List.ofFn x).getD n false = x (Fin.last n) :=
  getD_ofFn x (Fin.last n)

theorem fn_snoc_eval (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (heval : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)))
    (y : Fin n → Bool) (b : Bool) :
    circuitFun (n + 1) C (Fin.snoc y b) = (b || H y) := by
  rw [heval]
  simp [Fin.snoc_last, Fin.snoc_castSucc]

def ChainInv (n : ℕ) (C : Circuit) (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length) : Prop :=
  StrictMono c ∧
  (∀ i : Fin (k + 1), (C.gates.get (c i)).op = GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧
  n ∈ (C.gates.get (c 0)).inputs ∧
  (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val) ∧
  (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧
  (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs,
    w ≠ n + 1 + (c i.castSucc).val ∧ w < n + 1 + (c i.succ).val) ∧
  (∀ j : Fin C.gates.length, Reads n (C.gates.get j) → j = c 0) ∧
  (∀ (i : Fin k) (j : Fin C.gates.length),
    Reads (n + 1 + (c i.castSucc).val) (C.gates.get j) → j = c i.succ) ∧
  (∀ y : Fin n → Bool,
    (C.wires (List.ofFn (Fin.snoc y true))).getD (n + 1 + (c (Fin.last k)).val) false = true) ∧
  (∀ x : Fin (n + 1) → Bool,
    (C.wires (List.ofFn x)).getD (n + 1 + (c (Fin.last k)).val) false = true →
    circuitFun (n + 1) C x = true)

theorem extend_chain (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hmin : IsMinimalCircuit (n + 1) C)
    (hnc : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (heval : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)))
    (hlast : C.output = n + 1 + (C.gates.length - 1))
    (hlt : ∀ (j : Fin C.gates.length) (a : ℕ), Reads a (C.gates.get j) → a < n + 1 + j.val) :
    ∀ (d k : ℕ) (c : Fin (k + 1) → Fin C.gates.length),
      C.gates.length - 1 - (c (Fin.last k)).val ≤ d →
      ChainInv n C k c →
      ∃ (k' : ℕ) (c' : Fin (k' + 1) → Fin C.gates.length),
        ChainInv n C k' c' ∧ (c' (Fin.last k')).val + 1 = C.gates.length := by
  intro d
  induction d with
  | zero =>
    intro k c hd hinv
    have hlt' := (c (Fin.last k)).isLt
    exact ⟨k, c, hinv, by omega⟩
  | succ d ih =>
    intro k c hd hinv
    by_cases hdone : (c (Fin.last k)).val + 1 = C.gates.length
    · exact ⟨k, c, hinv, hdone⟩
    · obtain ⟨hmono, hop2, hn0, hw0, hnext_in, hw_next, huniq0, huniq_step, htrue_last, habs_last⟩ := hinv
      have hnc_all : ∃ x x' : Fin (n + 1) → Bool, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C x' := by
        obtain ⟨y, y', hy⟩ := hnc
        refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
        rw [fn_snoc_eval n C H heval, fn_snoc_eval n C H heval]
        simpa using hy
      have hout_ne : C.output ≠ n + 1 + (c (Fin.last k)).val := by
        rw [hlast]
        have := (c (Fin.last k)).isLt
        omega
      obtain ⟨j_wit, _, hj_wit_read⟩ := minimal_dead_gate (n + 1) C hmin (c (Fin.last k)) hout_ne
      obtain ⟨nxt, hlt_nxt, huniq_nxt, hop_nxt, hlen_nxt, hin_nxt, w_nxt, hw_nxt_in, hw_nxt_ne, hw_nxt_lt⟩ :=
        absorb_step (n + 1) C (n + 1 + (c (Fin.last k)).val) hmin hnc_all
          (by have := (c (Fin.last k)).isLt; omega) habs_last ⟨j_wit, hj_wit_read⟩
      have hgt : c (Fin.last k) < nxt := by
        show (c (Fin.last k)).val < nxt.val
        omega
      let c1 : Fin (k + 2) → Fin C.gates.length := Fin.snoc c nxt
      have hc1_last : c1 (Fin.last (k + 1)) = nxt := by simp [c1]
      have hc1_zero : c1 0 = c 0 := by
        have h0 : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
        rw [h0]; simp [c1]
      have hc1_mono : StrictMono c1 := by
        rw [Fin.strictMono_iff_lt_succ]
        intro i
        refine Fin.lastCases ?_ ?_ i
        · have h1 : (Fin.last k).castSucc = Fin.castSucc (Fin.last k) := rfl
          have h2 : (Fin.last k).succ = Fin.last (k + 1) := Fin.succ_last k
          simp only [c1, Fin.snoc_castSucc, h2, Fin.snoc_last]
          exact hgt
        · intro r
          have h1 : r.castSucc.succ = r.succ.castSucc := rfl
          simp only [c1, Fin.snoc_castSucc, h1]
          exact hmono Fin.castSucc_lt_succ
      have hc1_true : ∀ y : Fin n → Bool,
          (C.wires (List.ofFn (Fin.snoc y true))).getD (n + 1 + nxt.val) false = true := by
        intro y
        exact or_gate_true (n + 1) C _ (by simp) nxt (hlt nxt) hop_nxt
          (n + 1 + (c (Fin.last k)).val) hin_nxt (htrue_last y)
      have hc1_abs : ∀ x : Fin (n + 1) → Bool,
          (C.wires (List.ofFn x)).getD (n + 1 + nxt.val) false = true →
          circuitFun (n + 1) C x = true := by
        intro x hxt
        let y : Fin n → Bool := fun t => x t.castSucc
        have hx_eq : x = Fin.snoc y (x (Fin.last n)) := (Fin.snoc_init_self x).symm
        cases hb : x (Fin.last n) with
        | true =>
          rw [heval, hb]; rfl
        | false =>
          have hx0 : x = Fin.snoc y false := by rw [← hb]; exact hx_eq
          rw [hx0] at hxt ⊢
          let S : ℕ → Prop := fun a => a = n ∨ ∃ i : Fin (k + 1), a = n + 1 + (c i).val
          have hS_out : ¬ S C.output := by
            intro hS
            rcases hS with hS | ⟨i, hS⟩
            · rw [hlast] at hS; omega
            · have hi_le : (c i).val ≤ (c (Fin.last k)).val :=
                hmono.monotone (Fin.le_last i)
              have hnxt_lt := nxt.isLt
              rw [hlast] at hS
              omega
          have hag := wires_agree_outside n C y hlt S (Or.inl rfl) (by
            intro j hjS
            by_cases hjn : j = nxt
            · left
              subst hjn
              rw [hxt, hc1_true y]
            · right
              intro u hru huS
              rcases huS with rfl | ⟨i, rfl⟩
              · exact hjS (Or.inr ⟨0, by rw [huniq0 j hru]⟩)
              · refine Fin.lastCases (motive := fun i =>
                    Reads (n + 1 + (c i).val) (C.gates.get j) → False) ?_ ?_ i hru
                · intro hru'
                  exact hjn (huniq_nxt j hru')
                · intro r hru'
                  exact hjS (Or.inr ⟨r.succ, by rw [huniq_step r j hru']⟩)) C.output hS_out
          show (C.wires (List.ofFn (Fin.snoc y false))).getD C.output false = true
          rw [hag]
          show circuitFun (n + 1) C (Fin.snoc y true) = true
          rw [fn_snoc_eval n C H heval]; rfl
      have hinv1 : ChainInv n C (k + 1) c1 := by
        refine ⟨hc1_mono, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · rw [hc1_last]; exact ⟨hop_nxt, hlen_nxt⟩
          · intro r; simp only [c1, Fin.snoc_castSucc]; exact hop2 r
        · rw [hc1_zero]; exact hn0
        · rw [hc1_zero]; exact hw0
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simp only [c1, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
            exact hin_nxt
          · intro r
            have h1 : r.castSucc.succ = r.succ.castSucc := rfl
            simp only [c1, Fin.snoc_castSucc, h1]
            exact hnext_in r
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simp only [c1, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
            exact ⟨w_nxt, hw_nxt_in, hw_nxt_ne, hw_nxt_lt⟩
          · intro r
            have h1 : r.castSucc.succ = r.succ.castSucc := rfl
            simp only [c1, Fin.snoc_castSucc, h1]
            exact hw_next r
        · intro j hj; rw [hc1_zero]; exact huniq0 j hj
        · intro i j hj
          refine Fin.lastCases (motive := fun i =>
              Reads (n + 1 + (c1 i.castSucc).val) (C.gates.get j) → j = c1 i.succ) ?_ ?_ i hj
          · intro hj'
            simp only [c1, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] at hj' ⊢
            exact huniq_nxt j hj'
          · intro r hj'
            have h1 : r.castSucc.succ = r.succ.castSucc := rfl
            simp only [c1, Fin.snoc_castSucc, h1] at hj' ⊢
            exact huniq_step r j hj'
        · rw [hc1_last]; exact hc1_true
        · rw [hc1_last]; exact hc1_abs
      exact ih (k + 1) c1 (by rw [hc1_last]; have := nxt.isLt; omega) hinv1

end Gap568

open Gap568 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hmin hnc heval
  have hnc_all : ∃ x x' : Fin (n + 1) → Bool, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C x' := by
    obtain ⟨y, y', hy⟩ := hnc
    refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
    rw [fn_snoc_eval n C H heval, fn_snoc_eval n C H heval]
    simpa using hy
  have hlt : ∀ (j : Fin C.gates.length) (a : ℕ), Reads a (C.gates.get j) → a < n + 1 + j.val :=
    fun j a hr => minimal_reads_lt (n + 1) C hmin hnc_all j a hr
  have hout_ne_n : C.output ≠ n := by
    intro hout
    obtain ⟨y, y', hy⟩ := hnc
    apply hy
    have h1 := fn_snoc_eval n C H heval y false
    have h2 := fn_snoc_eval n C H heval y' false
    have hw1 : circuitFun (n + 1) C (Fin.snoc y false) = false := by
      show (wiresFrom C.gates (List.ofFn (Fin.snoc y false))).getD C.output false = false
      rw [hout, getD_wiresFrom C.gates _ n (by simp), getD_ofFn_last]
      simp
    have hw2 : circuitFun (n + 1) C (Fin.snoc y' false) = false := by
      show (wiresFrom C.gates (List.ofFn (Fin.snoc y' false))).getD C.output false = false
      rw [hout, getD_wiresFrom C.gates _ n (by simp), getD_ofFn_last]
      simp
    simp_all
  have hneed0 : ∃ j : Fin C.gates.length, Reads n (C.gates.get j) := by
    by_contra! hno
    obtain ⟨y0, hy0⟩ := exists_false_of_ne hnc
    have hag := wires_agree_outside n C y0 hlt (fun a => a = n) rfl
      (fun j _ => Or.inr (fun a hr ha => hno j (ha ▸ hr))) C.output hout_ne_n
    have h1 := fn_snoc_eval n C H heval y0 false
    have h2 := fn_snoc_eval n C H heval y0 true
    change circuitFun (n + 1) C (Fin.snoc y0 false) = circuitFun (n + 1) C (Fin.snoc y0 true) at hag
    rw [h1, h2, hy0] at hag
    cases hag
  have hpos : 0 < C.gates.length := by
    obtain ⟨j, _⟩ := hneed0
    exact Nat.zero_lt_of_lt j.isLt
  have hlast : C.output = n + 1 + (C.gates.length - 1) :=
    minimal_output_last (n + 1) C hmin hnc_all hpos
  have habs0 : ∀ x : Fin (n + 1) → Bool,
      (C.wires (List.ofFn x)).getD n false = true → circuitFun (n + 1) C x = true := by
    intro x hxn
    have h1 : (C.wires (List.ofFn x)).getD n false = x (Fin.last n) := by
      rw [wires_eq, getD_wiresFrom C.gates _ n (by simp), getD_ofFn_last]
    rw [heval, ← h1, hxn]; rfl
  obtain ⟨c0, _, huniq0, hop0, hlen0, hin0, w0, hw0_in, hw0_ne, hw0_lt⟩ :=
    absorb_step (n + 1) C n hmin hnc_all (by omega) habs0 hneed0
  have hc0_true : ∀ y : Fin n → Bool,
      (C.wires (List.ofFn (Fin.snoc y true))).getD (n + 1 + c0.val) false = true := by
    intro y
    refine or_gate_true (n + 1) C _ (by simp) c0 (hlt c0) hop0 n hin0 ?_
    rw [wires_eq, getD_wiresFrom C.gates _ n (by simp), getD_ofFn_last]
    simp
  have hc0_abs : ∀ x : Fin (n + 1) → Bool,
      (C.wires (List.ofFn x)).getD (n + 1 + c0.val) false = true →
      circuitFun (n + 1) C x = true := by
    intro x hxt
    let y : Fin n → Bool := fun t => x t.castSucc
    have hx_eq : x = Fin.snoc y (x (Fin.last n)) := (Fin.snoc_init_self x).symm
    cases hb : x (Fin.last n) with
    | true => rw [heval, hb]; rfl
    | false =>
      have hx0 : x = Fin.snoc y false := by rw [← hb]; exact hx_eq
      rw [hx0] at hxt ⊢
      have hag := wires_agree_outside n C y hlt (fun a => a = n) rfl (by
        intro j _
        by_cases hj0 : j = c0
        · left; subst hj0; rw [hxt, hc0_true y]
        · right; intro a hr ha; exact hj0 (huniq0 j (ha ▸ hr))) C.output hout_ne_n
      show (C.wires (List.ofFn (Fin.snoc y false))).getD C.output false = true
      rw [hag]
      show circuitFun (n + 1) C (Fin.snoc y true) = true
      rw [fn_snoc_eval n C H heval]; rfl
  let cinit : Fin 1 → Fin C.gates.length := fun _ => c0
  have hinit_inv : ChainInv n C 0 cinit := by
    refine ⟨?_, ?_, hin0, ⟨w0, hw0_in, hw0_ne, hw0_lt⟩, ?_, ?_, huniq0, ?_, hc0_true, hc0_abs⟩
    · intro a b hab; exact absurd hab (by omega)
    · intro i; exact ⟨hop0, hlen0⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  obtain ⟨k, c, hinv, hclast⟩ :=
    extend_chain n C H hmin hnc heval hlast hlt (C.gates.length - 1 - c0.val) 0 cinit le_rfl hinit_inv
  obtain ⟨hmono, hop2, hn0, ⟨w0', hw0'_in, hw0'_ne, hw0'_lt⟩, hnext_in, hw_next, huniq_0, huniq_step, _, _⟩ := hinv
  let E : ℕ → ℕ → Prop := fun a b =>
    ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ Reads a (C.gates.get j)
  have hreach_only : ∀ b : ℕ, Relation.TransGen E n b →
      ∃ i : Fin (k + 1), b = n + 1 + (c i).val := by
    intro b htr
    induction htr with
    | single he =>
      obtain ⟨j, rfl, hr⟩ := he
      exact ⟨0, by rw [huniq_0 j hr]⟩
    | tail _ he ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, rfl, hr⟩ := he
      rw [hi] at hr
      refine Fin.lastCases (motive := fun i =>
          Reads (n + 1 + (c i).val) (C.gates.get j) → ∃ i' : Fin (k + 1), n + 1 + j.val = n + 1 + (c i').val)
        ?_ ?_ i hr
      · intro hr_last
        have h1 := hlt j _ hr_last
        have h2 := j.isLt
        omega
      · intro r hr_r
        exact ⟨r.succ, by rw [huniq_step r j hr_r]⟩
  have hreach_chain : ∀ i : Fin (k + 1), Relation.TransGen E n (n + 1 + (c i).val) := by
    intro i
    obtain ⟨m, hm⟩ := i
    induction m with
    | zero =>
      apply Relation.TransGen.single
      refine ⟨c ⟨0, hm⟩, rfl, Or.inr ⟨?_, hn0⟩⟩
      rw [(hop2 ⟨0, hm⟩).1]; intro h; cases h
    | succ m ih =>
      have hm0 : m < k := by omega
      apply Relation.TransGen.tail (ih (by omega))
      refine ⟨c ⟨m + 1, hm⟩, rfl, Or.inr ⟨?_, hnext_in ⟨m, hm0⟩⟩⟩
      rw [(hop2 ⟨m + 1, hm⟩).1]; intro h; cases h
  refine ⟨k, c, hmono, hclast, by rw [hlast]; omega, hop2, hn0, hnext_in, huniq_0, huniq_step, ?_, ?_, ?_⟩
  · intro j
    constructor
    · intro htr
      obtain ⟨i, hi⟩ := hreach_only (n + 1 + j.val) htr
      exact ⟨i, Fin.ext (by omega)⟩
    · rintro ⟨i, rfl⟩
      exact hreach_chain i
  · refine ⟨w0', hw0'_in, hw0'_ne, hw0'_lt, ?_⟩
    intro htr
    obtain ⟨i, hi⟩ := hreach_only w0' htr
    have hle : (c 0).val ≤ (c i).val := hmono.monotone (Fin.zero_le i)
    omega
  · intro i
    obtain ⟨w, hw_in, hw_ne, hw_lt⟩ := hw_next i
    have hw_ne_n : w ≠ n := by
      intro e
      have hw_in' : n ∈ (C.gates.get (c i.succ)).inputs := e ▸ hw_in
      have hr : Reads n (C.gates.get (c i.succ)) :=
        Or.inr ⟨(by rw [(hop2 i.succ).1]; intro h; cases h), hw_in'⟩
      have heq : c i.succ = c 0 := huniq_0 (c i.succ) hr
      have hlt0 : c 0 < c i.succ := hmono (Fin.succ_pos i)
      rw [heq] at hlt0
      exact lt_irrefl _ hlt0
    refine ⟨w, hw_in, hw_ne, hw_ne_n, hw_lt, ?_⟩
    intro htr
    obtain ⟨r, hr⟩ := hreach_only w htr
    by_cases hle : i.succ ≤ r
    · have hle' : (c i.succ).val ≤ (c r).val := hmono.monotone hle
      omega
    · have hr_lt : r.val ≤ i.val := by
        have : r.val < i.val + 1 := Nat.lt_of_not_le hle
        omega
      let r' : Fin k := ⟨r.val, by omega⟩
      have hr_eq : r = r'.castSucc := Fin.ext rfl
      rw [hr_eq] at hr
      by_cases hri : r' = i
      · rw [hri] at hr; exact hw_ne hr
      · have hread_r : Reads (n + 1 + (c r'.castSucc).val) (C.gates.get (c i.succ)) :=
          Or.inr ⟨(by rw [(hop2 i.succ).1]; intro h; cases h), hr ▸ hw_in⟩
        have heq : c i.succ = c r'.succ := huniq_step r' (c i.succ) hread_r
        have hfeq : i.succ = r'.succ := hmono.injective heq
        exact hri (Fin.succ_inj.mp hfeq).symm
