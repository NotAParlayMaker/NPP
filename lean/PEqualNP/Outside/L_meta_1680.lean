import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1680

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Constant propagation adapted from MetaComplexity/Helpers/Elim.lean.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht, List.append_assoc]
    rfl

private theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨tail, h, hlen⟩ := wiresFrom_prefix gs w
  simp [h, hlen]

private theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

/-- A NOT gate reads only its first wire: drop the others. -/
private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
private def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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

private theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
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

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
private abbrev Stat := Sum Bool ℕ

private def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
    next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
private def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
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

private theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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

private theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
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

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
private def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

private def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

private theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

private theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
    saved. -/
private theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
    and every old wire has a valid status whose value on the new wires is the old value. -/
private def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

private theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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

private theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ hi

private def initial (n : ℕ) : List Stat × List Gate :=
  (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat)), [])

private theorem initial_inv (n : ℕ) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn x) (initial n) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · simp [initial, hi, Stat.Valid, Stat.val, wiresFrom]
  · simp [initial, List.getD_eq_default, hi, Stat.Valid, Stat.val, wiresFrom]

private theorem skip_inv (n : ℕ) (x : Fin n → Bool) (w : List Bool)
    (acc : List Stat × List Gate) (st : Stat) (b : Bool)
    (h : Inv n (List.ofFn x) w acc) (hv : st.Valid n)
    (hb : st.val (List.ofFn x) = b) :
    Inv n (List.ofFn x) (w ++ [b]) (acc.1 ++ [st], acc.2) := by
  obtain ⟨hl, hi⟩ := h
  have hs : st.val (wiresFrom acc.2 (List.ofFn x)) = b := by
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix acc.2 (List.ofFn x)
    rw [ht, Stat.val_append _ _ _ (by simpa using hv)]
    exact hb
  refine ⟨by simp [hl], ?_⟩
  intro i
  by_cases he : i = acc.1.length
  · subst i
    change ((acc.1 ++ [st]).getD acc.1.length (Sum.inl false)).Valid (n + acc.2.length) ∧
      ((acc.1 ++ [st]).getD acc.1.length (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        (w ++ [b]).getD acc.1.length false
    simp only [getD_snoc_eq]
    rw [hl, getD_snoc_eq]
    exact ⟨Stat.valid_mono (Nat.le_add_right _ _) st hv, hs⟩
  · rw [getD_snoc_ne _ _ _ _ he, getD_snoc_ne _ _ _ _ (by omega)]
    exact hi i

theorem prove : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), (∃ x y : Fin n → Bool, f x ≠ f y) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s + 1 → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = f x) → (∃ j : ℕ, j < C.gates.length ∧ ((∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = b) ∨ (∃ i : Fin n, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = x i))) → PEqualNP.MetaComplexity.HasCircuitSize n f s := by
  classical
  intro n s f hnc C hfan hsize hfun hex
  obtain ⟨j, hj, hsem⟩ := hex
  let pre := C.gates.take j
  let g := C.gates[j]
  let post := C.gates.drop (j + 1)
  have hsplit : C.gates = pre ++ g :: post := by
    have hs := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem_cons hj] at hs
    exact hs.symm
  have hprelen : pre.length = j := by simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
  have htotal : C.size = pre.length + 1 + post.length := by
    simp [Circuit.size, hsplit]
    omega
  have hok : ∀ k ∈ C.gates, Ok k := hfan
  have hpok : ∀ k ∈ pre, Ok k := fun k hk =>
    hok k (by rw [hsplit]; exact List.mem_append_left _ hk)
  have hpostok : ∀ k ∈ post, Ok k := fun k hk =>
    hok k (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hk))
  obtain ⟨st, hvalid, hst⟩ : ∃ st : Stat, st.Valid n ∧
      ∀ x : Fin n → Bool, st.val (List.ofFn x) =
        (C.wires (List.ofFn x)).getD (n + j) false := by
    rcases hsem with ⟨b, hb⟩ | ⟨i, hi⟩
    · exact ⟨Sum.inl b, trivial, fun x => (hb x).symm⟩
    · refine ⟨Sum.inr i.val, i.isLt, ?_⟩
      intro x
      simpa [Stat.val, i.isLt] using (hi x).symm
  let before := elim n pre (initial n)
  let after : List Stat × List Gate := (before.1 ++ [st], before.2)
  let final := elim n post after
  have hb_len : before.2.length ≤ pre.length := by
    have h := elim_len n pre (initial n)
    simpa [before, initial] using h
  have hf_len : final.2.length ≤ s := by
    have h := elim_len n post after
    change final.2.length ≤ before.2.length + post.length at h
    omega
  have hb_ok : ∀ k ∈ before.2, Ok k :=
    elim_ok n pre (initial n) (by simp [initial])
  have hf_ok : ∀ k ∈ final.2, Ok k := elim_ok n post after hb_ok
  have heval (x : Fin n → Bool) :
      (final.1.getD C.output (Sum.inl false)).val (wiresFrom final.2 (List.ofFn x)) = f x := by
    let w := wiresFrom pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hwlen : w.length = n + j := by simp [w, length_wiresFrom, hprelen]
    have hwire : (C.wires (List.ofFn x)).getD (n + j) false = b := by
      change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = b
      rw [hsplit, wiresFrom_append]
      change (wiresFrom post (w ++ [b])).getD (n + j) false = b
      rw [getD_run _ _ _ (by simp [hwlen]), ← hwlen, getD_snoc_eq]
    have hb_inv : Inv n (List.ofFn x) w before :=
      inv_elim n (List.ofFn x) (by simp) pre _ (initial n) hpok (initial_inv n x)
    have ha_inv : Inv n (List.ofFn x) (w ++ [b]) after :=
      skip_inv n x w before st b hb_inv hvalid ((hst x).trans hwire)
    have hf_inv := inv_elim n (List.ofFn x) (by simp) post (w ++ [b]) after hpostok ha_inv
    have hval := (hf_inv.2 C.output).2
    change (final.1.getD C.output (Sum.inl false)).val (wiresFrom final.2 (List.ofFn x)) = _ at hval
    rw [← hfun x]
    change _ = (wiresFrom C.gates (List.ofFn x)).getD C.output false
    rw [hsplit, wiresFrom_append]
    exact hval
  obtain ⟨out, hout⟩ : ∃ out, final.1.getD C.output (Sum.inl false) = Sum.inr out := by
    cases h : final.1.getD C.output (Sum.inl false) with
    | inr out => exact ⟨out, rfl⟩
    | inl b =>
      obtain ⟨x, y, hxy⟩ := hnc
      exfalso
      apply hxy
      rw [← heval x, ← heval y, h]
      rfl
  refine ⟨⟨final.2, out⟩, hf_ok, hf_len, ?_⟩
  intro x
  have h := heval x
  rw [hout] at h
  exact h

end PEqualNP.Outside.L_meta_1680

theorem PEqualNP.Outside.L_meta_1680 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), (∃ x y : Fin n → Bool, f x ≠ f y) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s + 1 → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = f x) → (∃ j : ℕ, j < C.gates.length ∧ ((∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = b) ∨ (∃ i : Fin n, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = x i))) → PEqualNP.MetaComplexity.HasCircuitSize n f s :=
  PEqualNP.Outside.L_meta_1680.prove
