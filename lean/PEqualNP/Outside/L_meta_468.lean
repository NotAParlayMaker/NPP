import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

def L_meta_468_wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem L_meta_468_wires_eq (C : Circuit) (x : List Bool) : C.wires x = L_meta_468_wiresFrom C.gates x := rfl

theorem L_meta_468_wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    L_meta_468_wiresFrom (gs ++ gs') w = L_meta_468_wiresFrom gs' (L_meta_468_wiresFrom gs w) := by
  simp [L_meta_468_wiresFrom, List.foldl_append]

theorem L_meta_468_wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, L_meta_468_wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [L_meta_468_wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : L_meta_468_wiresFrom (g :: gs) w
        = L_meta_468_wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem L_meta_468_length_wiresFrom (gs : List Gate) (w : List Bool) :
    (L_meta_468_wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := L_meta_468_wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem L_meta_468_getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (L_meta_468_wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := L_meta_468_wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def L_meta_468_Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem L_meta_468_getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem L_meta_468_getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def L_meta_468_gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem L_meta_468_mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem L_meta_468_mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ L_meta_468_gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  L_meta_468_mem_foldr_union _ _ _

def L_meta_468_suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [L_meta_468_gateSupp L g]) L

def L_meta_468_inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def L_meta_468_Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem L_meta_468_agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), L_meta_468_Agree x y L w w' →
      L_meta_468_Agree x y (L_meta_468_suppsFrom gs L) (L_meta_468_wiresFrom gs w) (L_meta_468_wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [L_meta_468_gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [L_meta_468_getD_snoc_eq] at hj
      rw [h1, L_meta_468_getD_snoc_eq, h2, L_meta_468_getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((L_meta_468_mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [L_meta_468_getD_snoc_ne _ _ _ _ hjl] at hj
      rw [L_meta_468_getD_snoc_ne _ _ _ _ (by omega), L_meta_468_getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem L_meta_468_agree_inputs (x y : Fin n → Bool) :
    L_meta_468_Agree x y (L_meta_468_inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [L_meta_468_inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [L_meta_468_inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def L_meta_468_normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem L_meta_468_normGate_eval (g : Gate) (F : ℕ → Bool) :
    (L_meta_468_normGate g).op.eval ((L_meta_468_normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [L_meta_468_normGate]
  cases inputs <;> simp [GateOp.eval]

def L_meta_468_NOk (g : Gate) : Prop := L_meta_468_Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem L_meta_468_normGate_nok (g : Gate) (h : L_meta_468_Ok g) : L_meta_468_NOk (L_meta_468_normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [L_meta_468_normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [L_meta_468_normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [L_meta_468_normGate] <;> omega

theorem L_meta_468_wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    L_meta_468_wiresFrom (gs.map L_meta_468_normGate) w = L_meta_468_wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : L_meta_468_wiresFrom ((g :: gs).map L_meta_468_normGate) w = L_meta_468_wiresFrom (gs.map L_meta_468_normGate)
        (w ++ [(L_meta_468_normGate g).op.eval ((L_meta_468_normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : L_meta_468_wiresFrom (g :: gs) w
        = L_meta_468_wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, L_meta_468_normGate_eval, ih]

abbrev L_meta_468_Stat := Bool ⊕ ℕ

def L_meta_468_Stat.val (w : List Bool) : L_meta_468_Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def L_meta_468_Stat.Valid (m : ℕ) : L_meta_468_Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def L_meta_468_simpNot (m : ℕ) : List L_meta_468_Stat → Option Gate × L_meta_468_Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def L_meta_468_simpAnd (m : ℕ) : List L_meta_468_Stat → Option Gate × L_meta_468_Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def L_meta_468_simpOr (m : ℕ) : List L_meta_468_Stat → Option Gate × L_meta_468_Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def L_meta_468_simplify (op : GateOp) (m : ℕ) (ins : List L_meta_468_Stat) : Option Gate × L_meta_468_Stat :=
  match op with
  | GateOp.and => L_meta_468_simpAnd m ins
  | GateOp.or => L_meta_468_simpOr m ins
  | GateOp.not => L_meta_468_simpNot m ins
  | _ => (none, Sum.inl false)

theorem L_meta_468_simplify_ok (op : GateOp) (m : ℕ) (ins : List L_meta_468_Stat) :
    ∀ g ∈ (L_meta_468_simplify op m ins).1, L_meta_468_Ok g := by
  intro g hg
  cases op <;> simp only [L_meta_468_simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [L_meta_468_simpAnd] at hg <;> (subst hg; simp [L_meta_468_Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [L_meta_468_simpOr] at hg <;> (subst hg; simp [L_meta_468_Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [L_meta_468_simpNot] at hg <;> (subst hg; simp [L_meta_468_Ok])
  · simp at hg
  · simp at hg

theorem L_meta_468_simplify_count (op : GateOp) (m : ℕ) (ins : List L_meta_468_Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (L_meta_468_simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [L_meta_468_simplify, L_meta_468_simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [L_meta_468_simplify, L_meta_468_simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [L_meta_468_simplify, L_meta_468_simpNot]

theorem L_meta_468_simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List L_meta_468_Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((L_meta_468_simplify op w.length ins).2).Valid (w.length + (L_meta_468_simplify op w.length ins).1.toList.length) ∧
    ((L_meta_468_simplify op w.length ins).2).val (L_meta_468_wiresFrom (L_meta_468_simplify op w.length ins).1.toList w)
      = op.eval (ins.map (L_meta_468_Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [L_meta_468_simplify, L_meta_468_simpAnd, L_meta_468_Stat.Valid, L_meta_468_Stat.val, GateOp.eval]
    · cases a <;> simp_all [L_meta_468_simplify, L_meta_468_simpAnd, L_meta_468_Stat.Valid, L_meta_468_Stat.val, GateOp.eval, L_meta_468_wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [L_meta_468_simplify, L_meta_468_simpAnd, L_meta_468_Stat.Valid, L_meta_468_Stat.val, GateOp.eval, L_meta_468_wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [L_meta_468_simplify, L_meta_468_simpOr, L_meta_468_Stat.Valid, L_meta_468_Stat.val, GateOp.eval]
    · cases a <;> simp_all [L_meta_468_simplify, L_meta_468_simpOr, L_meta_468_Stat.Valid, L_meta_468_Stat.val, GateOp.eval, L_meta_468_wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [L_meta_468_simplify, L_meta_468_simpOr, L_meta_468_Stat.Valid, L_meta_468_Stat.val, GateOp.eval, L_meta_468_wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [L_meta_468_simplify, L_meta_468_simpNot, L_meta_468_Stat.Valid, L_meta_468_Stat.val, GateOp.eval]
    · cases a <;> simp_all [L_meta_468_simplify, L_meta_468_simpNot, L_meta_468_Stat.Valid, L_meta_468_Stat.val, GateOp.eval, L_meta_468_wiresFrom]

def L_meta_468_elimStep (n : ℕ) (acc : List L_meta_468_Stat × List Gate) (g : Gate) : List L_meta_468_Stat × List Gate :=
  (acc.1 ++ [(L_meta_468_simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (L_meta_468_simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def L_meta_468_elim (n : ℕ) (gs : List Gate) (acc : List L_meta_468_Stat × List Gate) : List L_meta_468_Stat × List Gate :=
  gs.foldl (L_meta_468_elimStep n) acc

theorem L_meta_468_getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem L_meta_468_elim_getD (n k : ℕ) (d : L_meta_468_Stat) (gs : List Gate) : ∀ acc : List L_meta_468_Stat × List Gate,
    k < acc.1.length → (L_meta_468_elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : L_meta_468_elim n (g :: gs) acc = L_meta_468_elim n gs (L_meta_468_elimStep n acc g) := rfl
    rw [h3, ih (L_meta_468_elimStep n acc g) (by simp [L_meta_468_elimStep]; omega)]
    exact L_meta_468_getD_snoc_ne _ _ _ _ (by omega)

theorem L_meta_468_toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem L_meta_468_elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List L_meta_468_Stat × List Gate,
    (∀ g ∈ acc.2, L_meta_468_Ok g) → ∀ g ∈ (L_meta_468_elim n gs acc).2, L_meta_468_Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (L_meta_468_elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact L_meta_468_simplify_ok _ _ _ g' (by simpa using h1)

theorem L_meta_468_elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List L_meta_468_Stat × List Gate,
    (L_meta_468_elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [L_meta_468_elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (L_meta_468_elimStep n acc g)
    have h2 : (L_meta_468_elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [L_meta_468_elimStep, List.length_append]
      have := L_meta_468_toList_length_le (L_meta_468_simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : L_meta_468_elim n (g :: gs) acc = L_meta_468_elim n gs (L_meta_468_elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem L_meta_468_elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List L_meta_468_Stat × List Gate,
    (∀ g ∈ gs, L_meta_468_NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (L_meta_468_elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : L_meta_468_elim n (g :: gs) acc = L_meta_468_elim n gs (L_meta_468_elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (L_meta_468_simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply L_meta_468_simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (L_meta_468_elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (L_meta_468_simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := L_meta_468_elim_len n gs (L_meta_468_elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (L_meta_468_elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [L_meta_468_elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [L_meta_468_elimStep]
          rw [L_meta_468_getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (L_meta_468_elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [L_meta_468_elimStep, List.length_append]
        have := L_meta_468_toList_length_le (L_meta_468_simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem L_meta_468_Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : L_meta_468_Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem L_meta_468_Stat.val_append (w t : List Bool) : ∀ s : L_meta_468_Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def L_meta_468_Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List L_meta_468_Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (L_meta_468_wiresFrom acc.2 y) = w.getD i false

theorem L_meta_468_inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List L_meta_468_Stat × List Gate), (∀ g ∈ gs, L_meta_468_Ok g) → L_meta_468_Inv n y w acc →
      L_meta_468_Inv n y (L_meta_468_wiresFrom gs w) (L_meta_468_elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (L_meta_468_elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := L_meta_468_wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', L_meta_468_length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := L_meta_468_simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := L_meta_468_simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (L_meta_468_Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : L_meta_468_wiresFrom (acc.2 ++ r.1.toList) y = L_meta_468_wiresFrom r.1.toList w' := by
      rw [L_meta_468_wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := L_meta_468_wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [L_meta_468_elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (L_meta_468_wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [L_meta_468_getD_snoc_eq, hl, L_meta_468_getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [L_meta_468_getD_snoc_ne _ _ _ _ hil, L_meta_468_getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨L_meta_468_Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, L_meta_468_Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def L_meta_468_initStats (n : ℕ) (b : Bool) : List L_meta_468_Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : L_meta_468_Stat)) ++ [Sum.inl b]

theorem L_meta_468_inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    L_meta_468_Inv n (List.ofFn y) (List.ofFn y ++ [b]) (L_meta_468_initStats n b, []) := by
  refine ⟨by simp [L_meta_468_initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : L_meta_468_Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [L_meta_468_initStats]
    rw [L_meta_468_getD_snoc_len _ _ _ _ l1, L_meta_468_getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [L_meta_468_initStats]
    rw [L_meta_468_getD_snoc_ne _ _ _ _ (by omega), L_meta_468_getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, L_meta_468_Stat.Valid, L_meta_468_Stat.val, L_meta_468_wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem L_meta_468_ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem L_meta_468_supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (L_meta_468_suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [L_meta_468_gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [L_meta_468_getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (L_meta_468_mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [L_meta_468_getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem L_meta_468_inputSupps_getD (m j : ℕ) (h : j < m) :
    (L_meta_468_inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [L_meta_468_inputSupps, h]

theorem L_meta_468_inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (L_meta_468_inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (L_meta_468_inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := L_meta_468_inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [L_meta_468_inputSupps]; omega)]; simp

theorem L_meta_468_elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List L_meta_468_Stat × List Gate) :
    L_meta_468_elim n (g :: gs) acc = L_meta_468_elim n gs (L_meta_468_elimStep n acc g) := rfl

theorem L_meta_468_elim_append (n : ℕ) (pre post : List Gate) (acc : List L_meta_468_Stat × List Gate) :
    L_meta_468_elim n (pre ++ post) acc = L_meta_468_elim n post (L_meta_468_elim n pre acc) := by
  simp [L_meta_468_elim, List.foldl_append]

theorem L_meta_468_elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List L_meta_468_Stat × List Gate,
    (L_meta_468_elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [L_meta_468_elim_cons, ih]
    simp only [L_meta_468_elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem L_meta_468_initStats_last (n : ℕ) (b : Bool) :
    (L_meta_468_initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  L_meta_468_getD_snoc_len _ _ _ _ (by simp)

theorem L_meta_468_simplify_const (op : GateOp) (m : ℕ) (ins : List L_meta_468_Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (L_meta_468_simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [L_meta_468_simplify, L_meta_468_simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [L_meta_468_simplify, L_meta_468_simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [L_meta_468_simplify, L_meta_468_simpNot]

theorem L_meta_468_elimStep_none (n : ℕ) (acc : List L_meta_468_Stat × List Gate) (g : Gate) (hg : L_meta_468_NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (L_meta_468_elimStep n acc g).2.length = acc.2.length := by
  have hnone : (L_meta_468_simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply L_meta_468_simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (L_meta_468_simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def L_meta_468_fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem L_meta_468_elimStep_const (n : ℕ) (acc : List L_meta_468_Stat × List Gate) (g : Gate) (hg : L_meta_468_NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (L_meta_468_fixBit g)) :
    ∃ c, (L_meta_468_elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (L_meta_468_elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (L_meta_468_simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := L_meta_468_getD_snoc_eq _ _ _
  rw [e]
  apply L_meta_468_simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (L_meta_468_fixBit g)
  · intro h; simp [L_meta_468_fixBit, h]
  · intro h; simp [L_meta_468_fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem L_meta_468_suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    L_meta_468_suppsFrom (pre ++ post) L = L_meta_468_suppsFrom post (L_meta_468_suppsFrom pre L) := by
  simp [L_meta_468_suppsFrom, List.foldl_append]

theorem L_meta_468_length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (L_meta_468_suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : L_meta_468_suppsFrom (g :: gs) L = L_meta_468_suppsFrom gs (L ++ [L_meta_468_gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem L_meta_468_supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (L_meta_468_suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [L_meta_468_gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [L_meta_468_getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (L_meta_468_mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [L_meta_468_getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem L_meta_468_two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, L_meta_468_NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (L_meta_468_suppsFrom gs (L_meta_468_inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (L_meta_468_elim n gs (L_meta_468_initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (L_meta_468_elim n gs (L_meta_468_initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, L_meta_468_elim_getD n n _ gs _ (by simp [L_meta_468_initStats])]
    exact L_meta_468_initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact L_meta_468_supp_noread n gs (L_meta_468_inputSupps (n + 1)) hread (L_meta_468_inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : L_meta_468_NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, L_meta_468_NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, L_meta_468_NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, L_meta_468_elim n (pre ++ g :: post) (L_meta_468_initStats n b, [])
      = L_meta_468_elim n post (L_meta_468_elimStep n (L_meta_468_elim n pre (L_meta_468_initStats n b, [])) g) :=
    fun b => by rw [L_meta_468_elim_append, L_meta_468_elim_cons]
  have hAn : ∀ b, (L_meta_468_elim n pre (L_meta_468_initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [L_meta_468_elim_getD n n _ pre _ (by simp [L_meta_468_initStats])]
    exact L_meta_468_initStats_last n b
  have hAl : ∀ b, (L_meta_468_elim n pre (L_meta_468_initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [L_meta_468_elim_fst_len]
    simp [L_meta_468_initStats]
  have hA2 : ∀ b, (L_meta_468_elim n pre (L_meta_468_initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => L_meta_468_elim_len n pre (L_meta_468_initStats n b, [])
  have hB2 := fun b => L_meta_468_elimStep_none n (L_meta_468_elim n pre (L_meta_468_initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (L_meta_468_elimStep n (L_meta_468_elim n pre (L_meta_468_initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [L_meta_468_elimStep, hAl b]
  have hBn : ∀ b, (L_meta_468_elimStep n (L_meta_468_elim n pre (L_meta_468_initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((L_meta_468_elim n pre (L_meta_468_initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [L_meta_468_getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => L_meta_468_elim_len n post (L_meta_468_elimStep n (L_meta_468_elim n pre (L_meta_468_initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (L_meta_468_elim n pre (L_meta_468_initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      L_meta_468_elim_len_lt n n pre (L_meta_468_initStats n false, []) hpren (by simp [L_meta_468_initStats])
        ⟨false, L_meta_468_initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := L_meta_468_elim_len_lt n n post (L_meta_468_elimStep n (L_meta_468_elim n pre (L_meta_468_initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := L_meta_468_elimStep_const n (L_meta_468_elim n pre (L_meta_468_initStats n (L_meta_468_fixBit g), [])) g hgn n hng
    (hAn (L_meta_468_fixBit g))
  rw [hAl (L_meta_468_fixBit g)] at hc
  refine ⟨L_meta_468_fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := L_meta_468_elim_len_lt n (n + 1 + pre.length) post
      (L_meta_468_elimStep n (L_meta_468_elim n pre (L_meta_468_initStats n (L_meta_468_fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (L_meta_468_fixBit g)
    have := hB2 (L_meta_468_fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (L_meta_468_fixBit g) c
      rw [hsplit, e, L_meta_468_elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : L_meta_468_suppsFrom (pre ++ g :: post) (L_meta_468_inputSupps (n + 1))
        = L_meta_468_suppsFrom post (L_meta_468_suppsFrom pre (L_meta_468_inputSupps (n + 1))
          ++ [L_meta_468_gateSupp (L_meta_468_suppsFrom pre (L_meta_468_inputSupps (n + 1))) g]) := by
      rw [L_meta_468_suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := L_meta_468_supp_noread n pre (L_meta_468_inputSupps (n + 1)) h1 (L_meta_468_inputSupps_noread n)
    have hLl : (L_meta_468_suppsFrom pre (L_meta_468_inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [L_meta_468_length_suppsFrom]
      simp [L_meta_468_inputSupps]
    refine L_meta_468_supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
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
      rw [L_meta_468_getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem L_meta_468_gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map L_meta_468_normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, L_meta_468_NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact L_meta_468_normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (L_meta_468_wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, L_meta_468_wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      L_meta_468_Inv n (List.ofFn y) (L_meta_468_wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (L_meta_468_elim n gs (L_meta_468_initStats n b, [])) := by
    intro b y
    rw [L_meta_468_ofFn_snoc]
    exact L_meta_468_inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (L_meta_468_inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((L_meta_468_elim n gs (L_meta_468_initStats n b, [])).1.getD C.output (Sum.inl false)).val
        (L_meta_468_wiresFrom (L_meta_468_elim n gs (L_meta_468_initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (L_meta_468_elim n gs (L_meta_468_initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (L_meta_468_suppsFrom gs (L_meta_468_inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (L_meta_468_agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (L_meta_468_agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := L_meta_468_two_saved n gs hnok C.output hsupp hout
  cases hst : (L_meta_468_elim n gs (L_meta_468_initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (L_meta_468_elim n gs (L_meta_468_initStats n b, [])).2.length, by omega,
      ⟨(L_meta_468_elim n gs (L_meta_468_initStats n b, [])).2, j⟩, L_meta_468_elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def L_meta_468_wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def L_meta_468_relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (L_meta_468_wmap n m π)⟩

def L_meta_468_relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (L_meta_468_relGate n m π), L_meta_468_wmap n m π C.output⟩

def L_meta_468_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def L_meta_468_Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (L_meta_468_wmap n m π w) false = W.getD w false

theorem L_meta_468_rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : L_meta_468_Rel n m π W W') : L_meta_468_Rel n m π (L_meta_468_step W g) (L_meta_468_step W' (L_meta_468_relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (L_meta_468_relGate n m π g).op.eval
      ((L_meta_468_relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [L_meta_468_relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [L_meta_468_step]; omega, by simp [L_meta_468_step]; omega, ?_⟩
  intro w
  simp only [L_meta_468_step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : L_meta_468_wmap n m π w < W'.length := by
      unfold L_meta_468_wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : L_meta_468_wmap n m π w = W'.length := by
      unfold L_meta_468_wmap
      split
      · omega
      · omega
    rw [he, hw, L_meta_468_getD_snoc_eq, L_meta_468_getD_snoc_eq]
  · have hge : W'.length + 1 ≤ L_meta_468_wmap n m π w := by
      unfold L_meta_468_wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem L_meta_468_rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, L_meta_468_Rel n m π W W' →
      L_meta_468_Rel n m π (gs.foldl L_meta_468_step W) ((gs.map (L_meta_468_relGate n m π)).foldl L_meta_468_step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (L_meta_468_rel_step n m π W W' g h)

theorem L_meta_468_rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    L_meta_468_Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold L_meta_468_wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem L_meta_468_relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨L_meta_468_relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [L_meta_468_relGate] using (ok g0 hg0).2⟩
  · simpa [L_meta_468_relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (L_meta_468_rel_fold n m π C.gates _ _ (L_meta_468_rel_init n m π x)).2.2 C.output
    exact this

theorem L_meta_468_snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
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

theorem L_meta_468_gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := L_meta_468_relabel_size (⇑σ) f s h
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
    rw [L_meta_468_snoc_swap, L_meta_468_snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := L_meta_468_gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := L_meta_468_relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (L_meta_468_snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem L_meta_468_gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map L_meta_468_normGate with hgs
  have hnok : ∀ g ∈ gs, L_meta_468_NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact L_meta_468_normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (L_meta_468_wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, L_meta_468_wiresFrom_norm, ← hev x]; rfl
  set acc := L_meta_468_elim n gs (L_meta_468_initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      L_meta_468_Inv n (List.ofFn y) (L_meta_468_wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [L_meta_468_ofFn_snoc]
    exact L_meta_468_inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (L_meta_468_inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (L_meta_468_wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := L_meta_468_elim_len_lt n n gs (L_meta_468_initStats n b, []) hnok (by simp [L_meta_468_initStats])
          ⟨b, L_meta_468_getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, L_meta_468_elim_getD n n _ gs _ (by simp [L_meta_468_initStats])] at hst
          have hb : (L_meta_468_initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            L_meta_468_getD_snoc_len _ _ _ _ (by simp)
          rw [show ((L_meta_468_initStats n b, ([] : List Gate))).1 = L_meta_468_initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := L_meta_468_supp_noread n gs (L_meta_468_inputSupps (n + 1)) hread (L_meta_468_inputSupps_noread n) C.output hout
        have hag := (L_meta_468_agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (L_meta_468_agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, L_meta_468_elim_ok n gs _ (by simp), le_rfl, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem L_meta_468_gate_elim_one_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (s' : ℕ), s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := L_meta_468_relabel_size (⇑σ) f s h
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
    rw [L_meta_468_snoc_swap, L_meta_468_snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := L_meta_468_gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := L_meta_468_relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (L_meta_468_snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem L_meta_468_fix_one {N : ℕ} (f : (Fin N → Bool) → Bool) (p : Fin N)
    (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin N → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin N → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize N f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize N (fun x => f (Function.update x p b)) s' := by
  cases N with
  | zero => exact p.elim0
  | succ N => exact L_meta_468_gate_elim_one_at N f p b s hdep hnc h

theorem L_meta_468_fix_two {N : ℕ} (f : (Fin N → Bool) → Bool) (p : Fin N) (s : ℕ)
    (hdep : ∃ x : Fin N → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin N → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize N f s) :
    ∃ b s', s' + 2 ≤ s ∧ HasCircuitSize N (fun x => f (Function.update x p b)) s' := by
  cases N with
  | zero => exact p.elim0
  | succ N => exact L_meta_468_gate_elim_at N f p s hdep hnc h

theorem L_meta_468_fix_prefix {n k : ℕ} (f : (Fin (n + k) → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin k → Bool, f (Fin.append (fun _ => false) y) ≠
      f (Fin.append (fun _ => false) y'))
    (hf : HasCircuitSize (n + k) f s) :
    HasCircuitSize k (fun y => f (Fin.append (fun _ => false) y)) s := by
  obtain ⟨C, hC, hsize, heval⟩ := hf
  let a : List L_meta_468_Stat :=
    List.replicate n (Sum.inl false : L_meta_468_Stat) ++ List.ofFn (fun j : Fin k => (Sum.inr (j : ℕ) : L_meta_468_Stat))
  have ha : a.length = n + k := by simp [a]
  have hinit (y : Fin k → Bool) :
      L_meta_468_Inv k (List.ofFn y) (List.ofFn (Fin.append (fun _ : Fin n => false) y))
        (a, []) := by
    refine ⟨by simp [ha], ?_⟩
    intro i
    have hxs : List.ofFn (Fin.append (fun _ : Fin n => false) y) =
        List.replicate n false ++ List.ofFn y := by
      rw [List.ofFn_fin_append]
      simp
    rw [hxs]
    change (a.getD i (Sum.inl false)).Valid k ∧
      (a.getD i (Sum.inl false)).val (List.ofFn y) =
        (List.replicate n false ++ List.ofFn y).getD i false
    by_cases hi : i < n
    · have hil : i < (List.replicate n (Sum.inl false : L_meta_468_Stat)).length := by simpa
      have hir : i < (List.replicate n false).length := by simpa
      rw [show a = _ from rfl, List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ hir]
      simp [hi, L_meta_468_Stat.Valid, L_meta_468_Stat.val]
    · have hil : (List.replicate n (Sum.inl false : L_meta_468_Stat)).length ≤ i := by simpa using Nat.le_of_not_gt hi
      have hir : (List.replicate n false).length ≤ i := by simpa using Nat.le_of_not_gt hi
      rw [show a = _ from rfl, List.getD_append_right _ _ _ _ hil, List.getD_append_right _ _ _ _ hir]
      simp only [List.length_replicate]
      by_cases hj : i - n < k
      · simp [hj, L_meta_468_Stat.Valid, L_meta_468_Stat.val]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)]
        exact ⟨trivial, rfl⟩
  let acc := L_meta_468_elim k C.gates (a, [])
  have hv (y : Fin k → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (L_meta_468_wiresFrom acc.2 (List.ofFn y)) =
        f (Fin.append (fun _ => false) y) := by
    rw [← heval]
    exact ((L_meta_468_inv_elim k _ (by simp) C.gates _ _ hC (hinit y)).2 C.output).2
  cases hres : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨y, y', hy⟩ := hnc
    exact (hy (by rw [← hv y, ← hv y', hres]; rfl)).elim
  | inr o =>
    refine ⟨⟨acc.2, o⟩, L_meta_468_elim_ok k C.gates _ (by simp), ?_, ?_⟩
    · have hlen := L_meta_468_elim_len k C.gates (a, [])
      exact (show acc.2.length ≤ C.gates.length by simpa [acc] using hlen).trans hsize
    · intro y
      have h := hv y
      rw [hres] at h
      exact h

def L_meta_468_cover {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S

def L_meta_468_isolated {V : Type*} (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ a ∈ A, ∀ v, ¬ G.Adj a v

def L_meta_468_leaf {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ∀ w, G.Adj u w → w = v

theorem L_meta_468_leaf_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (h : L_meta_468_leaf G u v) : G.degree u = 1 :=
  SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨v, h.1, h.2⟩

theorem L_meta_468_leaf_choice {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (hex : ∃ a b, G.Adj a b) :
    ∃ u v, L_meta_468_leaf G u v ∧
      (G.degree v ≤ 2 ∨ ∃ z, z ≠ u ∧ L_meta_468_leaf G z v) := by
  obtain ⟨a, b, hab⟩ := hex
  let _ : Nonempty V := ⟨a⟩
  obtain ⟨u, r, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  cases p with
  | nil =>
    have hpos := hmax a b (SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil)
      (SimpleGraph.Walk.IsPath.nil.cons (by simpa using hab.ne))
    simp at hpos
  | @cons u v r huv q =>
    have hq := hp.of_cons
    refine ⟨u, v, ⟨huv, ?_⟩, ?_⟩
    · intro w huw
      by_contra hn
      have hw : w ∉ (q.cons huv).support := by
        intro hm
        exact hn (by simpa using hG.eq_snd_of_adj_start hp huw hm)
      have hlong := hmax _ _ _ (hp.cons hw (h := huw.symm))
      simp at hlong
    · by_cases hd : G.degree v ≤ 2
      · exact Or.inl hd
      right
      have he : ∃ z, G.Adj v z ∧ z ≠ u ∧ z ≠ q.snd := by
        by_contra! hm
        apply hd
        have hsub : G.neighborFinset v ⊆ {u, q.snd} := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases hzu : z = u
          · exact Or.inl hzu
          · exact Or.inr (hm z ((G.mem_neighborFinset v z).mp hz) hzu)
        exact (Finset.card_le_card hsub).trans (by simpa using Finset.card_insert_le u ({q.snd} : Finset V))
      obtain ⟨z, hvz, hzu, hzq⟩ := he
      have hz : z ∉ q.support := by
        intro hm
        exact hzq (hG.eq_snd_of_adj_start hq hvz hm)
      have hpz := hq.cons hz (h := hvz.symm)
      refine ⟨z, hzu, hvz.symm, ?_⟩
      intro w hzw
      by_contra hwv
      have hw : w ∉ (q.cons hvz.symm).support := by
        intro hm
        exact hwv (by simpa using hG.eq_snd_of_adj_start hpz hzw hm)
      have hlong := hmax _ _ _ (hpz.cons hw (h := hzw.symm))
      simp at hlong

def L_meta_468_core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

def L_meta_468_f {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool) (x : Fin (n + k) → Bool) : Bool :=
  L_meta_468_core G A (fun i => x (Fin.castAdd k i)) || g (fun j => x (Fin.natAdd n j))

theorem L_meta_468_cast_update {n k : ℕ} (x : Fin (n + k) → Bool) (p : Fin n) (b : Bool) :
    (fun i => Function.update x (Fin.castAdd k p) b (Fin.castAdd k i)) =
      Function.update (fun i => x (Fin.castAdd k i)) p b := by
  funext i
  by_cases hi : i = p
  · subst i
    simp
  · rw [Function.update_of_ne hi, Function.update_of_ne]
    exact fun h => hi (Fin.castAdd_injective n k h)

theorem L_meta_468_nat_update {n k : ℕ} (x : Fin (n + k) → Bool) (p : Fin n) (b : Bool) :
    (fun j => Function.update x (Fin.castAdd k p) b (Fin.natAdd n j)) =
      (fun j => x (Fin.natAdd n j)) := by
  funext j
  apply Function.update_of_ne
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem L_meta_468_f_update {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (x : Fin (n + k) → Bool) (p : Fin n) (b : Bool) :
    L_meta_468_f G A g (Function.update x (Fin.castAdd k p) b) =
      (L_meta_468_core G A (Function.update (fun i => x (Fin.castAdd k i)) p b) ||
        g (fun j => x (Fin.natAdd n j))) := by
  rw [L_meta_468_f, L_meta_468_cast_update, L_meta_468_nat_update]

theorem L_meta_468_core_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) : L_meta_468_core G A (fun _ => false) = false := by
  simp [L_meta_468_core]

theorem L_meta_468_core_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) {p : Fin n} (hp : p ∉ A) :
    L_meta_468_core G A (fun i => decide (i = p)) = false := by
  simp [L_meta_468_core, hp]

theorem L_meta_468_f_zero {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool) (y : Fin k → Bool) :
    L_meta_468_f G A g (Fin.append (fun _ => false) y) = g y := by
  simp [L_meta_468_f, L_meta_468_core_zero]

theorem L_meta_468_update_false {n : ℕ} (x : Fin n → Bool) (p w : Fin n) :
    Function.update x p false w = true ↔ w ≠ p ∧ x w = true := by
  by_cases hw : w = p <;> simp [hw, Function.update_of_ne]

theorem L_meta_468_update_true {n : ℕ} (x : Fin n → Bool) (p w : Fin n) :
    Function.update x p true w = true ↔ w = p ∨ x w = true := by
  by_cases hw : w = p <;> simp [hw, Function.update_of_ne]

theorem L_meta_468_f_restrict_nc {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg : ∃ y y', g y ≠ g y') (p : Fin n) (b : Bool) (hp : b = false ∨ p ∉ A) :
    ∃ x x' : Fin (n + k) → Bool,
      L_meta_468_f G A g (Function.update x (Fin.castAdd k p) b) ≠
      L_meta_468_f G A g (Function.update x' (Fin.castAdd k p) b) := by
  obtain ⟨y, y', hy⟩ := hg
  refine ⟨Fin.append (fun _ => false) y, Fin.append (fun _ => false) y', ?_⟩
  simp only [L_meta_468_f_update, Fin.append_left, Fin.append_right]
  have hzero : L_meta_468_core G A (Function.update (fun _ => false) p b) = false := by
    cases b with
    | false =>
      rw [Function.update_eq_self]
      exact L_meta_468_core_zero G A
    | true =>
      have hm : p ∉ A := hp.resolve_left Bool.noConfusion
      have he : Function.update (fun _ => false) p true = fun i => decide (i = p) := by
        funext i
        by_cases hi : i = p <;> simp [hi, Function.update_of_ne]
      rw [he]
      exact L_meta_468_core_single G A hm
  simpa only [hzero, Bool.false_or] using hy

theorem L_meta_468_f_dep_extra {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg : ∃ y, g y = false) {p : Fin n} (hp : p ∈ A) :
    ∃ x : Fin (n + k) → Bool,
      L_meta_468_f G A g (Function.update x (Fin.castAdd k p) (!x (Fin.castAdd k p))) ≠
      L_meta_468_f G A g x := by
  obtain ⟨y, hy⟩ := hg
  refine ⟨Fin.append (fun _ => false) y, ?_⟩
  have htrue : L_meta_468_core G A (Function.update (fun _ => false) p true) = true := by
    simp only [L_meta_468_core, decide_eq_true_eq]
    exact Or.inl ⟨p, hp, Function.update_self ..⟩
  simp [L_meta_468_f_update, L_meta_468_f_zero, hy, htrue]

theorem L_meta_468_f_dep_edge {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg : ∃ y, g y = false) (hA : L_meta_468_isolated G A)
    {p v : Fin n} (hpv : G.Adj p v) :
    ∃ x : Fin (n + k) → Bool,
      L_meta_468_f G A g (Function.update x (Fin.castAdd k p) (!x (Fin.castAdd k p))) ≠
      L_meta_468_f G A g x := by
  obtain ⟨y, hy⟩ := hg
  let z : Fin n → Bool := fun i => decide (i = v)
  refine ⟨Fin.append z y, ?_⟩
  have hv : v ∉ A := fun hm => hA v hm p hpv.symm
  have hzero : L_meta_468_core G A z = false := L_meta_468_core_single G A hv
  have hp : z p = false := by simp [z, hpv.ne]
  have htrue : L_meta_468_core G A (Function.update z p true) = true := by
    simp only [L_meta_468_core, decide_eq_true_eq]
    exact Or.inr ⟨p, v, hpv, by simp, by simp [z, Function.update_of_ne hpv.ne.symm]⟩
  rw [L_meta_468_f_update, L_meta_468_f]
  simp [hp, hzero, htrue, hy]

theorem L_meta_468_f_extra_false {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool) (hA : L_meta_468_isolated G A)
    {p : Fin n} (hp : p ∈ A) (x : Fin (n + k) → Bool) :
    L_meta_468_f G A g (Function.update x (Fin.castAdd k p) false) =
      L_meta_468_f G (A.erase p) g x := by
  rw [L_meta_468_f_update, L_meta_468_f]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [L_meta_468_core, decide_eq_true_eq, L_meta_468_update_false, Finset.mem_erase]
  constructor
  · rintro (⟨a, ha, hap, hax⟩ | ⟨u, v, huv, ⟨_, hu⟩, ⟨_, hv⟩⟩)
    · exact Or.inl ⟨a, ⟨hap, ha⟩, hax⟩
    · exact Or.inr ⟨u, v, huv, hu, hv⟩
  · rintro (⟨a, ⟨hap, ha⟩, hax⟩ | ⟨u, v, huv, hu, hv⟩)
    · exact Or.inl ⟨a, ha, hap, hax⟩
    · exact Or.inr ⟨u, v, huv, ⟨fun e => hA p hp v (e ▸ huv), hu⟩,
        ⟨fun e => hA p hp u (e ▸ huv.symm), hv⟩⟩

theorem L_meta_468_f_vertex_false {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    {p : Fin n} (hp : p ∉ A) (x : Fin (n + k) → Bool) :
    L_meta_468_f G A g (Function.update x (Fin.castAdd k p) false) =
      L_meta_468_f (G.deleteIncidenceSet p) A g x := by
  rw [L_meta_468_f_update, L_meta_468_f]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [L_meta_468_core, decide_eq_true_eq, L_meta_468_update_false,
    SimpleGraph.deleteIncidenceSet_adj]
  constructor
  · rintro (⟨a, ha, _, hax⟩ | ⟨u, v, huv, ⟨hup, hu⟩, ⟨hvp, hv⟩⟩)
    · exact Or.inl ⟨a, ha, hax⟩
    · exact Or.inr ⟨u, v, ⟨huv, hup, hvp⟩, hu, hv⟩
  · rintro (⟨a, ha, hax⟩ | ⟨u, v, ⟨huv, hup, hvp⟩, hu, hv⟩)
    · exact Or.inl ⟨a, ha, fun e => hp (e ▸ ha), hax⟩
    · exact Or.inr ⟨u, v, huv, ⟨hup, hu⟩, ⟨hvp, hv⟩⟩

theorem L_meta_468_f_leaf_true {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    {p v : Fin n} (hp : p ∉ A) (hl : L_meta_468_leaf G p v) (x : Fin (n + k) → Bool) :
    L_meta_468_f G A g (Function.update x (Fin.castAdd k p) true) =
      L_meta_468_f (G.deleteIncidenceSet v) (insert v A) g x := by
  rw [L_meta_468_f_update, L_meta_468_f]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [L_meta_468_core, decide_eq_true_eq, L_meta_468_update_true,
    SimpleGraph.deleteIncidenceSet_adj, Finset.mem_insert]
  constructor
  · rintro (⟨a, ha, rfl | hax⟩ | ⟨u, w, huw, hu, hw⟩)
    · exact (hp ha).elim
    · exact Or.inl ⟨a, Or.inr ha, hax⟩
    · by_cases huv : u = v
      · subst u
        exact Or.inl ⟨v, Or.inl rfl, hu.resolve_left hl.1.ne.symm⟩
      by_cases hwv : w = v
      · subst w
        exact Or.inl ⟨v, Or.inl rfl, hw.resolve_left hl.1.ne.symm⟩
      have hup : u ≠ p := fun e => hwv (hl.2 w (e ▸ huw))
      have hwp : w ≠ p := fun e => huv (hl.2 u (e ▸ huw.symm))
      exact Or.inr ⟨u, w, ⟨huw, huv, hwv⟩, hu.resolve_left hup, hw.resolve_left hwp⟩
  · rintro (⟨a, hav | ha, hax⟩ | ⟨u, w, ⟨huw, _, _⟩, hu, hw⟩)
    · subst a
      exact Or.inr ⟨p, v, hl.1, Or.inl rfl, Or.inr hax⟩
    · exact Or.inl ⟨a, ha, Or.inr hax⟩
    · exact Or.inr ⟨u, w, huw, Or.inr hu, Or.inr hw⟩

theorem L_meta_468_deleted_cover {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {p : V} (hS : L_meta_468_cover (G.deleteIncidenceSet p) S) :
    L_meta_468_cover G (insert p S) := by
  intro u v huv
  by_cases hu : u = p
  · exact Or.inl (Finset.mem_insert.mpr (Or.inl hu))
  by_cases hv : v = p
  · exact Or.inr (Finset.mem_insert.mpr (Or.inl hv))
  rcases hS u v (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨huv, hu, hv⟩) with h | h
  · exact Or.inl (Finset.mem_insert_of_mem h)
  · exact Or.inr (Finset.mem_insert_of_mem h)

theorem L_meta_468_twin_cover {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {p z v : V} (hp : L_meta_468_leaf G p v)
    (hz : L_meta_468_leaf G z v) (hzp : z ≠ p)
    (hS : L_meta_468_cover (G.deleteIncidenceSet p) S) :
    ∃ T : Finset V, L_meta_468_cover G T ∧ T.card ≤ S.card := by
  by_cases hv : v ∈ S
  · refine ⟨S, ?_, le_rfl⟩
    intro a b hab
    by_cases ha : a = p
    · subst a
      exact Or.inr (hp.2 b hab ▸ hv)
    by_cases hb : b = p
    · subst b
      exact Or.inl (hp.2 a hab.symm ▸ hv)
    exact hS a b (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hab, ha, hb⟩)
  · have hvs : v ≠ p := hp.1.ne.symm
    have hzs : z ∈ S :=
      (hS z v (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hz.1, hzp, hvs⟩)).resolve_right hv
    refine ⟨insert v (S.erase z), ?_, ?_⟩
    · intro a b hab
      by_cases ha : a = p ∨ a = z
      · have hb : b = v := ha.elim (fun he => hp.2 b (he ▸ hab)) (fun he => hz.2 b (he ▸ hab))
        exact Or.inr (Finset.mem_insert.mpr (Or.inl hb))
      by_cases hb : b = p ∨ b = z
      · have ha' : a = v := hb.elim (fun he => hp.2 a (he ▸ hab.symm)) (fun he => hz.2 a (he ▸ hab.symm))
        exact Or.inl (Finset.mem_insert.mpr (Or.inl ha'))
      have h := hS a b (SimpleGraph.deleteIncidenceSet_adj.mpr
        ⟨hab, fun he => ha (Or.inl he), fun he => hb (Or.inl he)⟩)
      exact h.imp (fun hm => Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨fun he => ha (Or.inr he), hm⟩))
        (fun hm => Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun he => hb (Or.inr he), hm⟩))
    · exact (Finset.card_insert_le _ _).trans_eq (Finset.card_erase_add_one hzs)

theorem L_meta_468_delete_isolated {V : Type*} {G : SimpleGraph V} {A : Finset V}
    (hA : L_meta_468_isolated G A) (p : V) :
    L_meta_468_isolated (G.deleteIncidenceSet p) A :=
  fun a ha v hav => hA a ha v (G.deleteIncidenceSet_le p hav)

theorem L_meta_468_insert_isolated {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {A : Finset V} (hA : L_meta_468_isolated G A) (p : V) :
    L_meta_468_isolated (G.deleteIncidenceSet p) (insert p A) := by
  intro a ha v hav
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact (SimpleGraph.deleteIncidenceSet_adj.mp hav).2.1 rfl
  · exact L_meta_468_delete_isolated hA p a ha v hav

set_option maxHeartbeats 1000000 in
theorem L_meta_468_lower (n k c : ℕ) (g : (Fin k → Bool) → Bool)
    (hg : ∃ y y', g y ≠ g y') (hc : ∀ r, HasCircuitSize k g r ↔ c ≤ r) :
    ∀ (s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      G.IsAcyclic → L_meta_468_isolated G A → HasCircuitSize (n + k) (L_meta_468_f G A g) s →
      ∃ S : Finset (Fin n), L_meta_468_cover G S ∧ A.card + G.edgeFinset.card + S.card + c ≤ s := by
  have hg0 : ∃ y, g y = false := by
    obtain ⟨y, z, hyz⟩ := hg
    cases hy : g y with
    | false => exact ⟨y, hy⟩
    | true =>
      refine ⟨z, ?_⟩
      cases hz : g z
      · rfl
      · exact (hyz (hy.trans hz.symm)).elim
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro G dG A hG hA hs
    by_cases hAe : A.Nonempty
    · obtain ⟨p, hp⟩ := hAe
      obtain ⟨r, hr, hf⟩ := L_meta_468_fix_one (L_meta_468_f G A g) (Fin.castAdd k p) false s
        (L_meta_468_f_dep_extra G A g hg0 hp)
        (L_meta_468_f_restrict_nc G A g hg p false (Or.inl rfl)) hs
      rw [show (fun x => L_meta_468_f G A g (Function.update x (Fin.castAdd k p) false)) =
        L_meta_468_f G (A.erase p) g from funext (L_meta_468_f_extra_false G A g hA hp)] at hf
      obtain ⟨S, hS, hsize⟩ := ih r (by omega) G (A.erase p) hG
        (fun a ha => hA a (Finset.mem_of_mem_erase ha)) hf
      refine ⟨S, hS, ?_⟩
      have := Finset.card_erase_add_one hp
      omega
    by_cases hE : ∃ u v, G.Adj u v
    · obtain ⟨p, v, hpv, hchoice⟩ := L_meta_468_leaf_choice G hG hE
      have hp : p ∉ A := fun hm => hA p hm v hpv.1
      have hv : v ∉ A := fun hm => hA v hm p hpv.1.symm
      have hd := L_meta_468_f_dep_edge G A g hg0 hA hpv.1
      have hcardp := G.card_edgeFinset_deleteIncidenceSet p
      have hcardv := G.card_edgeFinset_deleteIncidenceSet v
      have hdegreep := L_meta_468_leaf_degree G hpv
      have hboundp := G.degree_le_card_edgeFinset p
      rcases hchoice with hsmall | ⟨z, hzp, hzv⟩
      · obtain ⟨b, r, hr, hf⟩ := L_meta_468_fix_two (L_meta_468_f G A g) (Fin.castAdd k p) s hd
          (fun b => L_meta_468_f_restrict_nc G A g hg p b (Or.inr hp)) hs
        cases b with
        | false =>
          rw [show (fun x => L_meta_468_f G A g (Function.update x (Fin.castAdd k p) false)) =
            L_meta_468_f (G.deleteIncidenceSet p) A g from
              funext (L_meta_468_f_vertex_false G A g hp)] at hf
          obtain ⟨S, hS, hsize⟩ := ih r (by omega) (G.deleteIncidenceSet p) A
            (SimpleGraph.IsAcyclic.anti (G.deleteIncidenceSet_le p) hG) (L_meta_468_delete_isolated hA p) hf
          exact ⟨insert p S, L_meta_468_deleted_cover hS,
            by have := Finset.card_insert_le p S; omega⟩
        | true =>
          rw [show (fun x => L_meta_468_f G A g (Function.update x (Fin.castAdd k p) true)) =
            L_meta_468_f (G.deleteIncidenceSet v) (insert v A) g from
              funext (L_meta_468_f_leaf_true G A g hp hpv)] at hf
          obtain ⟨S, hS, hsize⟩ := ih r (by omega) (G.deleteIncidenceSet v) (insert v A)
            (SimpleGraph.IsAcyclic.anti (G.deleteIncidenceSet_le v) hG) (L_meta_468_insert_isolated hA v) hf
          refine ⟨insert v S, L_meta_468_deleted_cover hS, ?_⟩
          have := Finset.card_insert_le v S
          have := Finset.card_insert_of_notMem hv
          have := G.degree_le_card_edgeFinset v
          omega
      · obtain ⟨r, hr, hf⟩ := L_meta_468_fix_one (L_meta_468_f G A g) (Fin.castAdd k p) false s hd
          (L_meta_468_f_restrict_nc G A g hg p false (Or.inl rfl)) hs
        rw [show (fun x => L_meta_468_f G A g (Function.update x (Fin.castAdd k p) false)) =
          L_meta_468_f (G.deleteIncidenceSet p) A g from
            funext (L_meta_468_f_vertex_false G A g hp)] at hf
        obtain ⟨S, hS, hsize⟩ := ih r (by omega) (G.deleteIncidenceSet p) A
          (SimpleGraph.IsAcyclic.anti (G.deleteIncidenceSet_le p) hG) (L_meta_468_delete_isolated hA p) hf
        obtain ⟨T, hT, hTS⟩ := L_meta_468_twin_cover hpv hzv hzp hS
        exact ⟨T, hT, by omega⟩
    · have hAb : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAe
      have hGb : G = ⊥ := by
        ext u v
        exact iff_false_intro (fun huv => hE ⟨u, v, huv⟩)
      have he : (fun (y : Fin k → Bool) => L_meta_468_f G A g
          (Fin.append (fun _ => false) y)) = g :=
        funext (L_meta_468_f_zero G A g)
      have hnc : ∃ y y' : Fin k → Bool, L_meta_468_f G A g (Fin.append (fun _ => false) y) ≠
          L_meta_468_f G A g (Fin.append (fun _ => false) y') := by
        simpa only [L_meta_468_f_zero] using hg
      have hfix := L_meta_468_fix_prefix (L_meta_468_f G A g) s hnc hs
      rw [he] at hfix
      have hcs := (hc s).mp hfix
      refine ⟨∅, fun u v huv => (hE ⟨u, v, huv⟩).elim, ?_⟩
      simpa [hAb, SimpleGraph.edgeFinset_eq_empty.mpr hGb] using hcs

def L_meta_468_push (N : ℕ) (C : Circuit) (op : GateOp) (i j : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [i, j]⟩], N + C.size⟩

theorem L_meta_468_push_ok (N : ℕ) (C : Circuit) (op : GateOp) (i j : ℕ)
    (hC : FanInTwo C) (hop : op = GateOp.and ∨ op = GateOp.or) :
    FanInTwo (L_meta_468_push N C op i j) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hC p hp
  · simp only [List.mem_singleton] at hp
    subst p
    rcases hop with rfl | rfl <;> simp

theorem L_meta_468_push_size (N : ℕ) (C : Circuit) (op : GateOp) (i j : ℕ) :
    (L_meta_468_push N C op i j).size = C.size + 1 := by
  simp [L_meta_468_push, Circuit.size]

theorem L_meta_468_push_out (N : ℕ) (C : Circuit) (op : GateOp) (i j : ℕ) :
    (L_meta_468_push N C op i j).output < N + (L_meta_468_push N C op i j).size := by
  rw [L_meta_468_push_size]
  change N + C.size < N + (C.size + 1)
  omega

theorem L_meta_468_push_eval {N : ℕ} (C : Circuit) (op : GateOp) (i j : ℕ)
    (x : Fin N → Bool) :
    (L_meta_468_push N C op i j).eval (List.ofFn x) =
      op.eval [(C.wires (List.ofFn x)).getD i false, (C.wires (List.ofFn x)).getD j false] := by
  have hlen : (C.wires (List.ofFn x)).length = N + C.size := by
    rw [L_meta_468_wires_eq, L_meta_468_length_wiresFrom]
    simp [Circuit.size]
  rw [Circuit.eval, L_meta_468_wires_eq]
  change (L_meta_468_wiresFrom (C.gates ++ [⟨op, [i, j]⟩]) (List.ofFn x)).getD (N + C.size) false = _
  rw [L_meta_468_wiresFrom_append, ← L_meta_468_wires_eq, ← hlen]
  exact L_meta_468_getD_snoc_eq _ _ _

theorem L_meta_468_read_input {N : ℕ} (C : Circuit) (x : Fin N → Bool) (i : Fin N) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  rw [L_meta_468_wires_eq, L_meta_468_getD_wiresFrom _ _ _ (by simpa using i.isLt)]
  simp

theorem L_meta_468_read_prefix {N : ℕ} {C D : Circuit} (h : C.gates <+: D.gates)
    (i : ℕ) (hi : i < N + C.size) (x : Fin N → Bool) :
    (D.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false := by
  obtain ⟨l, hl⟩ := h
  rw [L_meta_468_wires_eq, L_meta_468_wires_eq, ← hl, L_meta_468_wiresFrom_append]
  apply L_meta_468_getD_wiresFrom
  simpa [L_meta_468_length_wiresFrom, Circuit.size] using hi

theorem L_meta_468_or_inputs {V : Type*} [DecidableEq V] {N : ℕ}
    (π : V → Fin N) (S : Finset V) (C : Circuit) (hC : FanInTwo C) (hS : S.Nonempty) :
    ∃ D : Circuit, C.gates <+: D.gates ∧ FanInTwo D ∧ D.size + 1 ≤ C.size + S.card ∧
      D.output < N + D.size ∧
      ∀ x : Fin N → Bool, D.eval (List.ofFn x) = decide (∃ a ∈ S, x (π a) = true) := by
  induction S using Finset.induction_on with
  | empty => simp at hS
  | @insert a S ha ih =>
    by_cases h : S.Nonempty
    · obtain ⟨D, hp, hD, hsize, _, hev⟩ := ih h
      let E := L_meta_468_push N D GateOp.or D.output (π a)
      refine ⟨E, hp.trans ⟨_, rfl⟩, L_meta_468_push_ok _ _ _ _ _ hD (Or.inr rfl),
        ?_, L_meta_468_push_out .., ?_⟩
      · rw [L_meta_468_push_size, Finset.card_insert_of_notMem ha]
        omega
      · intro x
        rw [L_meta_468_push_eval, L_meta_468_read_input]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
        change (D.eval (List.ofFn x) || x (π a)) = _
        rw [hev, Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
        constructor
        · rintro (⟨v, hv, hx⟩ | hx)
          · exact ⟨v, Or.inr hv, hx⟩
          · exact ⟨a, Or.inl rfl, hx⟩
        · rintro ⟨v, hva | hv, hx⟩
          · subst v
            exact Or.inr hx
          · exact Or.inl ⟨v, hv, hx⟩
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst S
      refine ⟨⟨C.gates, π a⟩, ⟨[], by simp⟩, hC, by simp [Circuit.size],
        by have := (π a).isLt; simp [Circuit.size]; omega, ?_⟩
      intro x
      change (C.wires (List.ofFn x)).getD (π a) false = _
      rw [L_meta_468_read_input]
      simp

theorem L_meta_468_or_extras {V : Type*} [DecidableEq V] {N : ℕ}
    (π : V → Fin N) (A : Finset V) (C : Circuit) (hC : FanInTwo C)
    (ho : C.output < N + C.size) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size + A.card ∧ D.output < N + D.size ∧
      ∀ x : Fin N → Bool, D.eval (List.ofFn x) =
        (C.eval (List.ofFn x) || decide (∃ a ∈ A, x (π a) = true)) := by
  induction A using Finset.induction_on with
  | empty =>
    exact ⟨C, hC, by simp, ho, by simp⟩
  | @insert a A ha ih =>
    obtain ⟨D, hD, hsize, _, hev⟩ := ih
    let E := L_meta_468_push N D GateOp.or D.output (π a)
    refine ⟨E, L_meta_468_push_ok _ _ _ _ _ hD (Or.inr rfl),
      ?_, L_meta_468_push_out .., ?_⟩
    · rw [L_meta_468_push_size, Finset.card_insert_of_notMem ha]
      omega
    · intro x
      rw [L_meta_468_push_eval, L_meta_468_read_input]
      simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
      change (D.eval (List.ofFn x) || x (π a)) = _
      rw [hev, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
      constructor
      · rintro ((h | ⟨v, hv, hx⟩) | hx)
        · exact Or.inl h
        · exact Or.inr ⟨v, Or.inr hv, hx⟩
        · exact Or.inr ⟨a, Or.inl rfl, hx⟩
      · rintro (h | ⟨v, hva | hv, hx⟩)
        · exact Or.inl (Or.inl h)
        · subst v
          exact Or.inr hx
        · exact Or.inl (Or.inr ⟨v, hv, hx⟩)

theorem L_meta_468_incident_circuit {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
    (π : V → Fin N) (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (C : Circuit) (hC : FanInTwo C) (ho : C.output < N + C.size) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size + G.degree v + 1 ∧ D.output < N + D.size ∧
      ∀ x : Fin N → Bool, D.eval (List.ofFn x) =
        (C.eval (List.ofFn x) ||
          decide (∃ w, G.Adj v w ∧ x (π v) = true ∧ x (π w) = true)) := by
  by_cases hn : (G.neighborFinset v).Nonempty
  · obtain ⟨B, hp, hB, hsize, _, hb⟩ :=
      L_meta_468_or_inputs π (G.neighborFinset v) C hC hn
    let E := L_meta_468_push N B GateOp.and (π v) B.output
    let D := L_meta_468_push N E GateOp.or C.output E.output
    have hE : FanInTwo E := L_meta_468_push_ok _ _ _ _ _ hB (Or.inl rfl)
    refine ⟨D, L_meta_468_push_ok _ _ _ _ _ hE (Or.inr rfl), ?_, L_meta_468_push_out .., ?_⟩
    · rw [L_meta_468_push_size, L_meta_468_push_size]
      have hdeg : (G.neighborFinset v).card = G.degree v := rfl
      omega
    · intro x
      have he : C.gates <+: E.gates := hp.trans ⟨_, rfl⟩
      rw [L_meta_468_push_eval, L_meta_468_read_prefix he C.output ho]
      simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
      change (C.eval (List.ofFn x) || E.eval (List.ofFn x)) = _
      rw [L_meta_468_push_eval, L_meta_468_read_input]
      simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
      change (C.eval (List.ofFn x) || (x (π v) && B.eval (List.ofFn x))) = _
      rw [hb, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro (h | ⟨hv, w, hw, hx⟩)
        · exact Or.inl h
        · exact Or.inr ⟨w, hw, hv, hx⟩
      · rintro (h | ⟨w, hw, hv, hx⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hv, w, hw, hx⟩
  · have hadj : ∀ w, ¬ G.Adj v w := by
      intro w hw
      exact hn ⟨w, (G.mem_neighborFinset v w).mpr hw⟩
    exact ⟨C, hC, by omega, ho, by simp [hadj]⟩

set_option maxHeartbeats 1000000 in
theorem L_meta_468_edge_circuit {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
    (π : V → Fin N) (S : Finset V) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (C : Circuit),
      L_meta_468_cover G S → FanInTwo C → C.output < N + C.size →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size + G.edgeFinset.card + S.card ∧
        D.output < N + D.size ∧
        ∀ x : Fin N → Bool, D.eval (List.ofFn x) =
          (C.eval (List.ofFn x) || decide (∃ u w, G.Adj u w ∧ x (π u) = true ∧ x (π w) = true)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro G dG C hS hC ho
    have hadj : ∀ u w, ¬ G.Adj u w := by
      intro u w huw
      simpa using hS u w huw
    exact ⟨C, hC, by simp, ho, by simp [hadj]⟩
  | @insert v S hv ih =>
    intro G dG C hS hC ho
    have hrest : L_meta_468_cover (G.deleteIncidenceSet v) S := by
      intro u w huw
      obtain ⟨ha, hu, hw⟩ := SimpleGraph.deleteIncidenceSet_adj.mp huw
      exact (hS u w ha).imp (fun h => (Finset.mem_insert.mp h).resolve_left hu)
        (fun h => (Finset.mem_insert.mp h).resolve_left hw)
    obtain ⟨D, hD, hsize, hDo, hDe⟩ := ih (G.deleteIncidenceSet v) C hrest hC ho
    obtain ⟨E, hE, hEsize, hEo, hEe⟩ := L_meta_468_incident_circuit π G v D hD hDo
    refine ⟨E, hE, ?_, hEo, ?_⟩
    · rw [Finset.card_insert_of_notMem hv]
      have he := G.card_edgeFinset_deleteIncidenceSet v
      have hd := G.degree_le_card_edgeFinset v
      omega
    · intro x
      rw [hEe, hDe, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, SimpleGraph.deleteIncidenceSet_adj]
      constructor
      · rintro ((h | ⟨u, w, ⟨huw, _, _⟩, hu, hw⟩) | ⟨w, hvw, hvx, hw⟩)
        · exact Or.inl h
        · exact Or.inr ⟨u, w, huw, hu, hw⟩
        · exact Or.inr ⟨v, w, hvw, hvx, hw⟩
      · rintro (h | ⟨u, w, huw, hu, hw⟩)
        · exact Or.inl (Or.inl h)
        · by_cases hu' : u = v
          · subst u
            exact Or.inr ⟨w, huw, hu, hw⟩
          by_cases hw' : w = v
          · subst w
            exact Or.inr ⟨u, huw.symm, hw, hu⟩
          exact Or.inl (Or.inr ⟨u, w, ⟨huw, hu', hw'⟩, hu, hw⟩)

theorem L_meta_468_upper {n k c s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A S : Finset (Fin n)) (g : (Fin k → Bool) → Bool)
    (hg : ∃ y y', g y ≠ g y') (hc : HasCircuitSize k g c)
    (hS : L_meta_468_cover G S) (hsize : A.card + G.edgeFinset.card + S.card + c ≤ s) :
    HasCircuitSize (n + k) (L_meta_468_f G A g) s := by
  obtain ⟨C, hC, hCsize, hCe⟩ := L_meta_468_relabel_size (Fin.natAdd n) g c hc
  have ho : C.output < n + k + C.size := by
    by_contra! h
    have hh (x : Fin (n + k) → Bool) : C.eval (List.ofFn x) = false := by
      rw [Circuit.eval, L_meta_468_wires_eq, List.getD_eq_default]
      simpa [L_meta_468_length_wiresFrom, Circuit.size] using h
    obtain ⟨y, y', hyy⟩ := hg
    have h₁ := hCe (Fin.append (fun _ => false) y)
    have h₂ := hCe (Fin.append (fun _ => false) y')
    have hcomp (z : Fin k → Bool) :
        Fin.append (fun _ : Fin n => false) z ∘ Fin.natAdd n = z := by
      funext j
      exact Fin.append_right _ _ _
    simp only [hh, hcomp] at h₁ h₂
    exact hyy (h₁.symm.trans h₂)
  obtain ⟨D, hD, hDsize, hDo, hDe⟩ := L_meta_468_edge_circuit (Fin.castAdd k) S G C hS hC ho
  obtain ⟨E, hE, hEsize, _, hEe⟩ := L_meta_468_or_extras (Fin.castAdd k) A D hD hDo
  refine ⟨E, hE, by omega, ?_⟩
  intro x
  rw [hEe, hDe, hCe, L_meta_468_f, L_meta_468_core, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, Function.comp_def]
  constructor
  · rintro ((hg | he) | ha)
    · exact Or.inr hg
    · exact Or.inl (Or.inr he)
    · exact Or.inl (Or.inl ha)
  · rintro ((ha | he) | hg)
    · exact Or.inr ha
    · exact Or.inl (Or.inr he)
    · exact Or.inl (Or.inl hg)

theorem PEqualNP.Outside.L_meta_468 :
    ∀ (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), G.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) || g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ A.card + G.edgeFinset.card + t + c ≤ s) := by
  intro n k c t s G dG A g hG hA _ hg hc hcover hmin
  change HasCircuitSize (n + k) (L_meta_468_f G A g) s ↔ _
  constructor
  · intro h
    obtain ⟨S, hS, hs⟩ := L_meta_468_lower n k c g hg hc s G A hG hA h
    have := hmin S hS
    omega
  · intro hs
    obtain ⟨S, hS, hScard⟩ := hcover
    exact L_meta_468_upper G A S g hg ((hc c).mpr le_rfl) hS (by simpa [hScard] using hs)
