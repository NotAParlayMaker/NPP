import Mathlib
import PEqualNP.Defs

namespace Live514
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

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
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
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

end Live514

namespace Live514
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

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
  induction h with
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

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

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

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

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

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
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
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
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
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
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
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
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
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
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
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

end Live514

namespace Live514

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

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
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

def search (k : Nat) : Nat → List Nat → Bool
  | 0, ws => ws == [goal k]
  | s+1, ws => ws.length ≤ s+2 && (cov k ws &&& lo k == lo k) &&
      next (mask k) (s+2-ws.length) ws (search k s)

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

theorem search_complete {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    search k s ws = true := by
  induction s generalizing ws with
  | zero => simp [search,zero_done h rfl]
  | succ s ih =>
    have hl := run_len h
    have hn := next_complete h s rfl ws (.refl _) (search k s) (fun _ => ih)
    simp [search,hl,required h,hn]

end Live514

namespace Live514
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

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

def rows514 : List ℕ := [137, 137, 9, 9, 82, 18, 137, 82, 18, 9, 149, 212, 82, 228, 212, 9, 36, 17, 228, 21, 133, 1, 34, 100, 168, 74, 149, 232, 1, 133, 10, 100, 145, 21, 200, 9, 137, 4, 136, 8, 160, 137, 232, 32, 17, 5, 16, 160, 74, 17, 34, 36, 34, 5, 36, 192, 66, 20, 148, 9, 2, 36, 200, 68, 74, 84, 72, 160, 17, 82, 82, 18, 18, 137, 9, 82, 137, 9, 18, 106, 232, 137, 228, 232, 18, 36, 10, 228, 42, 98, 2, 5, 164, 84, 145, 106, 212, 2, 98, 17, 164, 74, 42, 208, 18, 82, 32, 80, 16, 68, 82, 212, 4, 10, 34, 8, 68, 145, 10, 5, 36, 5, 34, 36, 192, 129, 40, 104, 18, 1, 36, 208, 160, 145, 168, 144, 68, 10, 141, 139, 11, 73, 210, 50, 169, 90, 26, 41, 213, 244, 19, 244, 213, 65, 52, 81, 229, 53, 165, 65, 162, 102, 169, 90, 151, 248, 33, 141, 11, 37, 177, 29, 201, 33, 140, 6, 12, 24, 33, 152, 169, 48, 33, 65, 48, 162, 76, 65, 33, 48, 3, 7, 176, 65, 130, 12, 152, 3, 65, 33, 140, 12, 88, 112, 24, 193, 3, 114, 83, 19, 146, 201, 13, 86, 153, 25, 22, 234, 236, 11, 236, 234, 130, 44, 138, 230, 46, 102, 130, 69, 165, 86, 153, 107, 220, 6, 114, 19, 38, 78, 58, 210, 6, 112, 33, 48, 24, 6, 88, 86, 12, 6, 130, 12, 69, 176, 130, 6, 12, 3, 35, 76, 130, 65, 48, 88, 3, 130, 6, 112, 48, 152, 140, 24, 194, 3]

def xs514 : List ℕ := [0x804984010236008db60e2d8d43fd4fb593c2222a00008480236100822321b343a864f, 0xc1c5b1a87fa9f6b27c024c200811b0046da01044643668750c9e111150000424011b0, 0x110266e84ccee953003088401ca9275b005040b91a01138a40002a6682022a49d6c00, 0x3822425418705bed81718041b59ac000f3e40c04a0060814bb605480106dc4b00824f, 0x2e300836b358001e79c11212a0c382df6c0a90020db89601049f206025003040a5db0, 0x61108039524eb60088813374266774a98054cd04045493ad8008205c8d0089c52000, 0x422a0430a96aa3629ac420c80102a9bb261089010eaa5a28d8867c18104048a847890, 0x5884190020553764c2115021854b551b14cf830208091508f1208448087552d146c43]

abbrev f514 : BFn 8 := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)

theorem rows514_len : rows514.length = 276 := by decide +kernel

theorem enc_inputs514 :
    (List.ofFn fun (i : Fin 8) => (fun x : Fin 8 → Bool => x i)).map (fun a => encL a rows514)
      = xs514 := by decide +kernel

theorem enc_goal514 : encL f514 rows514 = goal 138 := by decide +kernel

theorem mask514 : mask 138 = 2 ^ rows514.length - 1 := by rw [rows514_len]; rfl

theorem proper_fail514 : ∀ zs ∈ xs514.sublists, zs ≠ xs514 →
    (cov 138 zs &&& lo 138) ≠ lo 138 := by decide +kernel

theorem no_sub514 (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 138) (goal 138) s xs514) :
    ∀ s ≤ 10, ∀ zs : List ℕ, zs.Sublist xs514 → NatRun (mask 138) (goal 138) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xs514
  · subst e; exact noRunFull s hs h
  · exact proper_fail514 zs (List.mem_sublists.2 hz) e (required h)

theorem main514 (noRunFull : ∀ s ≤ 10, ¬ NatRun (mask 138) (goal 138) s xs514) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) s → 11 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run f514 ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hr : NatRun (mask 138) (encL f514 rows514) s' (ws.map fun a => encL a rows514) :=
    Run.map (fun a : BFn 8 => encL a rows514)
      (fun a => by rw [mask514]; exact encL_inv a rows514)
      (fun a b => encL_and a b rows514) (fun a b => encL_or a b rows514) hrun
  rw [enc_goal514] at hr
  refine no_sub514 noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputs514]
  exact hsub.map _

end Live514

namespace Live514

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag <<< d).testBit i then w.testBit (i-d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

def deltaA : Nat := lo 69 ||| ((lo 69) <<< 138)

def setA (xs : List Nat) := xs.map (moveBits deltaA 69)

theorem runA {s ws} (h : NatRun (mask 138) (goal 138) s ws) :
    NatRun (mask 138) (goal 138) s (setA ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

def laneHash (i w : Nat) : Nat :=
  let m := 18446744073709551557
  let a := ((w >>> (69*i)) &&& 0x1fffffffffffffffff) + 73 * ((w >>> (138+69*i)) &&& 0x1fffffffffffffffff)
  ((a % m + 123456789)^5) % m + 1

def laneSum (i : Nat) : List Nat → Nat
  | [] => 0
  | w :: r => laneHash i w + laneSum i r

def orient (ws : List Nat) := if laneSum 0 ws ≤ laneSum 1 ws then ws else setA ws
theorem runOrient {s ws} (h : NatRun (mask 138) (goal 138) s ws) :
    NatRun (mask 138) (goal 138) s (orient ws) := by
  unfold orient
  split
  · exact h
  · exact runA h

def recipeStep (ma : Nat) (lit : Nat → Nat) (op : Nat) (stack : List Nat) : List Nat :=
  if op < 8 then lit op :: stack
  else match stack with
  | [] => []
  | a :: t => if op = 8 then (a ^^^ ma) :: t else match t with
    | [] => []
    | b :: r => (if op = 9 then a &&& b else a ||| b) :: r

def recipeVal (ma : Nat) (lit : Nat → Nat) : Nat → Nat → List Nat → Nat
  | 0, _, stack => stack.headD 0
  | t+1, ops, stack =>
    if ops = 0 then stack.headD 0 else
      recipeVal ma lit t (ops >>> 4) (recipeStep ma lit (ops &&& 15) stack)

end Live514

namespace Live514

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
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
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
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
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]

end Live514

namespace Live514

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
  induction h with
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
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
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
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

end Live514

namespace Live514

def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def hashWords : List Nat → Nat
  | [] => 0
  | a :: r => ((a % 18446744073709551557 + 123456789)^5) % 18446744073709551557 + 1 + hashWords r

def safe (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat) (rot : List Nat → List Nat) (ticket : Nat → Nat → Nat) :
    Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    scoreCheck k (s+1) ws (ticket (s+1) i) || !(next (mask k) (s+2-ws.length) ws fun zs =>
        (covers k s zs) &&
        (let zs := rot zs
         let j := idx s zs
         !(j < N s && zs.isPerm (S s j))))

theorem safe_sound {k S N idx rot ticket} {s i} (hc : safe k S N idx rot ticket s i = true)
    (hrot : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [safe,zero_done h rfl] at hc
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := (covers k s zs) &&
        (let zs := rot zs
         let j := idx s zs
         !(j < N s && zs.isPerm (S s j)))
    have hF (zs : List Nat) (hz : NatRun (mask k) (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, beq_self_eq_true, Bool.true_and,
        Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hrot hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change (scoreCheck k (s+1) (S (s+1) i) (ticket (s+1) i) || !(next _ _ _ F)) = true at hc
    rw [scoreCheck_no h] at hc
    rw [hN] at hc
    contradiction

theorem noRuns {k S N idx rot ticket} {cap : Nat}
    (hrot : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, safe k S N idx rot ticket s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hr
    obtain ⟨q,hq,j,hj,hh⟩ := safe_sound (hc s hs i hi) hrot hr
    exact ih q hq (by omega) j hj hh

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
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

end Live514

namespace Live514

def wire517 (i : Nat) : Nat :=
  let tab : Nat := (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then 0x4000000000001004045001000000000000000000000000000000000000000000000004000000000000002007000000000000000000000000000000000000000000000000000a140000000000000210a00000000000000084000000000000808420000000000000002360000000000002010a0000000000000008d000000000400080420000000000000002220000000200000100000000000000000000000000000000000000000000000000001220000000000000000000800000000000000000000000000000000000000000000000360000000010002400010040000000000009000000000400090000000000000000000000820000000100011100000000000000000000000000000000000000000000000000000100000000000009100000000000000000000000000000000000000000000000000000000008000001000000000000000000000000000000000000000000000000000000000000000000081021100000000000000000000000000002040804000000000000000000000000000040020000000000000000000000000000000000000000000000000000000000000000001000000800000000000000000000000000000000000000000000000000000000000000024a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x210000c3000000000c1029500020002000084000001000021003040a0400000000000200000030000000000100040000000000000000000000000000000000000000000000120a22008000000000020000000000000004820080000000000000000000000000000040036080000000010200000000000000000000900004000040408000000000000000040000000000000008000000000000000000000000000000000000000000000000000034008d8200000101d9451193c202020000040023600080002192410864f00000000003012ad800000010198400093c000000000000023600080002180000824f000000000030008d800000010198400093c000000000000023600080002180000824f0000000000200360000000000002000000000800000008009800000000400080000000000000000200000800000000100000002000000000000000000000000000000000000000000000200000000000010000400090000000000000000000000000000000000000000000000200000000000000000010000000000000000000000000000000000000000000000000140004820000010149451110c2020200000400212000000021124100443000000000010000c000000000080000000000000000000000000000000000000000000000000000100004800000010108400010c0000000000000212000000021000000043000000000010000400000000004100110002000200000400000000000000104000400) else (if i < 48 then 0x400000600010000080000a9071100c000280000008000000002020022418040000000400000600010000080000a9071100400028000000800000000202002241804000000040000020000000000000000011100000000000000000000000000000000000000000002033480012780000000081825f6c0010000c301201049e20600000204085db000000020044ce9520000000000a1275b000040900801130a4000226480002848d6c000000002000480012000000000081025b0000000008001200000020600000204084c0000000000200000004000000000010000040000000000000000000000000000000000000000000183052ad800000010198c000f3e00004200608142b601080102184200824f0000000018205be0000000010012c000f1a40c042006081498001000104004b00000000000000182052a0800000000110800063a000042006081408001000100004200000000000000182052a0000000000010800061a00004200608140800100010000420000000000000011000000080000000000000008000000000000000000000000000000000000000000010204b60800000010102400092040c0000040810980000000040009000000000000000404eb60000000200020374a000040900001010a400002048000080852000000000000404e940000000000020274a000040900001010a400002048000080852000000000000230008db000000101d9429593c2000200008400236100802121b040a864f else 0x1000110244b60000801054266470090040c0000040810980000000040009000000000100010424eb60000801254224750090054cd04045493ad8008205c8d0089c52000000100010424e940000801054264674a900040900001010a400002048000080852000000100010034000482080105436d471190c2020200000400212000000021124100443000100010024222000080125426457009000000000000000000000000000000000000000100010024000000080105426447009000000000000000000000000000000000000000100001520eb60080000210002700098040c4040044830980000014040009400000000100001520e22008000020000031000800004040044830080000014000000400000000100001520e22008000020000030000800004040044830080000014000000400000000008000404eb60000010210062774a100540900001010ad000820488500898520000000080000042360820010210142551b1005000000010108d000800008500090420000000080000042360000010210042550a1005000000010108d000800008500090420000000080000000000000010000042000a0000000000000000000000000000000000000000004000406e9410000080000a9275b004040b80001018a4000020682002a49d2400000004000216000d3000080000e907950042002a000084800001000223003241a040000000400001600058200080101e9471110c2022a00000480212000020221324180443)) else (if i < 96 then (if i < 80 then 0x804000032000c92042088018009b1020000000000000000000000000000000000000080400002600019204288801a90fb1024000280000008000000002020022418040000080400002600009204208801200fb10200000000000000000000000000000000000000804000022a14092042088010029bb0200000000000008400000000000080842000000804000022036092042088010209b10200080000000800980000000040008000000000804000022008092042088011009b10380000000000000000000000000000000000000804000022000092042888010109b10200000000000000000000000000000000000000804000022000092042089010049b1920000000000000000000000000000000000000080400002200009204208801400bb10200000000000000000000000000000000000000804000022000092042088010109b10280000000000000000000000000000000000000804000022000092042088010009b1020000000000000000000000000000000000000020420084ea1430000084000a9271b005000290a0012884000280202002a49c6c0000020420084aa152000000400081235b001000010a0012084000286000002848c6c0000020420084aa142000000400000211b001000010a0012084000280000000808468000001080100242360000811254266570a9005000000010108d00080000850009042000000100203728e232780000200001b0046c001040443448310c9e000140000004011b0 else 0x10024a84c8ee0130000080008a927110040002800000080000000020200224180400010020a87f88e012780008000801a0046c00100004300001049e000000000000011b0010020a85ca8f2b2000008000811a00061a0000420060814080010001000042000000010020a84c88e01200000800080120000000000000000000000000000000000000000002a041008620360924420c8010289b1220008000002080098005400104040a000000002804100062000092442088010289b1220000000000000000000000000000000000000220010186053e0804000400112800063a008042006081498005400104044a00000000220010086003608040004001028000220008000002080098005400104040a000000000b04210c6ee942920c21cd43646ffb921040910a01130a40002a048000080856800000a0420086aa142920420c8010029bb021000010a0012084000280000000808468000009040100260000920c218d43644fb1920000000000000000000000000000000000000080c0000262360920430a901425dbb1205000000010108d00080000850009042000000804010016000d820c218d43ec4fb19242222a00008480236100822321b343a864f000804000232000cb204208801c10bb502020002000084000001000021003040a0400000804000062214092042088010009bb0200000008001008400000000000000046800000804000032008d92042089019849b193c000000000000023600080002180000824f) else (if i < 112 then 0x61008029100000018801212004202db08000000000000000000000000000000000000610080291000000088012120042024a080000000000000000000000000000000000004110803140448000008133742645640980544d04045011200008205c890001410000022a0430a96a03629ac420c8010289bb260088000caa1a0098867400104040a005890022a0430896a81429ac420c80102a9bb221089010eaa5a28d8867c18104048a84789002280430a16aa3629ac420880102a9bb260088000ca85a28d8862000004008884789002280430a16a00029ac42088010289bb260080000ca8120000862000000000000589002220430a94aa14218c000400002a19b241080010ea8120840862800000008084789002220030a968036298c000400102809b260088000caa1a0098867400104040a00589002200030b348001278c000000003809f6c0090000cb81201049e200000000000059b002200030a358000e38c0000000c3829f240280020ca896000087200021003040a5c9002020420896aa362088000400002211b001008010a005a28d80028000040088846800020000008524eb60088000000022274a000048900001492ad80002048040088852000020000008120a360088000000002210a0000080000004828d800000000400888420000200000081000000088000000002000a0000000000000000000000000000000000000010120a85da8e23208000820080130000800004040044830080000014000000400000 else 0x6190c039526eb609a8c33bf43667ffb9a054cd04045493ad8008205c8d0089c5200006190c03912600009a8c339f43664ffb9a0000000000000000000000000000000000006110823956ceb720888133742e7775b98054cd048455b3ad800a265c8d028dcd6c00061108039d24fbe0088813374276f74af9a54cd46047493ed8009205d8d00cbc52000061108039534ebed8888133743fe774a9bc54cd04045493afb608285c8f1889c5a24f061108039534eb648a881337436f775b98c74ed240454d3af9208205c8f11add52443061108039524eb60088813374267774a98054cd04045493ad8008205c8d0089c52000061108039524eb60088813374266f74af8054cd04045493ad8008205c8d0089c52000061108039524eb60088813374266774a98054cd04045493ad8008205c8d0089c520000611080391240000088813174266474a98000000000000000000000000000000000000611080391200220088813374246500098050c40404448309800800148d000940000006100822b3080012788012120043824e6c00100004300001049e000000000000011b006100822914800120880121200c3025b0800000008001200000020600000204084c00061008029310000c3880121200c302df08020002000084000001000021003040a04000610080291204b60088012130042424a98040c00000408109800000000400090000000610080291042360088012330042574a1805000000010108d00080000850009042000))) else (if i < 192 then (if i < 160 then (if i < 144 then 0x1002424008404941003080401488000000400000000000000000000000000000000001002424008205be1803080411518400093e40c04a0060814bb605480106dc4b00824f10020420084ea142001000400409251b005000010a0113084000284000000a4946c0010000400004621410010080004a9071b00400028080111884000004202002241c6c0010000020004c2152001000000489075b00400000080113084000206000002241c6c001000000000542144821000010549451b10c2020208011508612000400021124146c431000000000442140001000000409051b0040000008011108400000400000024146c000e110803b574eb6448891337c267775b9c0fccd2484d5d3ad8008245c8d018dc56c000e100802b1500004488112128043025b0c0a800208081400000000400000104004c000800082033580016780110008043801f6c0a90020c381401049e00400000104005db008000820205800164001100080c3025b040a800208081600000020600000304084c000800080020542364400110218043551b140f800208091508d0008040085010d046c000800080020500004400110008043001b040a800208081400000000400000104004c0008000000005000040001000080020000000000000000000000000000000000000000006390c33b16e00029acc339f4366cffbbe0080000ca8120000862000000000000589006300832b148000218c01212004282db2c0080000ca81200008620000000000005890 else 0x110262e84ccce953003088401ca9264a005040b91a01138a40002a6682022a49d6c00110262e84ccce953003088401c89251b0040000008011108400000400000024146c00110262e84cc8e953003088401c89225b0040000008001200000020600000204084c00110262e84cc8e953003088401c8920000040000000000000000000000000000000000110262e84cc8e953003080401c88204a005040911a01130a40002a648002080856800110262e84cc8e952003080401c00204a001040911a01130a40002a648002080856800110062c844844811003088001ca90640004040b810010182000002668202224190400110020a84ccce152001008000c09251b0040000008011108400000400000024146c00100a4640086249419234a0c8158809b1024000000000000000000000000000000000010024660084ae943003080401488211b005000010a00120840002800000008084680010024640084649410030884014a90711004000280000008000000002020022418040010024640004609410030804014a8075b005040b91a01138a40002a6682022a49d6c001002426008484953003080401489025b0040000008001200000020600000204084c001002424018605be1003080401498800061e0000420060814080010001000042000000100242400c44e9410030804014a8274a004040900001010a4000020480000808520001002424008446941003080401489051b0040000008011108400000400000024146c00) else (if i < 176 then 0x110266e84ccee953003088401ca9275b00d040b91a01138a40002a6682022a49d6c00110266e84ccee953003088401ca9275b005040b91a01138a40002a6682022a49d6c00110266e84ccee953003088401ca927110040002800000080000000020200224180400110266e84ccee953003088401ca92511005040b91a01138a40002a6682022a49d6c00110266e84ccee953003088401c28254a005040b91a01138a40002a6682020a0956800110266e84ccee953003080401ca8275b005040b91a01138a40002a6682022a49d6c00110266e84ccec953003088401ca8275b005040b91a01138a40002a6682022a49d6c00110266e84ccae953003088401c89211b005000010a001208400028000000080846800110266e84ccae953003088401c8921110040000000000000000000000000000000000110266e84ccae953003088401c89205b005040b91a01138a40002a6682022a49d6c00110266e84ccac953003088401ca82240005040b91200028200002a268202280890000110266e84c8ee953003088401ca82740005040b91201038a40002a2682022a09d2000110266e84c8ee953003088401c29275b005040b91a01138a40002a6682022a49d6c00110266e84c8ee953003088401c292500005040b91201018a40000a0682020a0952000110266c84c86e941003088401c282500005040b91201018a40000a0682020a0952000110262e84ccce953003088401ca9274a004040900001010a400002048000080852000 else 0x110266e84edee95f303088401ce927df005240bb1a01978a40012a66a3023a49f6c00110266e84ecee953303088401ca9275f005040b91a01138a40002a6682022a49d6c00110266e84cfee9df803088411db9675b93d040b91a01138a63602ae68223aa49dee4f110266e84ceee9d3003088401cb9275b01d040b91a01138a40002a6682022a49d6c00110266e84ceee953803088401da9275b025040b91a01138a40002a6682022a49d6c00110266e84ceee953103088401ca9275b005040b91a01138a40002a6682022a49d6c00110266e84ceee953003088411ca9675b905040b91a01138a40002a6682022a49d6c00110266e84ceee953003088401ca9275b005040b91a01138a40002a6682022a49d6c00110266e84cdee957823088411de9675b10d242bb1a01178a61202a6682233a49d6c43110266e84cdee957003088401ce9275b005240bb1a01178a40002a6682023a49d6c00110266e84ccefb73003088401ca9275b00d040b91a01138a40002a6682022a49d6c00110266e84cceeb73003088601ca9375b005040b91a01138a40002a6682022a49d6c00110266e84ccee953823088401da9275b005040b91a01138a40002a6682022a49d6c00110266e84ccee953103088401ca927db005040b91a01138a40002a6682022a49d6c00110266e84ccee953003088411ce9675b105040b91a01138a40002a6682022a49d6c00110266e84ccee953003088401ce9275b005040b91a01138a40002a6682022a49d6c00)) else (if i < 224 then (if i < 208 then 0x110a66e84ceae9539234a8c81d8929b10240000000000000000000000000000000000110366e94efee95f303889455eed67df905240bb1a01978a40012a66a3023a49f6c00110366e94ceeeb73003889655eed775b905040b91a01138a40002a6682022a49d6c00110366e94ceee953003889455eed675b905040b91a01138a40002a6682022a49d6c00110366e85deeeb73083088601ca9375b085040f95a055bba48002a67c2022a4dd6c00110366e84ceee953003088401ca9275b005040b91a01138a40002a6682022a49d6c0011026ee84cceeb73003098611ceb775b105540b91a01138ad000aa668a522ad9d6c0011026ee84ccee953003098401ceb275b005040b91a01138a40002a6682022a49d6c00110266e87fcee953783088401ca9a75f6c5050b91e31138b449e2a6682022a49d7db0110266e86edee95f703088401ce927df045240bb1a01978a40012a66a3023a49f6c00110266e86ccee953403088401ca9275b045040b91a01138a40002a6682022a49d6c00110266e86ccee953003088401cab275b0450c0b91a09138a40002a6682022a49d6c00110266e85dcee953083088401ca9275b085040b91a01138a40002a6682022a49d6c00110266e85ceefbf3003088401cb9a75b61f040bd3a071b9e48003a6692022e69d6c00110266e85ccee953003088401cab275b005040b91a01138a40002a6682022a49d6c00110266e85ccee953003088401ca9a75b605040b91a01138a40002a6682022a49d6c00 else 0x180000000050136480110001850a400010c4000000000000b12004000065409000043171a6eebcccee95302bcbbde5eed2ffb005be3bb1bc9978a4001aa6eaf923b4bf6c0017136eebddeeeb7308b89b775eef775b98554cf95a455bbad800aa67cad22addd6c0017136eebddeee95308b89b575eef675b985040b91a01138a40002a6682022a49d6c0017136aebddeceb7308b89b775eef774a98454cd04045493ad8008205c8d0089c5200017126eeadfdee95f38b09a521ceb27df085240bb1a01978a40012a66a3023a49f6c0017126eeaddcee95318b09a521ceb27db085040b91a01138a40002a6682022a49d6c0017126eeaddcee95308b09a521ceb275b085040b91a01138a40002a6682022a49d6c0016134a439d64eb6108b8937756ee774a98454cd04045493ad8008205c8d0089c52000132266f8edcee95318f088401caba7db2450c0b91ea9138a40862a6682022a49d7c90130266e8cdeeeb7308b088401cab275b005048b91a015baad8002a6682422ac9d6c00130266e8cdcee95308b088401cab275b005040b91a01138a40002a6682022a49d6c00112266f84ccee953007088401caba75b205040b91a01138a40002a6682022a49d6c00110b66e94ceee953923ca9cd5fed6ffb925040b91a01138a40002a6682022a49d6c00110a66e84efee95fb234a8c81de92fff025240bb1a01978a40012a66a3023a49f6c00110a66e84ceee9539234a8c81da92ffb025040b91a01138a40002a6682022a49d6c00) else (if i < 240 then 0x28200014187052ac01410000a092800061a0000420060814080010001000042000000282000141050000c01410000a08280006000000000000000000000000000000000000263000369308001a39c00212208082c46800100005b08201049f202025002000a11b01f126eeafddee95748b19a529ceb275b0c5ac0bb1a09178a40002a6682023a49d6c0019026ee86edee95f703198409ceb27df045ac0bb1a09978a40012a66a3023a49f6c0019026ee86cdee957403198409ceb275b045ac0bb1a09178a40002a6682023a49d6c00190266e84cdefb77803188419dab675b10d440b91a01138af1202e6682676ad9d6c43190266e84cdee957003188409cab275b005040b91a01138a40002a6682022a49d6c001884190000151404401150218449540010cf020200010500212080400835125100443182200100870136480510041850ac00032c4080000020800b9205400106540b0000431802424008505b6580318041958a400010c4000000000000b12004000065409000043180008002054214440111000844b051b044a800208091508400000400000124146c00180008000054014482111001854a451b104f830208091508f1208448087552d146c431800000010705b6480110001850a400090c40c0000040810b92004000065409000043180000000054336480110001850b451b10c4000008011108f1200440006542d146c43180000000054136482110001854b451110c6020200000400b1200400006552d100443 else 0x2e300836b358001e69c11212a0c3824e6c0a90020db89601049f206025003040a5db02e300836b318001e79c11212a04382df6c0a90020db89601049f206025003040a5db02e300836b158001e49c11212a0c282db6c0a90020db89601049f206025003040a5db02e300836b158001e49c11212a082804a6c0890000db81201049e206004000000059b02e300836b158000e19c11212a0c282db6c0080000ca812000086200000000000058902e3008369358001e39c11212a0c282df680a90020db89601049f206025003040a5db02e3008369158001e09c11212a0c3825b6800000008001200000020600000204084c002e300816b350000c79c11212a0c282df6c0a90020db89601049f206025003040a5db02e300816b150000c49c11212a0c3825b6c0a800208081400000000400000104004c002e3008169150000c19c11212a0c282db68000000000000000000000000000000000002e3008169150000c09c11212a0c2824a68000000000000000000000000000000000002c1008061210001c61011212a0c10244480a1002011084010419006025003040a0520282008143050000c41411000a0c3801b640a800208081400000000400000104004c00282000343358001e79410000a08380046c00100004300001049e000000000000011b0282000342258001e71410000a0818095640a90020db89601049f206025003040a5db0282000341058001e01410000a083825b6000000008001200000020600000204084c00)))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then 0x2e300836b378009e79c11212a0d382df6d8a90020db89601049f206025003040a5db02e300836b378001e79c11213a0c3c2dffc0a90020db89601049f206025003040a5db02e300836b378001e79c11212a0c382df6c0a90020db89601049f206025003040a5db02e300836b35c237e79c11233a0c3d7df7c0f90020db99709d49fa0602d5030d0e7db02e300836b35c001e79c11213a0c3c7df7c0a90020db89601049f206025003040a5db02e300836b35c001e79c11212a0e387df6c0a90020db89601049f206025003040a5db02e300836b358495e79c11212a0c382df6c0a90020db89601049f206025003040a5db02e300836b358223e79c11232a0c392df6c0a90020db89601049f206025003040a5db02e300836b358201e79c11212a0c382df6c0a90020db89601049f206025003040a5db02e300836b358123e79c11212a0c382df6c8a90020db89601049f206025003040a5db02e300836b358001efbc11212a1c383df6c0a90020db89601049f206025003040a5db02e300836b358001e79c11212a0c382df6c8a90020db89601049f206025003040a5db02e300836b358001e79c11212a0c382df6c0a90020db89601049f206025003040a5db02e300836b358001e79c11212a0c3824e6c00100004300001049e000000000000011b02e300836b358001e79c11212a08380df6c0a90020db89601049f206025003040a5db02e300836b358001e79c11212a04280ce6c0a90020db89601049f206025001000259b0 else 0x2e320836bb58015e79c11252a0c382df6c0a90020db89601049f206025003040a5db02e310c37b37e001f79c91b17e2efc7dffc4a902a0db89681049f206227003241a5db02e310837b77ceb7e79c91337e2e7f7dffc0fdcd24dfddf3bdc9fa265edd038dcf7db02e310837b37c223e79c91337e2e7d7dffc0a90020db89601049f206025003040a5db02e310837b37c001e79c91317e2e7c7dffc0a90020db89601049f206025003040a5db02e310836b778e23e79c11232a0c3b2df6c0a90424dbcde310c9f206165003044a5db02e3108179574eb6c09c91337e2e6f74af8054cd04045493ad8008205c8d0089c520002e300c36b35e201f79c11a12a0eb87df6c4a902a0db89681049f206227003241a5db02e300c36b35e001f79c11a12a0eb87df6cca902a0db89681049f206227003241a5db02e300c36b35e001f79c11a12a0eb87df6c4a902a0db89681049f206227003241a5db02e300c36b35a001e79c11212a0c383df6c0a90020db89601049f206025003040a5db02e300836bb7852be79c11212a0d382df6daa90062dbe9e150c9f306035003460a5db02e300836bb58a01e79c11212a0c3a2df6c0a90020db89601049f206025003040a5db02e300836bb58401e79c11212a0c382df6c0a90020db89601049f206025003040a5db02e300836b758e01e79c11212a0c3a2df6c0a90020db89601049f206025003040a5db02e300836b378009ff9c11213a1dbc2dfffca90020db8960127ff20e02521b040adfff) else (if i < 304 then 0x3822425418705bed01718040b49a800061e000042006081408001000100004200000038224254187049cd81718041b59ac000f3640c04a0060814bb605480106dc4b00824f3822425418505b6d81718041b58ac00070c4000000000000b12004000065409000043382242541850494d01718040b48a800060400000000000000000000000000000000003822425418405b6001718040b402800060240c04a006081498005400104c44b00000038224254085059cd81718040b598800063e00004a002000423605480102dc4200824f382242540850108d81718040b598800063e00004a002000423605480102dc4200824f382242540050094d81718041b58a400092440c0080000000b3604480006dc0900824f382000141050136c81510001a58ac00070c4000000000000b120040000654090000432f302cbeffdae01e79c11a12a8c3a3df6c0a90020db89601049f206025003040a5db02f3028beffd8e01e79c11a12a8c3a2df6c0a90020db89601049f206025003040a5db02e390c37b37e001efbcd339fe3e7cffffe0a90020db89601049f206025003040a5db02e380c36b37e001ffbc53a9aa1eb8fff6e4a902a0db89681049f206227003241a5db02e380c36b37a001efbc5329aa1c38bff6e0a90020db89601049f206025003040a5db02e3808178010000c83cd339fe34648a0920faf0281c88400b361c4882dfdd1922824f2e320836bb78037ef9c11252a1c382df6e0a98020dba9e019c9f7460354070e0a5db0 else 0x3823425518745bed81798145f7fec700f3e40c04a0060814bb605480106dc4b00824f382342541d70fbed89718061b59af000fbe40c44e0064834bb605481506dc4b40824f3823425418705bed81718041b59ac000f3e40c04a0060814bb605480106dc4b00824f38224a5418747bed81719061b5dad50af3e50c04a007091cfb60d480187dc4b04a24f3822427418785bff81718041b59bc25bf3e40c04a8061a14bb6074e0106de4f08ce4f3822425438705bedc1718041b59bc000f7e40c04a0060814bb605480106dc4b00824f382242541c74fbed81718041b5bae74af3e44c94a007091efb605684906dccb85a24f382242541970fbed89718041b59ae000f3e40c04a0064834bb605480106dc4b00824f3822425419705bed89718041b59ac000fbe40c04a0060814bb605480106dc4b00824f3822425418747bed81718041b59bc51bf3e40c04a807191cfb6054c0106dc6f14ee4f3822425418745bed83718041b5dbc511f3e60e06a0060c14bb605480106dd6f10864f3822425418707bed81718061b59ad000f3e40c04a0060814bb605480106dc4b00824f3822425418707bed81718041b59bc000f3e40c04a0060814bb605480106dc4b00824f3822425418705bed81718841b59bc000f3e40c04a0060814bb605480106dc4b00824f3822425418705bed81718041b59bc000f3e40c04a0060814bb605480106dc4b00824f3822425418705bed81718041b59ac000f3e40c04a0060814bb605480106dc4b00824f)) else (if i < 352 then (if i < 336 then 0x3e324a569950494d09f19252b4ca824a68400000000000000000000000000000000003e324a568040094001f19252b402004a001dcd919bc9130ad000ee6c8cde4898568003e300836b358137ef9d11213a5cbc2df7cce90020db89601b5bf2460256570d0a5df33d947bce54815c104131d232bc001040482d54d4f155215704188365cc9e0414101203c104a470014080d01399317f6ec4640904f66ba91418582236182e6afbfb353b864f3a2242549970fbed89f18041b59ae10af3e40c04a006483cfb605480106dccb84a24f3a22425499705bed89f18041b59ac00af3e40c04a0060814bb605480106dc4b00824f39226efc7cdee95f41719840bceba75b645ac0bb1a09178a40002a6682023a49d6c00392266fc5edee95f31718840bceba7df605240bb1a01978a40012a66a3023a49f6c00392266fc5cdee95f01718840bcaba75b605040b91a01138a40002a6682022a49d6c00392262fc5cf8fbff81718841bd9be000f3e40c04a0060814bb605480106dc4b00824f392262fc5cd8e95f01718840bc8ba0006040000000000000000000000000000000000382b465518765bed937da1cdf7fecfb1f3e40c04a0060814bb605480106dc4b00824f382a465418725bed9375a0c9b59ac9b1f3e40c04a0060814bb605480106dc4b00824f382a46540052000d8375a0c8b58808b1025aa32b9b88968023616cea272ff343ace4f382342551d74fbed89798165f7fef700fbe40c44e0064834bb605481506dc4b40824f else 0x3f326efedddee95f09f19a52bceba75b685040b91a01138a40002a6682022a49d6c003f326efeccdee95f01f19a52bceb27db005ac0bb1b89978a40012a66a7023a49f6c003f326afeffd8e95f79f19a52bccba2df6c4a90020db89601049f206025003040a5db03f326afeddd8e95f09f19a52bccba24a68400000000000000000000000000000000003f326afeddc8c95209f19252bc02a04a683dddd5ffff7b7fdc9eff7ddcde4cbc579b03e3b4e579d76fbed9bfdb3fff7fefffbfbe54cd4e047493efb60d685d8fdccbc5a24f3e3a4e578056094d83fdb3dff7ee4ffb925fefbb9bc9978af361eeeeaffffbdbfee4f3e334a77bf7cfbfff9f99377f7fff7dfffefdcd6edffdf3ffffff6e5fdfdfcfcfffff3e334a579d74fbed89f99377f7fef74afbe54cd4e047493efb60d685d8fdccbc5a24f3e334a579d74eb6d09f99377f6eef74af8454cd04045493ad8008205c8d0089c520003e334a5799745bed89f99357f7fec74afbe40c04a0060814bb605480106dc4b00824f3e324e76bb5e495f79f19a52b4eb87df6c4a902a0db89681049f206227003241a5db03e324a76bb785bfff9f19253b5dbc2dfffee9c06adbe9e15bfff74e0356df4f0adfff3e324a76bb585b7f79f19252b4cb82df6cca90020db89601049f206025003040a5db03e324a76bb58495f79f19252b4cb82df6c4a90020db89601049f206025003040a5db03e324a5699705bed89f19253b5dac24afbe40c04a0060814bb605480106dc4b00824f) else (if i < 368 then 0x400a0420286aa362920420c8010229bb061081010a081208d0002c080040488846800400a04000822a360820420c8010029200210090102024828d8005c18104048a84200040080420292aa2229a0420880100a9b12600000004224820088610101000002001090400804002062236092042088010209bb0600810008081008d00004080040408046800400804002022222092042088010009b1060000000000000000000000000000000000040020420296aa362180000400000a11b241000010e225a2848863810100008284789040020420284aa362820000400102211b041081010a081208d0002c080040488846800400100203d28e222180000200000b0002c000040442648300886101150000024010904000080020442360820010210142551b1405810008091108d00084080850409046800400000203928f2a2180000000010a00065a0000424264834088610101000042001090400000202968a3629a0000000102a11b240081000c2a5828d8861418104040a047890400000202928a222180000000000a00024000000042248200886101010000020010904000000020402360820000000102011b0400810008081008d000040800404080468003f336efffffeeb7f79f99b77feeff7dffc5fdcfb5ffddfbbdc9faa67efd23addf7db03f326efeffdee95f79f19a52bceba7df6c5ad0bb1fb9978b449f2a66a7023a49f7db03f326efefbda001f79f19a52bccb82df6c5a902b1fb89681049f286227023241a5db0 else 0x40841100202136a0400040200011100005800000000000000000000000000000000004084110020153624c20040210149551114c20202000004002120000000211241004434084110020113624c00040210109500014c00000000000002120000000210000000434084110020113624400040200041101104820002000004000000000000001040004004084110020053620c20040210141551114800000000000000000000000000000000004084110020053620400040210041550014800000000000000000000000000000000004084110020053620400040200009151104c00000000000000000000000000241004004084110020013760400040210003500014840000000000009000000000400090000004084110020013620c2004020010111110480000000000000000000000000000000000408411002001362040004820000110000480000000000000000000000000000000000408411002001362040004020000110000480000000000000000000000000000000000408411002001362040004020000010000400000000000000000000000000000000000408411002001162040004020000010000480000000000000000000000000000000000402a0430284aa142924420c80100a9bb261081010eaa120840867c181000482847890402a0430284a0002924420c8010088b1261081010eaa120000867c181000402005890402200302968a362984000400102a000260008000422482098865410104040a001090))) else (if i < 448 then (if i < 416 then (if i < 400 then 0x4084190020053760c20050210143551b1485000000010108d000800008500090420004084190020053620420050200041151b048b830208091508400080480810124146c004084190020013620400050200043100a048000000000000000000000000000000000040841500200736214000482000a9171104c0002800000080000000020200224180400408411202929b622580040200001b0002480000004224820088610101000002001090408411202809b622400040200001300004800000000000000000000000000000000004084112020493632400040200081125b0480000008001200000020600000204084c00408411003101362048004020000110000c80000000000000000000000000000000000408411002405ff60400040200021374a048040900001010a400002048000080852000408411002211362c7000402000c1129504820002000084000001000021003040a04004084110020553764c2004021014b551b14c2830208081408f1200408006152c146c434084110020413760c20040200103111b0480810008081008d000040800404080468004084110020413760c00040200103100004800000000000009000040000404080000004084110020413760400040200001111b04800000080010084000000000000000468004084110020413620400040200003101b048080000808100000000000000000000480040841100203136adc00040210199500097c000000000000023600080002180000824f else 0x422a04108862a36082c420c8010229bb021089010a8a5a28d8007c18104048a84680042280430a12aa2229ac420880102a9bb261089010eaa5a28d8867c18104048a84789042280010a12002209ac42088010288a02600890004aa482098865418104040a00109042200030a14823629ac000000102819b240081000ca81208d08624080040408047890418c35a86cabf632d20468a8090139b10680000000000000000000000000000000000418635a86ccbf772c20048600903311b049081010a081208d0002c080040488846800418435a86c9ff637c200482109e9771114c2022a00000480212000020221324180443418435a86c8bf632c2004820090131110480000000000000000000000000000000000418431a87d89f632480040200800b0006c201044643668750c9e111150000424011b0418431a86c89f63240004820080130000480000000000000000000000000000000000408e1520286bb762d20460e8010139bb069000010a001208400028000000080846800408c150020633760d20460a8010319bb0680810008081008d00004080040408046800408c150020233620d20460a8010119b106800000000000000000000000000000000004085110120253620400841254265570094800000000000000000000000000000000004084190020453760c20050210143551b1485810008091108d000840808504090468004084190020153764c2005021014b551b14c7020200010508f1208000087112d142443) else (if i < 432 then 0x422a0c30a96ea3629ac430e90142fdbb361589010eab5b28d886fc18185048b847890422a0430bb6af3f2fac420c80113a9bf6fb099052ebe5a3ddc9e7c1810404ca8479b0422a0430b96afbe29ac420c90112e9bbf7b48d052eae5a3cd8867c1810404cb847890422a0430b96af3e29ac420c80112a9bb67b089052eae5a3cd8867c1810404ca847890422a0430b96aeb629ac420c90102e9bbb6148d010eae5a38d8867c18104048b847890422a0430b96ae3629ac420c80102a9bb261089010eae5a38d8867c18104048a847890422a0430ad6eeb629ac420c80122affb2610c9910eab5b2ad8867e1c904048a857890422a0430ab7aa36ebac420c801c3abbf261289030eaade28d8877c18314078e8e7c90422a0430a97ea3669ac420c9014bedbb36d28b030eaa5e28f9a67c1810615ae947cd3422a0430a96aeb629ac420c80102a9bb261089010eaa5a28d8867c18104048a847890422a0430a96ae3629ac420c80102a9bb261089010eaa5a28d8867c18104048a847890422a0430a96ab3629ac420c80102a9bb269089010eaa5a28d8867c18104048a847890422a0430a96aa3629ac420c80102a9bb261089010eaa5a28d8867c18104048a847890422a0430a96a80029ac420c80100a8b1261089010eaa5a2008867c181000482805890422a0430a94aa3629ac420c80102a8bb261089010eaa5a28d8867c18104048a847890422a0430a14aa1429ac420c8010229bb061089010ea85228d0866c180040488847890 else 0x463b0c33ad6ea3629acc33fe4366bffb2e11c9d14eeb5b2ad886fe1dd8d048ac57890463b0c32bd6ae3629ac432fa0142bbfb2e1089414eae5a38d8867c19504048ac47890463b0433bd6aeb629acc23de4326abfbae10cdd14eee5a3ad8867e1dd0c048ac57890463a0c32b96aa3629ac432da0142abfb2e1089010eaa5a28d8867c18104048a84789046190c23bd2eeb629a8c33bf4366fffbbe054cd04467493ad8869215d8d008bc5309046190c03b526eb609a8c33bf43667ffb9e054cd04045493ad8008205c8d0089c5200043ae35b8edebf772dac468e80903b9bb269089010eaa5a28d8867c18104048a847890432a24b8ffeae372fac428c80903a9bf6e1099010eba5a29dc9e7c18104048a8479b0432a24b8edeae3729ac428c80903a9bb261089010eaa5a28d8867c18104048a84789042af1530bd6bf762dac460e80103b9bb2e9089414eae5a38d8867c19504048ac4789042ae1530a96bb762dac460e80103b9bb269089010eaa5a28d8867c18104048a84789042ae1510a0433760c2c460e8010319bb069089010a881208d0006c080040488846800422b0c31a96ea3629acc31ed4366ffbbb61589010eab5b28d886fc18185048b847890422b0431b96eeb629acc21cd4366efbbb6148d010eae5a38d8867c18104048b847890422b0431a96ea3629acc21cd4366efbbb61089010eaa5a28d8867c18104048a847890422a0c30ad6eeb629ac430e90162fffb3615c9910eab5b2ad886fe1c985048b857890)) else (if i < 480 then (if i < 464 then 0x4884190020513624c20150208143111b048a800208081400000000400000104004c004884190020513624400150208043101b048a800208081400000000400000104004c004884190020511624c20150218143501b148f830208081400b1208448087550d004c434884190020153624c20150218143551b148f830208091508f1208448087552d146c434884190020151624c2015021814b551114cf830200080400b1208408087552d1004434884190020113624c201502181435000148f830200080400b120840808755090000434884190020111624c201502181425000148f830200080400b1208408087550900004348841900200116204001502080021000040d8100000800009000840808544090000004884110020513624400140208003100004800000000000000000000000000000000004800080020502364c20110008143011b040a810208081408d0000448004050c046c00479439aae589a412488052320800304a0c19d1d15ff9736b449eab7dcc92080c579b046bf1d33bd6fff62dacc73ff4367fffbbe95cdd14eef5b3ad886fe1dd8d048bc57890469d1d03b527ff60da8c73bf43677ffb9e854cd04045493ad8008205c8d0089c5200046951903b525ff60488853374267774a9c854cd04045493ad8008205c8d0089c5200046941902b1013620488052320043124a0c80000000000000000000000000000000000463b0c33bd6eeb629acc33ff4366fffbbe15cdd14eef5b3ad886fe1dd8d048bc57890 else 0x5086534028417f614030c0601489100004c0000000000000000000000000000000000508419002045376040105021044b551b14c5000008011108d0008040085002d146c005084190020053760c21050210549551b14cf830208091508f1208448087552d146c435084110020553764c21040210549551b14c2020208011508612000400021124146c435084110020453760c2104020050b151b04c0810008091108d0000448004042c146c005084110020453760c21040200509151b04c0000008011108400000400000024146c005084110020453760401040200409151b04c0000008011108400000400000024146c005084110020413760401040200409100004c00000000000000000000000000000000005084110020053760c21040210509550014c5030000010108f120840808754291420435084110000053760821040210508550010c5030000010108f12084080875429142043500000002044236082100000050b051b0440810008091108d0000448004042c146c00498439a86cd9f6364001582088c3325b048a800208081600000020600000304084c004884190020553764400150218043551b148f800208091508d0008040085010d046c004884190020553624c2015021814b551b14ca820208081400212000400021124104c434884190020513764c20150218142511b148f830208081408f120840808755090468434884190020513764c20150208143111b048a810208081408d0000448004050c046c00) else (if i < 496 then 0x518677e86ceffff34030c8601cb9375b05d040b91a01138a40002a6682022a49d6c00518677e86cefff735030c8601ca9375b04d040b91a01138a40002a6682022a49d6c00518677e86cdfff774030c8601ce9375b04d240bb1a01178a40002a6682023a49d6c00518677e86ccfff73c230c8611de9775b14d040b91a01138a40002a6682022a49d6c00518677e86ccfff73c230c8601dab375b04d0c1b91a09138ad0002e6e82426ac9d6c00518677e86ccfff73c230c8601da9375b04d040b91a01138a40002a6682022a49d6c00518677e86ccfff734030c8611ce9775b14d040b91a01138a40002a6682022a49d6c00518677e86ccfff734030c8601cab375b04d0c0b91a09138a40002a6682022a49d6c00518677e86ccfff734030c8601ca9375b04d040b91a01138a40002a6682022a49d6c00518677e86ccfff734030c8601ca9375b045040b91a01138a40002a6682022a49d6c00518673e86cc9ff734030c8601c89300004c0000000000000000000000000000000000518673c84c81ff600030c0601c00300000354dd5f247697ed800df1dd8de4cbc52000510a66e86ceeeb739234a8c81da92ffb065040b91a01138a40002a6682022a49d6c00510266e86deeeb73183088401ca9a75b245040b91e235baa48863a7692022a69d7c90510266e86cceeb73823088401dab275b0450c1b91a09138ad0002e6e82426ac9d6c00510266e86cceeb73003088401ca9275b045040b91a01138a40002a6682022a49d6c00 else 0x573b6efbfdeeeb739afcbbff5feffffbbe55cdf95eef5bbad886fe7fdad26afdd7c9053ae77f8edefff73daf4e8e81dabbffb26d0c9b91eab5baad8867e7e92426ae9d7c90532a66f8edeeeb739af4a8c81dabaffb2650c9b91eab5baad8867e7e92426ae9d7c90532a66f8edeaeb739af4a8c81d8ba9bb265089010eaa5a28d8867c18104048a847890522a4670a96aeb639af4a0c8158aa9bb265089010eaa5a28d8867c18104048a847890518e77e86cefff73d234e8e81da93ffb06d040b91a01138a40002a6682022a49d6c00518777e96cefff734038c9655eed775b94d040b91a01138a40002a6682022a49d6c00518777e86cefff734030c8601ca9375b04d040b91a01138a40002a6682022a49d6c0051867fe86ccfff734230d8601ce9375b04dbc3bb1a09178a4000aa6e8a123a49d6c0051867fe86ccfff734030d8611ceb775b14d540b91a01138ad000aa668a522ad9d6c0051867fe86ccfff734030d8601ceb375b04d040b91a01138a40002a6682022a49d6c0051867fe86ccfed534230d8601ce9375b045bc3bb1a09178a4000aa6e8a123a49d6c00518677e87dcfff734830c8601ca9375b0cd040b91a01138a40002a6682022a49d6c00518677e87ccfff734030c8601ca9b75b64d040b91a01138a40002a6682022a49d6c00518677e86edfff7f7030c8601ce937df04d240bb1a01978a40012a66a3023a49f6c00518677e86ecfff737030c8601ca9375f04d040b91a01138a40002a6682022a49d6c00))))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then (if i < 528 then 0x5884190020511764c2115021854a500014cf830200080400b120840808755090000435884190020511624c2115021854b501114cf830208081400b1208448087552d104c435884190020453760401150218442550a140d810008091108d00084480854409046800588419002045376040115020840b151b044d810008091108d0008448085442d146c005884190020413760c21150208502111b040d810008091108d000844808544090468005884190020413760401150208403100a048d810008091108d000844808544090468005884190020413760401150208402100a040d810008091108d000844808544090468005884190020153764c2115021854a550014cf830200090508f120840808755291420435884190020153624401150218449540014cf0202000105002120804008351251004435884110020553764c2114021854b551114c6020200000400b1200400006552d1004435884110020513764c2114021850b511b14c4810008081008f120040800654090468435884110020513764c2114021850b511114c4000000000000b120040000654090000435884110020513764c0114021850b500014c4000000000000b120040000654090000435884110020513624c21140208509101104ca830208081400212004480025524104c4357977febfdefff7348b8db775eef775b9cd54cf95a455bbad800aa67cad22addd6c0057967feafdcfff7348b0da721ceb375b0cd040b91a01138a40002a6682022a49d6c00 else 0x5884190020557f64c2115021854b551b14cf830208091508f1208448087552d146c43588419002055376cc211502185cb551b14cf830208091508f1208448087552d146c435884190020553765c211502185cb551b14cf830208091508f1208448087552d146c435884190020553764d2115021854b559b14cf830208091508f1208448087552d146c435884190020553764c2115821854b551b14cf830208091508f1208448087552d146c435884190020553764c211502185cb551b14cf830208091508f1208448087552d146c435884190020553764c2115021856b571b14cf830208091508f1208448087552d146c435884190020553764c2115021854b551b14cf830208091508f1208448087552d146c435884190020553764c2115021854a551b144f830208091508f1208448087552d146c435884190020553764c0115021854b550a14c5000000010108f12084000875409042043588419002055376440115021844b540a14cf830208091508f1208448087552d146c43588419002055376440115020844b151b04ca800208091508400000400000124146c005884190020513764c21150218542500a148f830208091508f120844808755090468435884190020513764c2115020850b101b04cf830208091508f1208448087552d146c435884190020513764c0115021850a500a14cd810008091108f120844808754090468435884190020513764401150208443101b040f810208091508d0008448085450d046c00) else (if i < 560 then 0x5884190031553764ca115021854b551b1ccf830208091508f1208448087552d146c435884190030757f64c2115021854b551b94cf8f02080d1d18f9208448087552d146c435884190030553764c2115021854bd51b74cf830208091508f1208448087552d146c435884190030553764c2115021854b551b14cf830208091508f1208448087552d146c435884190028557764c2115021854b551b14cf830208091508f1208448087552d146c43588419002455ff64c2115021856b775b14cfc3920809150af120864c88755ad956c43588419002455f764c2115021854b751b14cf830208091508f1208448087552d146c43588419002255376cf211502185cb579f14cf830208099508f1218448297572d1e6c435884190022553764f2115021854b551f14cf830208091508f1208448087552d146c4358841900207537edc211502185db551b97cf830208091508f36084c80875d2d14ee4f58841900207537e4c2115021855b551b15cf830208091508f1208448087552d146c435884190020753764d2115021854b551b14cf830208091508f1208448087552d146c435884190020753764c2115021854b551b94cf830208091508f1208448087552d146c435884190020753764c2115021854b551b16cf830208091508f1208448087552d146c435884190020753764c2115021854b551b14cf830208091508f1208448087552d146c43588419002055b764c2115021854b751b14cf830208091508f120844808755ad946c43 else 0x5885190120753764c2195125c76f571b94cf830208091508f1208448087552d146c43588519003575f764ca115021854b751b1ccf8342480d5d38f9208449487552d546c435885190020753764c2115021854b551b14cf830208091508f1208448087552d146c4358841d20205f3777c211582185eb575b14cf832a08091788f120a46a0a7572d1c6c4358841d002457ff65c211582185eb775b14cfc3ba0809158af120864e8a757ad9d6c4358841d002457ff64c2115021856b775b14cfc3920809150af120864c88755ad956c4358841d002257376df211582185eb579f14cf832a08099588f121844a2b7572d1e6c4358841d00207737edc211582185fb571b97cf832a08091588f36084ca0a75f2d1cee4f58841d0020573765c211582185eb571b14cf832a08091588f120844a0a7572d1c6c4358841d0020573764c2115021854b551b14cf830208091508f1208448087552d146c4358841920335d3776fa115021854bd51f7ccf93020c391509f5be8448087552d147df358841920285db766c2115021854b751b14cf830208091508f1208448087552d146c4358841920245dff76c211502185eb775b14cfc3920809170af120a66c88757ad9d6c4358841920205d3776c211502185cb575b14cf830208091708f120a468087572d1c6c4358841920205d3776c2115021854b551b14cf830208091508f1208448087552d146c4358841920205d3766c2115021854b551b14cf830208091708f120a448087552d146c43)) else (if i < 608 then (if i < 592 then 0x588c1d00207737edd21570a985db5dbb97cf830208091508f36084c80875d2d14ee4f588c1d0020773764d21570a9854b5dbb16cf830208091508f1208448087552d146c4358865f60285fff67c231d06195cb751b14df83030a091708f120ac4808755ad946c4358865f4020573f65c231d06195eb575b14dfc3bb1a09178af120ae6e8a777ad9d6c4358865b60285d7f77c231d06195cb575b14cf830208091708f120a468087572d1c6c4358865b402c55ff65c231d06195eb775b14cfc3920809150af120864c88755ad956c4358865b4028757fedc231d06195db551b97cf830208091508f36084c80875d2d14ee4f58865b4028557f65c231d06195cb551b14cf830208091508f1208448087552d146c4358861d202c5fff66c2115061856b775b14dfc3930a09170af120ae4c88755ad956c4358861d20285fb776c211506185cb775b14df83030a091708f120ac6808757ad9c6c4358861d20285fb767c211586185eb771b14df832b0a091788f120ac4a0a757ad9c6c4358861d20285fb766c2115061854b751b14df83030a091708f120ac4808755ad946c435886190028553764c2115061854b551b14cf830208091508f1208448087552d146c4358851d0120773765c2195925c7ef571b94cf832a08091588f120844a0a7572d1c6c43588519012475ff64c2195125c76f775b94cfc3920809150af120864c88755ad956c43588519012275376cf2195125c7ef579f94cf830208099508f1218448297572d1e6c43 else 0x59867be86cddff76c231d0619d4b755b14dfc3931a09170af120ae6c88775ad956c4359867be86cc9ff724031d0609c02304a041dc1911a09130ad000ae6c8856489856800598677e86cdfff77c031c8619dab775b14d440b91a01138af1202e6682676ad9d6c43598677e86cdfff774031c8609cab375b04d040b91a01138a40002a6682022a49d6c0059843da86cdff777c21158218deb771b14cf832a08091588f120844a0a7572d1c6c4359843da86cdff776c21158218d4b751b14cf830208091508f1208448087552d146c4359843da864dfb776c21158218d6b775b14dfc3bb1a09178af120ae6e8a777ad9d6c43598439a86cddff76c21158218d6b775b14cfc3920809150af120864c88755ad956c43598439a86cddf776c21158218d4b751b14cf830208091508f1208448087552d146c4358a6191028753764c2515061854bd51b36cf8b02080b1d08f920d448187552f146c4358a4191020553764c2515021854bd51b34cf830208091508f1208448087552d146c43588e5f4120573f65c23df1edd76f5d3b96dfefbb9a49158af360cece8affdbdb5ee4f588e1d20287fb766d21570e9854b7dbb16df83030a091708f120ac4808755ad946c43588d1d0120773764d21d71adc76f5fbb96cf830208091508f1208448087552d146c43588c1d012057376dc21d71adc7ef5fbb96cfa32a08099588f36184ca2b75f3d3eee4f588c1d002277376cf21570a985cb5fbf16cf830208099508f1218448297572d1e6c43) else (if i < 624 then 0x5aae1d30a97fb766dad570e9854bfdbb36df8b030eab5f28f9a6fc5818755af947cd35aae1d30a96bb762dad570e88502b9bb261d89010eab5b28d886fc58185448b8478905aae1d10a0573764c2d570e9854b5dbb16df8b030a891708f120ec4808755ad946c435a841900a175b764ca915021854b751b14cf8b0208095d28f920844808755ad946c435a841900a1553764ca915021854b551b14cf830208091508f1208448087552d146c435a2a0430a97ab3669ad520c9850ae9bb36d489010eaa5a28f9a67c18106548b8478d3598e7fe86cffff77d235f8e99deb7ffb16dfc3bb1a09178af120ae6e8a777ad9d6c4359877fe96cffff77c239d965dfef775b94dfc3bb1a09178af120ae6e8a777ad9d6c4359867fe86edfff7ff231d8619deb77df14dfc3bb1a09978af121ae6eab777ad9f6c4359867fe86cffffffc231d8619dfb775b97dfc3bb1a09178af360aeee8a77fad9dee4f59867fe86cdfff77c231d8619deb775b14dfc3bb1a09178af120ae6e8a777ad9d6c4359867fe86cdfff77c231d8609deb375b04dac0bb1a09178a40002a6682023a49d6c0059867fe86cdfff774031d8609ceb375b04dac0bb1a09178a40002a6682023a49d6c0059867fe86ccfff734031d8609cab375b045dc1b91a09138ad000ae6e8a566ad9d6c0059867fe868df3777c231d8619dcb551b14df832b1a091788f120ac6a0a7772d1c6c4359867be86cddff77c231d8619dcb751b14cf830208091508f1208448087552d146c43 else 0x6a2a0434bb7aa37efbc520c8a183a9bf6e1099010eba5a29dc9e7c18104048a8479b06a2a0434b97aeb6e9bc520c9a182e9bbf6148d010eae5a38d8867c18104048b8478906a2a0434b97aa36e9bc520c8a182a9bb661089010eaa5a28d8867c18104048a84789068a411143051362c41414020a083900064800000000000000000000000000000000005f977febfdffff77cab9db77dfef775b9cdfcffb5a4d5fbaf920ae6fcaf77addd6c435f967feafddfff77cab1da739deb775b1cdfc3bb1a09178af120ae6e8a777ad9d6c435e9c1d03a0573764c29d73bfc76f5ffb14dfe3bb1bc9978af121ae6eaff77bdbf6c435e951903b575ff64ca995337c76f775b9ccfcfd2484d5d3af920864dc8f55add56c435e951903b1753764ca995337c76f575b9ccf830208091508f1208448087552d146c435e941922b15d3776ca91523385cb575b1ccf830208091708f120a468087572d1c6c435e941903a0553f64c2995337c76f575b94cfcf920849150af120864c88f55ad956c435e941902b555ff64ca915233856b775b1ccfc3920809150af120864c88755ad956c435e941902b355376cfa91523385cb57df1ccf830208099508f1218448297572d1e6c435e941902b1553764da915233854b57db1ccf830208091508f1208448087552d146c435e941902b1553764ca915233854b575b1ccf830208091508f1208448087552d146c435bae7ff8edffff77daf5f8e99debfffb36dfcbbb1eab5faaf9a6fe7e9a777af9d7cd3))) else (if i < 704 then (if i < 672 then (if i < 656 then 0x78a6535438717fedc171c061b59bd000f7e40c04a0060814bb605480106dc4b00824f78a6535438517f6d4171c060b48b900064c000000000000000000000000000000000078a419143255376cf3515021a5cbd79f74cf830208099508f1218448297572d1e6c4378a419143055376cc3515021a5cbd51b74cf830208091508f1208448087552d146c43782a465438727bed9375a0c9b59ac9b1f7e40c04a0060814bb605480106dc4b00824f782242743978fbef99718041b59ae000f7e40c04a4264834bbe65490106dc4b0092df6fb439beffd9f63e79c15a32a8c3b2df6c8a90020db89601049f206025003040a5db06ebc1d36b37b363efbc572baa1c39bff6e8a90020db89601049f206025003040a5db06eb41936b359363efbc15232a1c393df6c8a90020db89601049f206025003040a5db06eb41936b359363e79c15232a0c392df6c8a90020db89601049f206025003040a5db06eb41916b151362c49c15232a0c3924a6c800000000000000000000000000000000006e3a0c36bb7aa37efbc532daa1c3abff6e1a99030fbade29dc9f7c78354078e8e7db06e3a0c36b97aa36e9bc532daa1c2abfb6e1089010eaa5a28d8867c18104048a8478906e380c36b37a223efbc5329aa1c38bff6e0a90020db89601049f206025003040a5db06e300836b358237efbc11212a1c383df6c0a91020db89609d49f2468254070c0e7db06e300836b358223e79c11212a0c382df6c0a90020db89601049f206025003040a5db0 else 0x7eb41916a055376cc3d15233a5cb57db14cf830209899708f121a4682d7572d1e6c437e3b4e77bd7efbef9bfdb3fff7fefffbfff5cdd5eeef5b3efbe6fe9dd8fdccbc5fadf7e3a4e77a97eab6f9bfdb3dff7eeeffbb65fefbb9febdfaafbe7fefebffffbfbffedf7c945b4720553f6dc339d337f7ef575b94cfe7ba9949958af36186eeaffff3d3fee4f7a2a4674b97afbef9bf5a0c9b59ae9bbf7f48d05aeae5a3cfbe67c98106dccb84fadf7a2a4674b97aeb6f9bf5a0c8b58aa9bb665089010eaa5a28d8867c18104048a84789079a67ffc7cffffffc371d861bdfbf75bf7ffcfbfba0f1f9efb60feee9a7ffef9dee4f79a67ffc7cdfff7fc371d861bdebf75b74dfc3bb1a09178af120ae6e8a777ad9d6c4379a677fc7cffffffc171c861bdbbf75bf7f44cbdba071b9efb607ee6926feef9dee4f79a677fc7cdfff7f4171c860bcabb75b64d040b91a01138a40002a6682022a49d6c0079a673fc7cd9ff7f4171c860bc8bb00064c000000000000000000000000000000000078ae5f542057376dc375f0e9b5cb5dbb16dfa32b9b899788f361ecea2f7ff3d3eee4f78ae575438737fedd375e0e9b59bd9b1f7e40c04a0060814bb605480106dc4b00824f78a65b5438757fedc371d061b5dbd51bf7ef8f06a80f1d1cfb60d4c8187dd6f14ee4f78a65b5420553f6dc371d061b5cb551b96cf8f0288091508f360c4c8087dd2d14ee4f78a6535438717fedc371c061b59bd111f7e40c04a0060814bb605480106dc4b00824f) else (if i < 688 then 0x7fbe7ffefdebff72dbf5f2fabd02b9fb6e3dddd5ffff7b7fdc9eff7ddcde4cbc579b07fb77bfffdedff7249f9d377fe66f74afc3dddd5ffff7b7fdc9eff7ddcde4cbc579b07fb67ffefdcfff7349f1da72bcabb75b6c7dddfdffff7bffdc9eff7fdede6efdd7db07fb67bfeffd9ff7e79f1d272bcc3b2df6c3fddd7ffffff7fdc9fff7dfdde7cfcf7db07fb67bfefdf9ffffc9f1d273bd9af04afffdddd5ffff7b7ffffefffddcffccbc5fbff7fb67bfefdc9ff7249f1d272bc02b04a6c3dddd5ffff7b7fdc9eff7ddcde4cbc579b07ebe5f57a0573f6dc3fdf3fff7ef5ffb96dfefbb9bc9978af361eeeeaffffbdbfee4f7ebe1d36bb7fb77efbd572fba5cbffff7edf9b030fbbdf29fdbffc783d757af9e7df37ebc1917a055376cc3dd73bfe74f5dbb96cfaf0289c99508f361c4c82dfdd3d36ee4f7eb75b57bd75ffedcbf9d377f7fff75bffefcfd6e84f5d3efb60d6cdd8fddefd5ee4f7eb65b76bb7d7ffffbf1d273b5dbd7dfffef9f06adbf9f1dfffff4e83d7df6f1effff7eb65b57a0553f6dc3f9d377f7ef575b94dfefbb9bc9978af361eeeeaffffbdbfee4f7eb65b56a0553f64c3f1d273b54b555b14dfcf939bc9170af120ee6c8cff5ad956c437eb51937b77dff7efbd95337e7eff7dffccfdfd24dfddf3bfdbfa66dedf57addf7df37eb41936b35d377efbd15233a5cbd7df7ccf93020db99709f5bfa4682d7572d1e7df37eb41916b155376ccbd15233a5cbd75b7ccf830208091508f1208448087552d146c43 else 0x804984010236008db60e2d8d43fc4fb59342222a00008480236100822321b343a864f804984010236008db60e2d8d43bd4db593c2222a00008480236100822321b343a864f804984010236008db60e258d43fc4fb593c2222a00008480236100822321b343a864f804984010236008cb60e2d8d43754fb59382222a00008480236100822321b343a864f8049840102260081b60e2d8d437d4fb593c2222a00008480236100822321b343a864f8049840102260080b60e2d8d43754fb593800000000000000000000000000000000008049840102220089340e2d8c42b40aa48300202800008080024100822300a102a820c8049840102060000360e2d8c42650fb50002222a000084800001000223003343a04008049840002220080b6062c88011109b50380000000000000000000000000000000000804980010230008cb60e258d435448a4938222020000840023610080212191022824f80418020332800927c020c00001180046d80100004300001049e000000000000011b0804180001720e2a03c020c20001130040980004040044830080000014000000400000804180000230008c34020c0000d1029501820002000084000001000021003040a0400804180000220008034020c000011000401800000000000000000000000000000000007fbf7ffffdefff72dbfdf3ffff66fffbfe3dddd5ffff7b7fdc9eff7ddcde4cbc579b07fbe7ffffddfff7fcbfdf3ffffeefffbfe7ffffffffffffffffffffffffffffffffff)) else (if i < 736 then (if i < 720 then 0x806984110276008db64e2d8d43ffcfb5b3c2222a00008480236100822321b343a864f804b84010a7601cdb60e2dcd43fd4fb593c2222a00008480236100822321b343a864f80498c010236008db60e3d8d43ff4fbf93c2222a00008480236100822321b343a864f80498421333e009ffe0e2d8d43fdcfb5ffc2322a0430848127ff00822321b343a97ff804984210a3ea08fb60e2d8d43fd6fb593c2222a00008480236100822321b343a864f80498421027e009fb60e2d8d43fd4fff93c2222a08009680236120e22321b343ace4f804984011a3652adb60e2d8d43fdcfb5f3e2222e20068c942b6110823321b763a864f8049840112364bedb60e2d8d43ff4fb593c62e2a00048c90bb6100822361b3d3a864f804984011236008db60e2d8d43ff4fb593c2222a00008480236100822321b343a864f804984011236008db60e2d8d43fdcfb5f3c2222a00008480236100822321b343a864f804984010636e08db60e2d8d43fd6fb593c2222a00008480236100822321b343a864f804984010276008db60e2d8d43fd4fb593c2222a00008480236100822321b343a864f80498401023622adb60e2dad43fd5fb593c2222a00008480236100822321b343a864f80498401023612adb60e2d8d43fd4fb593c2222a00008480236100822321b343a864f804984010236008db60e2d8d43fd4fff93c2222a00008480236100822321b343a864f804984010236008db60e2d8d43fd4fb593c2222a00008480236100822321b343a864f else 0x904bc6410a765bedb63eadcd57fd4fb593c2222a00008480236100822321b343a864f904bc6410a7649cdb63eadcd57fd4fb593c2222a00008480236100822321b343a864f90498401027601cdb61e2d8d47fd4fb593c2222a00008480236100822321b343a864f88498c012276008df60f3d8dc3ff4fbf97caa22a08089480236100c22321b343ace4f884984010276008db60f2d8dc3ff4fb593c2222a00008480236100822321b343a864f8759a4abc78a80123c8e2f9e4a242ae4081070f957f0e2e3049f2b37e782290eb11b086598c039736ebedbe8e3fbf43ff7fff9bc76efa4045cdbafb618287ebf1bbdffa64f86598c039726ebe0be8e3fbf43777fff9b854cd04045493ad8008205c8d0089c5200086598c039336008dbe8e3f9f43ff4fff9bc2222a00008480236100822321b343a864f865188039724ebe03c8a1f374277774e99854cd04045493ad8008205c8d0089c5200082698431a37e008fbece2d8d43ffcfbfb7c2a22a0ca8968023e720822321b343adedf824984018336008dbe8e2d8d43ff4fbf93c2222a00008480236100822321b343a864f814be6c94ca2c881042eadcc5a34282083306cfdf24668f60a405b97d28a8d2e1820c8149a4a94ebee09fb60e2d8d4bfd6fb593c2222a00008480236100822321b343a864f8141a0a85fa8c0923c020c000810a00469201044643668750c9e111150000424011b08141a0a84ea8e09234020c00081120040180000000000000000000000000000000000) else (if i < 752 then 0xae718836b378009e7dc31e12a0d382df6d8a90020db89601049f206025003040a5db0a86984151276008db74f2d8de3ffcfb5f3c2222a00008480236100822321b343a864fa77beeffdfaeebfb3deebfff7af6ffeefb357cfdf7f7ebffdedffbb7ffdaadbefb3bca77be6ffdfbec89fbfeeafdf7bfdeff5fbf27efff7f6eef72fff7bb7f7abbf6fb97ffa77be6ffdfaac89b3deeafde7ab4aae4eb307cfdf7f6eaf70edf7bb7f78aad2eb93bca6798017932000883dce279e621488a4eb203c44e5f6e8750edf519175888526293bca551e2cf56804899252a8f167ab40244c92074fcf154a0d7065903a7e78aa506b832ca16ae6fc4a8a009b3566acc8389088a46330302db7b2a2c506df79b2370aa522a93bc914be6e94efee9dfb63eadcd5ffd6fff93d262bb1a01978a63612ae6a323bb4bfee4f914be6e94efee9dfb63eadcd5ffd6fb593c2222a00008480236100822321b343a864f914be6e94eeee9d3b63eadcd5ffd6fff93d040b91a01138a40002a6682022a49d6c00914be6e94ecee953363eadcc5eed2fff005262bb1a01978a40012a66a3023b4bf6c00914be6e84eeee9d3b636acc81db92fff03d040b91a01138a40002a6682022a49d6c009143e6e94eeee9d3343a8d455efd675f91d040b91a01138a40002a6682022a49d6c009143e6e84efee9df34328c401cf927df01d240bb1a01978a40012a66a3023a49f6c009143e6e84eeee9d334328c401cb9275f01d040b91a01138a40002a6682022a49d6c00 else 0xb96be6fd5efefbffb77fadcdffffeffff3f66ebfba079f9efb617ee6b36ffffbfee4fb86bc6551a765bedb77fadcdf7ffcfb5f3e62e2ea0068c94bb615482336df7f3a864fb86bc6551a765bedb77fadcdf7ffcfb5f3e40c04a0060814bb605480106dc4b00824fb86bc6551a7649cdb77fadcdf7ffcfb5f3c2222a00008480236100822321b343a864fb86bc6541a725bedb777acc9b59bc9b5f3e40c04a0060814bb605480106dc4b00824fb863c2541a705bedb5738c41b59bc004f3e40c04a0060814bb605480106dc4b00824fb77be6ffdfeee9db3dfeafde7ebdafffeb707cfdfff7fbff4edf7bf7f78aaf6ffffbcaf7beefffffac89f7defbfdefaf7aaffef3afcfffffefef70edf7bf7f78abd6ebdfbcaf71a8befff8e09e7dc31e12a8d3a2df6d8a90020db89601049f206025003040a5db0ae798c37b37e009fffcf3f9fe3ffcfffffcab22a0db8968127ff20e22721b343adfffae798c37b37e009effcf3f9fe3f7cfffff8a90020db89601049f206025003040a5db0ae798c36b37a009effc73e9aa1d38bff6f8a90020db89601049f206025003040a5db0ae798c179376008dbfcf3f9fe3ffcffffbc2222a00008480236100822321b343a864fae7988179330008cbfcf379fe356c8a4fb2fbf46e5feec75bfffd5997dfdd5b6293ffae718c36b37e009f7dc31e12a0fb87df6dca902a0db89681049f206227003241a5db0ae718837b37c009e7dcb1f17e2f7c7dffd8a90020db89601049f206025003040a5db0)))) else (if i < 896 then (if i < 832 then (if i < 800 then (if i < 784 then 0xc0cd9500226337e0f6066ca8011319bf0780810008081008d00004080040408046800c0cd9500222336a0f6066ca8011119b50780000000000000000000000000000000000c0c59901222537e0740a5d254277570e9585000000010108d00080000850009042000c0c59100332116a07c024420001090046da01044643668750c9e111150000424011b0c0c59100222136a074024c20001110040580000000000000000000000000000000000c04984212b3ea2afbe0e2d8d43fdefb5b7c2222a0422cca02be710923321b363a96dfc0498401227623edb60e2d8d43ff4fbf97c2a32a08089488f361048a2361f3c3eee4fc0498401223622adb60e2d8d43fd4fb597c2222a00008480236100822321b343a864fc04180202b28a2a23c020c000011a0042580000004224820088610101000002001090bfffffffdfbfdc9f7dfffffffefdfee4fbff7efff7f7eff72ffffbf7ffbfbf7fb97ffbfffffdfd6d75ddde7ffffffffff5fffdbfffffffbddb7dff779efefefffffdffef6fbff5fbfff7dd5c9f7dfbdf37feffd6dffdeff6fefdfdb7d727ffa3e7efbfb757bdfffbfd5fbcfd7b5fffd6dbbdf37feff774ed9ef7efef155edffff7983e7efffbfdffa76fbf7beeffdffec9dfbfffbfdffffeeffffb7ffffffffffffffffffffffffffffffffffbe7bce579f76fbedbfffbffff7fffffffbe76efee047cdbefb61d687fbfdfffffa64fbdd5fbcf56955c9d653bdf37fefd5644d9ef76fef155a5d7277983e7efbfb757b876f else 0xc1c5b1a87fa9f6b27c024c200811b24e6da01044643668750c9e111150000424011b0c1c5b1a87fa9f6b27c024c200811b1046da01044643668750c9e111150000424011b0c1c5b1a87fa9f6b27c024c200811b0956da01044643668750c9e111150000424011b0c1c5b1a87fa9f6b27c024c200811b0046da01044643668750c9e111150000424011b0c1c5b1a86ea9f6b274024c20081130040580000000000000000000000000000000000c1c5b1a86789a4127c024c20080130040c00104044306061049e011140000004011b0c0cd9d01223737edf60e7dad43ff5fbf97c7222a00018588f36180822b71b3d3ea64fc0cd9d01223736adf60e7dad43ff5fbf97c2222a00008480236100822321b343a864fc0cd95212a3fb6aff60e6dad43fd7fb597c2222a00008480236100822321b343a864fc0cd9521223f36bff60e6dad43fd5fb597c2222a00008480236100822321b343a864fc0cd9501333736adfe0e6dad43fd5fb59fc2222a00008480236100822321b343a864fc0cd9501323736adf60e6dad43fddfb5f7c2222a00008480236100822321b343a864fc0cd95012637f6adf60e6dad43fd7fb597c2222a00008480236100822321b343a864fc0cd9501227737edf60e6dad43ff5fbf97c2a32a08089488f361048a2361f3c3eee4fc0cd9501223736adf60e6dad43fd5fb597c2222a00008480236100822321b343a864fc0cd9501222736a0f60e6dad43755fb59780000000000000000000000000000000000) else (if i < 816 then 0xc1cdb5a87fabf6b2fe066ca80951bbb56fa01044643668750c9e111150000424011b0c1cdb5a87fabf6b2fe066ca80911b9b56fa01044643668750c9e111150000424011b0c1cdb5a87fabf6b2fe066ca80911b8b56fa01044643668750c9e111150000424011b0c1cdb5894487a400060e6dac4a243d20001163f9524161ea40008b1fca920b0f52000c1ccb5a8628b041276066c88080108b5041ab32b1fb8b6c1049f297a27023343a5db0c1c7b5a87febf7f27c024c600811b11f6db010456e367a7d4c9e391150000c2c479b0c1c5b9a87fadf7f27c025c210853f50e7da510446437697ddc9e9111585004b4431b0c1c5b5a87faff6b37c024c2008b9b7156de0106c643668f50c9e111352002665815b0c1c5b1a97fadf6b27c0a4d254a75f704fda01044643668750c9e111150000424011b0c1c5b1a87fbdf6b6fe024c210959f5157de2124664366c752dbe111150211665015f3c1c5b1a87fadfff27c024c200831b74e6da050d46437697f4c9e1315d0000c2c531b0c1c5b1a87fa9f6b37c024c200899b0046de01044643668750c9e111150000424011b0c1c5b1a87fa9f6b2fe024c200911b1156da01044643668750c9e111150000424011b0c1c5b1a87fa9f6b2fc024c200911b0046fa01044643668750c9e111150000424011b0c1c5b1a87fa9f6b27c024c210811f004fda01044643668750c9e111150000424011b0c1c5b1a87fa9f6b27c024c200851b2046da01044643668750c9e111150000424011b0 else 0xc3efb5b8ffebf7f2fec66ce80913b9bf6fb099456ebe7a7ddc9e7d1950404cac479b0c3e5b1b8ffe9f6b27cc24c200813b09f6da090446cbe7a750c9e311150000424059b0c3c5b1a8ffa9f7f27c824c200813b10e6da018446436687ddc9e111150400cac431b0c36ba4b8ffeae3f2bec62cc80912a9bf6f3099456ebe7a7ddc9e7d1950404cac479b0c2ef9531ab7fb7effece6ded43ffffbfb7d2ab2b0eaadea8fbe77c9a3361fbebefedfc2ef9530ab6bb7e2fec66ce80113b9bf279089010eaa5a28d8867c18104048a847890c26b8431ab7ea3efbece2dcd43ffefbfb7d2ab2b0eaadea8fbe77c9a3361fbebefedfc26b8430bb6aa3f2fec62cc80113a9bf6f9099010eba5a29dc9e7c18104048a8479b0c26b8430ab6aa3e2bec62cc80113a9bf279089010eaa5a28d8867c18104048a847890c1edb5b87febf6b2fe466ca80913b9b56fa01044643668750c9e111150000424011b0c1e7b1b87fe9f7f2fc424c600913b0046fa01844643668759c9e5511504044a4011b0c1cfb5a86eebf7f2f6066ce8091339bf079081010a081208d0002c080040488846800c1cdb5a97fbff6bffe0e6dad4bfdffb5ffe2326e6436ecf52fff11937321b767a97ffc1cdb5a97faff6b2fe0e6dad4b75ffb5ffa01044643668750c9e111150000424011b0c1cdb5a96ebff6bff60e6dad4bfd7fb597c2222a00008480236100822321b343a864fc1cdb5a96eaff6b2f60e6dad4b757fb59780000000000000000000000000000000000)) else (if i < 864 then (if i < 848 then 0xd0c59500226737e174124c2004b9171f05c00028080111884000004202002241c6c00c9c5b9a87ff9f6b67c035c208853b01f6daa90466c3e7c750c9e11515000146405db0c8cd9d01227736adf60f7dadc3ff5fbf97caa22a08089480236100c22321b343ace4fc8cd9d01223716adf60f7dadc3ff5fb597cfa32a00088480b361848a2b75f3d3a864fc8cd9901223116acf60f75adc35658a4978fa30200088400b36184882975d1922824fc8cd9501227736adf60f6dadc3ff5fb597c2222a00008480236100822321b343a864fc8c59900227136ac74035c2080d3129f058a8002080894000001004021003040a4c00c7ddbdabffaff6b27e8e7fbe4a75bfff6dbbf3ff7fffffff4c9fbb7fff923f6ff7db0c7ddbdabe7bfa49ffe8e7fbf4bfd7fff9fdbf3fb5ff9f7eb67ffabffefb3bb4ffffffc7ddbdabe78fa4127e8e7fbe4a653fff0c1bf3fb5ff9f7eb449fab7fef923b4ff7db0c7d5b9abffadfff27c8a5f374a77f74efda55cd46477697fdc9e9315d8d00cbc531b0c7d5b9aaffa9f6b27c825e320853b24e6da01044643668750c9e111150000424011b0c6dd9d03b33736adfe8e7fbf43ff5fff9fc2222a00008480236100822321b343a864fc6dd9903a30104007e8e77be424418a40c0bb34245f8e461049f81196d901106211b0c3efb5b9fffff7fffece6ded4bffffbffff2bb6f6ebefefdffff7d9b7361ffefeffffc3efb5b9ffeff7f2fece6ded4b77ffbfffb099456ebe7a7ddc9e7d1950404cac479b0 else 0xd1cff7e96efffffff63eeded5ffd7fff97d262bb1a01978a63612ae6a323bb4bfee4fd1cff7e96efffffff63eeded5ffd7fb597c2222a00008480236100822321b343a864fd1cff7e96eeffff3f63eeded5ffd7fff97d040b91a01138a40002a6682022a49d6c00d1cff7e94ceffff3863eeded5fbd7f7b93f56ffdfa477bfefb60ffffdaffefffdee4fd1cff7e87feffff3fe36ece81db9bfff6ff050fd7e377bff4c9e3b77d2022e6dd7db0d1cff7e87febfff3fe36ece81d99b9b56fe01044643668750c9e111150000424011b0d1cff7e86eeffff3f636ece81db93fff07d040b91a01138a40002a6682022a49d6c00d1cff7c94ca7ffe1863eeded5f3c7d2093f56ffdf24769fefb60df9fdaffcfbf5a24fd1c7f7e87feffff37c32cc601cb9b75f6df050fd7e377bff4c9e3b77d2022e6dd7db0d1c7f7e86eeffff37432cc601cb9375f05d040b91a01138a40002a6682022a49d6c00d1c7f3e87fe9fff37c32cc601c99b0046de01044643668750c9e111150000424011b0d1c7f3e86ee9fff37432cc601c99300405c0000000000000000000000000000000000d1c5b1a87fedf7f27c124c200c19b51f6de010446c37797d4c9e11515000066547db0d0cfd7412a777fedf63eeded57fd5fb597c2222a00008480236100822321b343a864fd0cd9501227737edf61e6dad47fd5fbf97c2222a08019588636100c22321b343eee4fd0cd9501227737edf61e6dad47fd5fb597c2222a00008480236100822321b343a864f) else (if i < 880 then 0xd8cd9501227737edf61f6dadc7ff5fb597c6222a00008480b36104822365f3d3a864fd8cc9d00225737edf6177ca985db5dbf17cfa32a08099588f36184ca2b75f3d3eee4fd8c59d00227737e5f6135c2185fb571f15cf832a08091588f120844a0a7572d1c6c43d8c59901227537e4f61b5d25c77f571f95cf830208091508f1208448087552d146c43d8c59900227537ecf6135c2185db579f15cf830208099508f1218448297572d1e6c43d8c59900227537e4f6135c21855b551f15cf830208091508f1208448087552d146c43d8c59100227137edf4134c21859b500497c4000000000000b36004800065c0900824fd7dfffebefcfed537ebefffe5eed3fff0c5bf3fb5ff9f7eb449fab7fef923b4ff7db0d7dfffebefaffff3febeffff5f7d7fff9ffffffffffffffffffffffffffffffffffffd7dfffcbdda7ffe18ebeffff5f7e7f6a9bf56ffdf24769fefb60df9fdaffcfbf5a24fd7d7ffebffeffff37cbadf775efff75ffdf55cfd7e777bffdc9ebb77dad22efdd7db0d3eff7f9edefffe39efeeded5f3efdbbb7f5effdfeef7bfefbe6ff9fdaffcfbf5fadfd3eff7f8ffeffff3fef6ece81dbbbfff6ff0d9fd7ebf7bffdc9e7f7fd2426eedd7db0d3eff7f8ffebfff3fef6ece81d9bb9bf6ff099456ebe7a7ddc9e7d1950404cac479b0d36be6f9effeebffbefeadcd5fffefffb7d2ebbb1eabdfaafbe77efeb363fbebffedfd1cff7e97ffffffffe3eeded5ffdfffffff272ff7e37ffff6fff3bf7f323bf6ffffff else 0xd9cdbda96efff7fff61f7dadcfff7fbf97cfa32a08099588f36184ca2b75f3d3eee4fd9c7ffe87ffffff7fe33dc619dfbf75f7dffd3ff7e3f7ffffdbebf7fda777efdd7df3d9c7ffe86effffff7433dc609cfb37df05dac0bb1a09978a40012a66a3023a49f6c00d9c7ffe86efffff7f633dc619dfb775f15dfc3bb1a09178af120ae6e8a777ad9d6c43d9c5b9a87ffdf7f6fe135c218d5bf51f7def93466c3f7d7dfdbe9559587556f547df3d9c5b9a86efdf7f6f6135c218d5b751f15cf830208091508f1208448087552d146c43d8cfdf412a777fedf63ffdedd7ff5fbf97cfa32a08099588f36184ca2b75f3d3eee4fd8cf9d212a7fb7eff61f7dedc7ff7fbf97dfa32b0a099788f361acca2b75fbdbeee4fd8cd9d21227f37fff61f7dadc7ff5fff97cfa32a08099788f361a4ea2b75f3d3eee4fd8cd9d012677ffedf61f7dadc7ff7fff97cfe3ba0809958af36186ceab75fbdbfee4fd8cd9d01227737edf61f7dadc7ff5fbf97cfa32a08099588f36184ca2b75f3d3eee4fd8cd9d01227737e4f61f7dadc77f5fbf97cf830208091508f1208448087552d146c43d8cd9d0122573764f61f7dadc76f5fbf14cfa32a08099588f121844a2b7573d3e6c43d8cd9d01207737e5c61f7dadc77f5d3b97cfa32a08091588f36084ca0a75d3d34ee4fd8cd9d00227737e4f6177ca9855b5dbf17cf830208091508f1208448087552d146c43d8cd9901227537ecf61f75adc75f5dbf97cfa30208099508f36184c82975d3d36ee4f))) else (if i < 960 then (if i < 928 then (if i < 912 then 0xeeff9d37bb7bb7eeffcf77ffe356f9bfffbfbf47effefe7dfffffd997dfdddbe6fbffeefd9d37b37f36bfffcf7fbfe3ffdfffffcab22a0db8968127ff20e22721b343adfffeefd9937b37916beffcf77bfe3d7daffffafbf46edfefe75bffff5f97dfdf5f6adfffeefd9917b33116acffcf77bfe356d8a4ffafbf46e5feec75bfffd5997dfdd5b6293ffeef59936b37936be7dc35e32a0d392df6d8a90020db89601049f206025003040a5db0ee7b8c37bb7ea3ffffcf3fdfe3ffefffffdabb2b0fbadea9ffff7cfa3761fbebeffffe9e5b1bc7ff9f6be7d434c20a893b0046da01044643668750c9e111150000424011b0e8ed9515327736adf74f6dade3ffdfb5f7c2222a00008480236100822321b343a864fe8ec91142211148cf7476488a11088a467aab306a5baa44527ff5598352dd522293ffe7ffffffffafec9b7feefffe7af5bfffef3bffffffffffff4edffbffff9abf6ffffbce7fff7ffffabfebb7deeeffe7ab5bae4efb07cfdf7f6eaf70edf7bb7f78aad2eb93bce77be6ffffeaebfbbfeeafde7bb6abffef30fdfdfffefaffdedf7fbff7caedaeffbbcdedd9d03b37737edfe9f7fbfc7ff5fff9fcfa32a08099588f36184ca2b75f3d3eee4fdbefbdb8fffff7f6fed77ce98d5bfdbf7fff9b476ebf7f7dfdbefd5958755efd47df3d9cfffe96efffffff63ffdeddfff7fff97dfe3bb1a09978af361aeeeab77fbdbfee4fd9cfffc96cf7ffe5c63ffdeddf7f7d3b97ffeffffa4f7dfefb60dfdfdaffdfff5ee4f else 0xf9e7f3fc7ef9ffff7573cc60bc9bb00465c0000000000000000000000000000000000f9e7f3dc5cf1ffed8573cc61bd9af000f3e40c44e0066874bb605591506dc4b40824ff9e6f3fc6ad9149f6573cc40bc99800465fab32fbfbab6c527ff7dfa372ff763adffff8ed9d15327737edf75f7dade7ffdfbff7cfa32a08099588f36184ca2b75f3d3eee4ff8e7d3543a717fedf573cc61b59bd004f7e40c04a0060814bb605480106dc4b00824ff7fff7ffdfaffffbbffeefff7fbcffe4fbf57ffdf7f7ebffffffffbfffffefbffb3ffefffffffffbbdebfffeffffffbf6fae4ffbffffff7feeef7bfffffbffffffdbeb93ffefffbdbefffbf7feffc77efaa9d3bbff6fba99476fbefe7ddc9f7d7975407cece7db0effdbdbffffff6bfffcf7fbfebffffffffeab26e6dbefef52fff31f37721b767adfffeffdbdbff7dfa41e7fcf7fbeeae7bfff6c1bf3fb5ff9f7eb449fab7fef923b4ff7db0effdbdbff7bfb6beffcf7fbfeb77ffffffbffffffffffffffffffffffffffffffffffeffdbdbefffbf6beffc77ebaa9d3bbff6faa90466dbefe750c9f317175003464a5db0effcbdbef3db041e7fc77e9aa8c38aff6c1ab32b1fb8b6c1049f297a27023343a5db0eff5b9befff9f6be7dc35e32a8d3b2df6daa90466dbefe750c9f317175003464a5db0eff5b9befff9f6be7dc35e32a8d3b2df6d8a90020db89601049f206025003040a5db0eff5b9befff9f6be7dc35e32a8d3b24e6da01044643668750c9e111150000424011b0) else (if i < 944 then 0xfff7fbfeffe9fff27df3de72bc13b04e6dbdddd5ffff7b7fdc9eff7ddcde4cbc579b0fff5b9befffdf7feffd35e33addbf7df7def93466dbfff7dfdbfb5797d7576f5e7df3feffdf57b3771fedfffff7fff7fedfffffffffffffffffffffffffffffffffffffffffeffdf57a2773fedf7fffffff7ff5fff97dfefbb9bc9978af361eeeeaffffbdbfee4ffeffdb57bb715fedfffff7fff7ded8a4ffefbf46e5feec75bfffd5997dfdd5b6293fffdd5fbef7fbdfebf7d3bdf37fefdf644fdef76fef577edf72fff93f7ffbfb777b97fffbeff7fcfffbfffffff7ece9bd9bf9bffff49d45eebe7a7dfffe7d99506dccbc4fbfffbeef7fcebfbb7fffff7ecc8bd9ba9bf67fabb2fbfbafeedffff7dfa376fffebefffff9eff7fd6aff149ff77fedcdfffdcfb5f7fab32fbfbab6c527ff7dfa372ff763adffff9eff7fc7ffbf6bfff77ece8bd99b8b56ffab36fffbefef52fff7dfb772ff767adffff9eef7fc6edffddff777ecc8bdb9afff67faf3bfbfbbb7cf67ff7ffeb72fff6bffffff9eef7fc6adb149ff777ecc8bd9988b567fab32fbfbab6c527ff7dfa372ff763adffff9e7f7fc7ffffffffd73cc61bdbbf75ffff45cfdfe377bfffffe7ff7d26feefddfffff9e7f3fc7ff9fffffd73cc61bd9bf004ffe41c44e4366875bffe5591506dc4b4093fff9e7f3fc7ff9ffff7d73cc60bc9bb0046de01044643668750c9e111150000424011b0f9e7f3fc7ef9fffff573cc61bd9bf004f7e40c04a0060814bb605480106dc4b00824f else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdeffff3cfffffffff3efd6afffdfffdffff7bfffffeffffdeffcfbf5fbfffffffffffbfb16bfffffffffffdfd8b5ffffbf6ffffefef5bffffdfb7ffff7f7adfffffffffffefdfb49ffffffffefffdbfff6ffbf3fffffbf7ef67ffffffffbfff6ffffffffffffdfccf7ffed87fffffffffe7ffb93ffeffffbcffffefb61fffffffffffffee4ffffeffffeadf1ddff7ffffdfffffcffff7ffffbfbffbb7cff7fffffebffffffbffffffffdfbdff7b55ebdffffffbfffffdee4ffeffffef5ffedf7bfffd7fffffff7f7b97fffff7fffeffffffff7df3de72bcfbb7df6dfad0ff7fbfffff4c9f3b77f7023e6df7db0fff7fbfffffdfffffdfbdf77fffff74effe55cd4e477697ffffed795d8fdccbc5b3fffff7fbfefff9fffffdf3de73bddbf2dfffee9c46edbefe75bfff75f1756df4f4adfff)) else 0))))
  (tab >>> (276*(i % 16))) &&& 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def code517 (i : Nat) : Nat :=
  let tab : Nat := (if i < 2048 then (if i < 1024 then (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then 0x32eb01fa4c1031dc0000000c72d7995a34b077000000032ec453040cd01dc0000000c6d3040cae1dc550000000390bce18701302b80000000c72c0995c055d51000000031caea184c0f52b80000000c72fca6a6540c77000000000000000000000000000000dd7324c1242b8770000000331c713040cae1fc00000000000000000000000000000383c713040cae1f80000000c72c079d304887f0000000355b026568d1940c0000000cff3179d3040c770000000000cfec0a55031dc00000000033fcc52c40c770000000000000000000000000000000000000000000000000000000c72c0995c053c0000000003304c1032b8770000000000cff31545301dc000000000362d793040c770000000000d56c0995c03d400000000035dcc93040c770000000000c72c0861c057000000000039fb01a340c77000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x31cc468ba08ae1dc0000000c72c0995514c07f000000032ec45e34c1031dc0000000c72c07b93040c7f000000035ed55a34c1031dc0000000d371c4c1032b87f0000000374cc93040cae1dc0000000c7311a19ba4c0ae000000032eb02907a9031dc0000000e86c0a61a340c77000000033fcc53040c8f1dc0000000cbb11a2d032b8770000000381cc93040cae1dc0000000c72c0a55a340c77000000032eb02634c1031dc0000000cbac079d3048877000000032eb02877a9301dc0000000cbac0a19e74c077000000035ab02654c1031dc0000000c72c0a4e882b8770000000332b96184c1031dc0000000cbb114c1032b877000000031cb026568d4f1dc0000000c7311701303d4ae000000031cbce187015f4c00000000c72c098d3040c7f000000032eb0286709302b80000000d56c09953040c7f000000032eb01ea4c1031dc0000000cc72e4c1032b8770000000375c714340cd21dc0000000c731178dba4c103) else (if i < 96 then 0x31cb028fa18ae1fc0000000c72c07e94240c77000000032eb01ee4c1031dc0000000cbb11a09302b877000000032eb01e74c1031fc0000000d56c0995a33d477000000032ec4530488ae1dc0000000cff31a25302b877000000031cb5e65701614c00000000c72c0a4dfa40c77000000032eb0265545301dc0000000cfec0659514c077000000034dcb93040cae1dc0000000e42c0861c057d300000000375c7143490ae1dc0000000ccac07b13040c77000000031cb0218700f52700000000cbac0a3e862b877000000033fcc53040cae1dc0000000cbac07a930488770000000331c71a3545301dc0000000c7311a2de340c77000000031cc4530488ae1fc0000000d52c068d3040c77000000031cb026568d565440000000c6ec068d514c0770000000359cbac04c1031dc0000000c7311a19302b87f else 0x32eb02644c1031dc0000000cbb114c1032b87f000000031cb0285701302b80000000dd71c4c1242b87f000000033fc453040c9c1dc0000000c72c0995c03d48f000000033fb01e54c1031dc0000000c73104c1032b8770000000375c71303d4ae1540000000cbb117a93040c77000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000031cb01ea4c1031fc0000000ccb104c1032b877000000000000000000000000000000000000000000000000000000000000000000000000000d5b1cb013040c7f000000031cb01e7701303d40000000cbac07a93040c7f0000000375cc93040cd21dc0000000cbb11a19302b877000000000000000000000000000000000000000000000000000000000000000000000000000dd72e4c11b2b877000000000000000000000000000000c72c079d3040c7f000000033fcc5614c1031dc0000000000000000000000)) else (if i < 192 then (if i < 160 then 0xc731168d3e40cae1dc000031cb01f568d3040c77000000000000000000000000000381cbac04c1032b87700000c72d779da34c1031dc0000355b026568d3040cd700000e6f8bc72c068cae1dc000031cb02214c1032b87f00000cff1cc468f40cae1dc0000000cbac07a93040c7700000c72c0a19e7701301dc00003a1b026568d3040c7700000c72c063d3040cae1fc000032eb02184c0f52b87700000cbac08613040cba1dc000034dc713040cae1dc4500000c72c079da34c1031fc000033fb01965853040c770000000332b02184c0f52b80000000c72c0a19e74c07f000000031cc453040cd01fc0000000d5b2eb013040c77000000031cb01fa4c1031fc0000000c73114c1032b87f00000003a0e46c068cae1dc0000000c72c0861a3570770000000356c713040c77154000000000000000000000000000003a0d5ac068d031dc0000000c72ba79d3040c77000000031cb01fa70d3040c0000000c72fdb961840c77 else 0xc72c07cda34c1031dc000031cb01e768d3040c7c00000cbac09c53040cae1dc000031cb02184c1033607f00000c72ba6113040cae1dc000032eb02244c1032b87700000c72c0a19c2701302b8000031cb02184c1033647f00000dab1c4c1032b8771540000355b021868cf52b87700000c73116e93040cae1dc000031cb02184c1033a87f00000e26c0971a34c1031dc0000362d56c09953040c7700000c72c093930488ae1fc000031cc45a34d1032b87700000cbac08fd3040cae1dc000031cb02187015f4c0f500000c731168d30494ae1dc000031cc468fa19a32b87700000c72c093942488ae1dc000031cbeee3b021840c7700000cff1bb013040cae1dc000031cb0286709a34c0ae00000c72c068d96545301dc000032eb01754c1222b87700000c72c086130494ae1fc0000390bce1868d302b87700000cff318613040cae1dc000032ec45a34c1032b87700000cbac08613040cb21dc000032eb028c4c1032b877) else (if i < 224 then 0xc731668d3040cae1dc000031cb02574c1032b87f00000c72c0995a35452c1dc0000334c72c04c1032b87700000c72c07c9a34c1031dc000031cb8ed8b02184c10300000cff1cc46864c0ae1dc000031cb01e768d304650300000c7311bbda34c0ae1dc000031cb021868d5f5407700000e8b3fb01e74c1031dc000031cb02264c1032b87f00000cbac09953040cae1fc000031cb02654c10325c7700000c7311a096b4c0ae1dc000031cc45e7709a34c10300000c72c09113040cae1fc000031cc45a34c1033a87700000c72c079d3040c77154000031cc45a34c1033607700000c72c079da34c1221dc000031cc45a34c1032d47700000cbac064d3040cae1dc000031cc45a34c1033347700000cbec08613040cae1dc000033fcc6654c1032b87700000cbac07393040cae1dc000031cb02655853040c7f00000cbac086130488ae1dc000032eb017e4c1032b87700000c73114c1032b877118000032eb01ea4c1031dc45 else 0xc72c0995a3545301dc000031cc456b4c1032b87700000c730eb013040cae1dc0000000cbb114c1032b87700000c72c079da34c1081dc000031cb02184c0f62b87f00000c72c09a53040cd01fc000031cb01844c1032b87f00000dd71c4c10334877154000031cb01e768d304107700000c73114c1032b87f1dc000031cb01e768d524c07700000c72c09393040cae1fc000031cb96ba8613040c7700000c72c079d3040c77158000032eb02044c1032b87700000d2b1c68d3040cae1dc000031cc45a34c1032d07700000c72f3861a34c1192b8000031cc4da34c1032b87700000cbac07253040cae1dc000031cc468b5ad032b87700000c72c0861a3575451dc0000000c72c079d3040c7f00000c72c0795a34c1031dc0000381cff334c1032b87700000c6ec05bd3040cae1dc0000332b02184c1033487700000cff31c713040cae1dc000031cb026568cf523c7700000e6f56c72c068d031dc000031cb026568d2c1dc6e))) else (if i < 384 then (if i < 320 then (if i < 288 then 0xc72c086130414ae1fc000031cc45a34b9032b87700000d56c0795a34c1031dc000031cc468068d302b87700000cbac08253040cae1dc000031cc45ac4c1032b87700000c6ec04c1032b877158000031cb028679d301dc4500000c72c079dbc4c1031dc000031cb01e768d3046c7700000d173168d3040cae1dc0000356c72c04c1031dc4500000ccac09953040cae1dc000031cb028979da34c07700000c72c0995c0545301dc0000390b02a068d302b87700000c72c07bda34c1031dc000031cb02634c1031dc4500000dab2eb013040cae1dc000031cb02a94c1032b87f00000c72ba8613040cae1fc000031cb01e76913040c7700000cbac08613040cb31dc0000336bba184c1032b87700000c72e0b02184c1031fc0000355b02654c1031dc4500000e8b56b01a34c1031dc000031cb025768d2c40c7700000cbac099530488ae1dc000031cc46b74c1032b87700000cbac08613040ccc1dc000031cb01e768d3040c77 else 0xcff3168d3040cae1dc000031cc45a34c0f52b87700000c731178da34c1031dc000031cb0286709302b84500000cbac08613046cae1dc000033fc72c0a3e862b87700000d5b1bb01a34c1031dc000031cc46866d5302b87700000cbaee8613040cae1dc000032ec453040cae1dc4500000c72c0a19e7709a34c0000031cb026568d2f40c7700000c72ee79da34c1031dc000031cc5da34c1032b87700000c72c086130490ae1fc000033fc72c079dc24c10300000c731168d3340cae1dc000031cb02184c0f52b87f00000c72bf79da34c1031dc000031cb01e768d304587700000c72c0801a34c1031dc000032eb01774c1222b87700000cbac086130488d01dc000032eb02364c1032b87700000c72c07e9934c1031dc000031cc46e068d3040c7700000c72c079da34c5031dc000031cb01f968d3040c7700000d5f1cb02654c1031fc000031cb01e74c1031fc4500000cbac08613040c9f1dc000031cc45a34e9032b877) else (if i < 352 then 0xc731168d3040cae1fc000031cb01954c1032b87700000c72c0995a35453035c000031cb028c4c1032b87f000000000000000000000000000381c72c04c1032b87f00000cfed25d53040cae1dc000032eb2a184c1032b87700000000000000000000000000031cc51a34c1032b87700000000000000000000000000031cbce18701303d4ae00000c7311a19a34c0ae1dc0000344b01f568d3040c7700000c72c07c1a34c1031dc000032eb02184c10329c7700000c72c08dd3040cae1fc000033fc73114c1032b87700000c72c07a1a34c1031dc000031cb02184c1032e87f00000d56c079da34c1031dc000031cb01e768d304187700000c72c08613040ccf1dc000031cb01e768d3040c7900000c72c0861a33d49c1dc000031cb01d94c1032b87f00000c72c0a19754c0ae1fc000032eb01754c1033407700000c72c0a1a184c0ae1fc000032eb02654c1032b87700000c72c09393040cd01fc0000355b026568d514c077 else 0xc72c05f93040cae1fc000031cb01ce4c1032b87f00000000000000000000000000031cb02714c1032b87f00000000000000000000000000000000000000000000000000cc71ca25a34c0ae1dc0000355b02657ed3040c7700000cbac09953040c8f1dc000031cb026568d1940c8f00000c72c0995a3585501dc0000327b01e768d3040c7700000000000000000000000000000000000000000000000000c72c064d3040cae1fc000033fccec079d3040c7700000c72c08fd3040cae1fc000031cb01ee68d3040c77000000033fcc53040cae1dc000031cb028664d302b87700000c72c079da34c1071dc0000335c45a34c1032b87700000c731179d6b4c1031dc000031cb01ea68d3040c7700000c6ec068d3040c8f1dc0000331c71a34c1032b87700000c72ba5d53040cae1dc000031cb02184c1032c87f00000c7311a19c04c0ae1dc000031cb01754c1222b87f00000c72c08913040cae1fc000033fccf124c1032b877)) else (if i < 448 then (if i < 416 then 0xe42c0861c04c0f52b8000000000000000000000000000000000000000000000000031cb7de768d3040c7700000c731168d30488ae1dc0000344b026568d614c07700000c731168d3040cbf1dc000031cb026068d5d4c07700000000000000000000000000031cb01e76ad3040c7700000e2f1cc45a34c0ae1dc000031cb01e74c1221dc4500000d56c0995a340cee1dc000031cb0265545301dc4500000e471bb01a34c0ae1dc0000371cbac04c1032b87700000c72c0a3e8668cae1dc000031cc453040cae1dc5500000c72c086143490ae1dc000000000000000000000000000cbac09953040cd01dc0000375cff334c1032b87700000cbac08613040cbb1dc000031cc45c25ad3040cae000000000000000000000000000381c72c068d2c40c7700000000000000000000000000031cb01e768d303e87700000c72c086130488ae1fc000031cc45a34c1032b87c00000cfec06653040cae1dc000031caea184c1032b877 else 0xc73114c1032b877158000031cb02654c1222b87f00000c72ba9953040cae1dc000031cc468268d302b87700000c731168d3040ccc1dc000031cc61a34c1032b87700000c72c0861a3555033700000000c73114c1032b87f00000c72c08613040cd21fc0000344b01e768d3040c7700000c72c379da34c1031dc000031cb0265509222b87700000d431c68d3040cae1dc000031cb01ed68d3040c7700000c731168d30410ae1dc000031cb01e7709a34c10300000c72c0861a346503270000031cb01e76e53040c7700000cff1cb02654b1031dc000032eb02184c1262b87700000c72c0861a3511031dc000031cb01934c1222b87700000c731168d30465032b8000031cb01c94c1032b87f00000e8b3fc453040cae1dc000031cb02184c1033307f00000c72f6b026568d2c1dc000031cb02724c1032b87f00000000000000000000000000000000000000000000000000c72c05d53040cae1fc0000331c71a34c10323c77) else (if i < 480 then 0xc731168d3046cae1dc0000355b7a6568d3040c7700000d5b1cc45a34c1031dc0000355b026568d5740c7700000cff1cc45e74c1031dc000033fc453040cae1dc5c00000c72dc8613040cae1fc000031cb02094c1032b87f00000cfec0a25964c0ae1dc000031cbce1868d5f4c07700000c73116913040cae1dc000031cc45a34c1032b87700000cfec06593040cae1dc0000355b026068d3040c7700000cbae3b02184c1031dc000031cc45a34c1082b87700000c72c08613046cae1fc000031cc45e068d3040c7700000c72c086130488d01fc000036ac72c04c1032b87f00000c72f5aea184c0ae1dc0000375c713046cae1dc4500000c72c07c5a34c1031dc000031cb01e76a53040c7700000000000000000000000000031cb02184c0ff2b87f00000c72c08613040cb31fc0000375c72c04c1222b87f00000c72c08d93040cae1fc000000000000000000000000000000000000000000000000031cc21e768d3040c77 else 0xc72c09953040cae1fc000031cc45a34c1162b87700000c72ee8613040cae1fc000031cb01e768d514c07700000ccac05ed3040cae1dc0000331c713040cae1dc4500000cbac09a53040cae1dc000031cb9a187f13040c7700000c72c07e9a34c1031dc000032ec456b4c1032b87700000c731168d3140cae1dc000031cb01b44c1032b87700000d5b3ac72c04c1031dc0000355d41a34c1032b87700000cbb1cb01e74c1031dc000031cbeac079da340c7700000c72c07a93040c77114000031cb01754c1033407f00000c731568d3040cae1dc000031cb01e968d3040c7700000c72c064d3040cae1dc000031cb01f868d3040c7700000cbac0861ea4c1031dc000031cb028568d302b87700000c73116f13040cae1dc0000327aea184c1032b87700000e0755b01a34c1031dc000031cb01e74c1031dc6900000c7311a19e768d301dc000032eb02184c1032707700000c731168d3040cc61dc000031cb02184c10327c7f)))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then 0xc73114c1032b87f114000033fc73117093040cae00000c72d7861a3519301dc0000331c6da34c1032b87700000cbb0eb013040cae1dc000032eb01e768d3040c7700000c72e6861a3575301dc000031cc45a34c1062b87700000c72c0a3e8679da31dc000032eb025a4c1032b87700000c72c08614340cd21dc000032eb018f4c1032b87700000c72ca8613040cae1fc0000355c45a34c1032b87700000cc71c6e53040cae1dc000031cc3ec04c1032b87700000d4b1c68d3040cae1dc000032eb024e4c1032b87f00000c72c07b93040c77114000031eb02184c1032b87f00000c72c0861303d4ae1540000355cfec09953040c7700000cc71c79da34c1031dc000032eb01da4c1032b87700000c7311a19c268d302b8000032eb02224c1032b87700000c72c0701754c0f52b80000388c71a34c1032b87700000c7311a19302b877114000031cc45a34c1032bc7700000cbac0861514c0ae1dc000033fb01964c10323c77 else 0xc72c0a3e86709a32b8000031cb01e768d3045c7700000cff1cb02634c1031dc000031cc45a34c1072b87700000c6ec068d614c1031dc000031cb02657ed514c07700000c72c079d3040c771180000327c45a34c1032b87700000c72e08613040c77154000031cc45a34c1032a47700000e6f1cc45a340cae1dc000031cb02654c10323c7f00000c72c079d3040c771ac000033fccf114c1032b87700000e42c0861a357d301dc000031cc45a34c11c2b87700000c72c079da34d1031dc000031cb025768d514c07700000c72c064d3040cd01dc000035bcbac09953040c7700000cbac086130494ae1dc000031cb029668d3040c7700000c72c0995a34b1031dc000031cc468b68d032b87700000c9ec08613040cae1fc000031cc4530488ae1dc4500000c72c279da34c1031dc000032eb02214c1032b87700000c72c079da34c1251dc000031cb01e768d3e40c7700000c72c0a3e862b877114000032eb01984c1032b877) else (if i < 608 then 0xcff31b013040cae1dc000031cc45ab4c1032b87700000c72e6861a34c10336c000000000000000000000000000c72c08e93040cae1fc000031cb028864d302b87700000c72c0971a34c1031dc000000000000000000000000000d56e6861a34c1031dc000031cc45a34c0fa2b87700000c72c079d6b4c1031dc000031cb026568d5d4c07700000cbac0995614c1031dc000032eb01ea5dd3040c7700000c72efb01e768d301dc0000327b01e968d3040c7700000c72c0a1a6368d301dc000031cbce83861302b87700000c731168d3040cd01dc000033fc72c0a19e74c07700000cbac09113040cae1dc000031cb02654c1033407f00000cbac08613040cd81dc000032ec72c07a93040c7700000c731168d3040cae1e4000032eb02694c1033407700000d5b3fc72c04c1031dc000031cb02184c1032ec7f00000cbac08613040cea1dc000032eb024e4c1222b877 else 0xc72c0a61a34b1031dc000031cc453040cae1dc6900000cbac09393040cae1dc000000000000000000000000000cbac0a913040cae1dc000031cb02b779d3040c7700000c9ec0861a34c0f52b8000000000000000000000000000c72b78613046cae1dc000032eb01ea68d3040c7700000c72c0995a3551301dc000000000000000000000000000d12c08613040cae1fc000000000000000000000000000c731168d3040cc51dc000031cc45a35193040c7700000cff1cb0286709302b8000000000000000000000000000d131868d3040cae1dc000037dc72c068d3040c7700000000000000000000000000000000000000000000000000c72c079d3040c7f1dc000000000000000000000000000cbac095d3040cae1dc000000000000000000000000000c731179da34c1031dc000032eb02264c1032b877000000000000000000000000000344b02187013040cd800000000000000000000000000031cb0265701303d4ae)) else (if i < 704 then (if i < 672 then 0xc72c08613040c9c1fc000031cb01e76b13040c7700000cbac086130488ae1fc0000355b02657013040c7700000c72c079da34e9031dc000031cb026568d575447700000c731168d30460ae1dc000031cb028e68d032b87700000000000000000000000000031cb028079da34c07700000d56c0995a34c1031dc000032eb82c08613040c7700000c8ac08613040cae1fc0000332b02184c1242b87700000cbac0aa53040cae1dc000000000000000000000000000000000000000000000000031cb01fa4c1031dc4500000c731178d6b4c1031dc000031cb01e668d3040c7700000e071c4c1032b877154000000000000000000000000000000000000000000000000031cc45c268d3040cae00000d131168d3040cae1dc000038bd5b1cb01a34c07700000cbac06113040cae1dc000031cc453040cae1dc4500000cc71c68d614c1031dc000031cb026568d614c07600000c730b4c1032b877154000031cb029a9952c40c77 else 0xdd71c4c1032b87f154000031cb0218545302b87f00000c72c0a19e76d5301dc000032eb01754c1032b87f00000cbb1cc453040cae1dc000031bb82c068d3040c7700000dd31cae93040cae1dc000031cb0265701614c06e00000cff316593040cae1dc000031cb01e768d303d47700000cbac0a19754c0ae1dc000031cb01f768d3040c7700000c72de995a3545301dc0000356c72c05b13040c7700000c73114c103340771140000357cbac09953040c7700000c7311a196b4c0ae1dc000032eb01e74c1031dc4500000d0f1c68d3040cae1dc000032eb02184c1052b87700000c73116a53040cae1dc000031cb01e768d3340c7700000c72d2861a3545301dc000032db02184c1032b87700000c72c06513040cae1dc000032eb01d94c1032b87700000cbaba8613040cae1dc0000381c72c068d514c07700000cfec05d53040c9c1dc000032eb01cf4c1032b87700000c73114c1032b8771ac0000375c7130490ae1dc55) else (if i < 736 then 0x375c72c04c1032b87f1dc00c72c090da34c1032b8770031cb01e768d3040c7707c00c72c0861a54c1032b8770032ec72c086130488ae1dc00c72c0861a351930465030031cb02184c1032b87f0a800c72ebb01e768d3040c770035fc72c068d3040cae1dc0000356c72c07013040c7700000c72de995fb4c1031dc000031cc45a3545302b87700000c72c0a19c4709302b8000032eb02374c1032b87700000cff1cb0265545301dc000031cb02637013040c7700000cbac0a1a184c0ae1dc000031cb028679da34c07700000c72c0861a353cae1dc000031cb0286709b54c0ae00000c72d7995a3585301dc000032eb024e4c1033407700000c2ec068d3040c9c1dc000031cb019b4c1032b87700000cff1cb01e74c1031dc0000356c72c068d3040c7700000000000000000000000000031cb02224c1032b87f00000c72c09a53040cae1fc000031cc45a34c1032707700000c7311be9a340cae1dc000031cb026368d3040c77 else 0x31cc4ac068d3040cae1dc00c72c4861a34c1032b8770031cb02184c1032b87713000c72c0861a34c1032a4770033fc72c095d3040cae1dc00cff1cb01964c1032b8770031cb01e768d3040c7708800c72c094da34c1032b87700375d5b1cb01a34c1031dc00dc73fc72c04c1032b8770031cb01d94c1032b87711400c72c068d814c1032b8770031cb5e1868d3040cd81dc00c72c0925a34c1032b8770031cb02b75d53040cae1dc00c72c079da34c1031dc290031cb361868d3040cae1dc00d331cb01a34c1032b8770031cc45a35ad3040cae1dc00c72c0861a34c1033ac770031cc731168d3040cae1dc00d56c0995a34c1032b8770031cb0286861c268d302b800c72c09fe184c1032b8770033fc72c07413040cae1dc00c72c09a5a34c103340770031cc45a34c1032b8770ec00c73119e1a34c1032b8770031cb026568d3040ccc1dc00c72c0861a34c1112b8770031cb022068d3040cae1dc000031cbcac068d3040c77))) else (if i < 896 then (if i < 832 then (if i < 800 then 0x31cb01a35d5303d4ae1dc00c72c08613040cae1fc7f0031cb021868d3040cad1dc00c72c0861bd4c1032b8770031cbc2c0861a34c0ae1dc00c72c068d7d4c1032b8770031cc45a34c1032b87704c00c72c6861a34c1032b8770031cb026568d3040cc71dc00c72c068d844c1032b8770033fc72c08613040ca81dc00c72c0861a34c103370770031cc6ec068d3040cae1dc00c72c08613040cba1dc450031cb021868d3040ccc1dc00c72c3861a34c1032b8770031cb01a36293040cae1dc00c72c08613040cae1dc540031cb01e7765a34c1031dc00dd71cb01a34c1033a8770033fc72c09393040cae1dc00c72c068d924c1032b8770031cb022668d3040cae1dc00ce71cb01e768d3040c770031cb02186fd3040cae1dc000031cc456b4c1032b8770031cb02186d93040cae1dc00dab1cbbec068d302b8770031cb02184c1032b87f08c00c72c0861a34c1032c0770032eb02928613040cae1dc00c72c09e5a34c1032b877 else 0x375cff33c713040cae1dc00c72c0861f468d3040c770031cb01754c1032b87711400c72c068d884c1032b8770031cb02af9953040cae1dc00c72c0921a3545302b8770031cb026568d3040cd01dc00c72c0a31a34c1032b8770031cb029779da34c1031dc00cff26b02184c1032b8770031caee1868d3040cae1dc00c72c068d754c1222b8770031cb01e768d3040c7718800c72d9b01e768d3040c770031cb01e768d3040c7711400c72c0765c04c1032b87700344b5e1868d3040cae1dc00e0f1cb01a34c1032b8770031cb026568d3040cd81dc00c731168d3040cae23c770031cc468668d754c0ae1dc00d56c0861a34c1032b8770036ac72e0b01a34c1031dc00c72c0931a34c1032b8770031cb01754c1032b8771a400c72c086130414ae1dc450031cb01a35d530420ae1dc00d5f1cc45a34c1032b8770031cc45a34c1032b8770a400dd71cb01a3545302b8770033fc72c08253040cae1dc00cff1cb02184c10327077) else (if i < 864 then 0x31cbb9a35d53040cae1dc00c72c0995a34c11940cae0031cb028668d754c0ae1dc00c72c079da34c1031dc6e0031cb025068d3040cae1dc00c72c079da35d53040c770033fc9ec08613040cae1dc00c72c095da34c10323c770031cb02716f13040cae1dc00e8b3fb01754c1032b8770031cc45a34c1032b87706400c72c09bde768d3040c770031cb02184c1032b87715c00c72e4b021868d3040c770031cb02657ed3040c8f1dc00c72c0861a34c1032b8780031cb0280861a34c0ae1dc00dd71cb25a34c1032b8770031cc46c0709a34c1032b800c72c07d9a34c1032b87700324b021868d3040cae1dc00c72c0981a34c1032b8770031cb020568d3040cae1dc00cff1cb01db4c1032b8770033fc72c09953040c8f1dc00df31cb82c068d3040c770031cc46eb68d3040cae1dc00c72c0995a34c103258770031cb024e4c1222b87711400d5f3fc72c09953040c770031cc45a34c1032b8770e800c72d295da34c1032b877 else 0x339c731168d3040cae1dc00d2f1cb01a34c1032b8770037fc72c068d3040cae1dc00c731168d534c1032b8770031cb029468d3040cae1dc00cbac0939a34c1032b8770031cb028c68d30465032b800c72c0935a34c1032b8770031cb024468d3040cae1dc00c72e0b02184c1031dc450031cb021868d3040cc51dc00c72c0861a34c10334c770031cb02184c1032b87f07c00c72c0861a34c103340770031cb021868d3840cae1dc00c72c079da35853040c770031cb021868d3040cae1dc00c72c08853040cae1dc450031cb021868d3040cb41dc00c72c0861a34c1033607700345c72c09c5a34c1032b800c72f6b021868d30464ae0031cb72184c1032b87711400c72c068d964c10323c770032eb02184c1032b87705000d56c0761a34c1032b8770031cc0ac079da34c1031dc00c72c0861a34c10d2b8770031cb021e68d3040cae1dc00e42c0861a34c1032b87700333c72c079da34c1031dc00c72c077da34c1032b877)) else (if i < 960 then (if i < 928 then 0x31cb021868d3040cbb1dc00dd71cb01a34c1222b8770031cb02654c1032b87f11400dd71c68d3040cae1dc5500381c72c05b13040cae1dc00c72c0861a3575302b8770031cb021868d30454ae1dc00c72c0871a34c1032b87700322b021868d3040cae1dc00c7311b65a34c1032b8770031cb01ac5d53040cae1dc00c731168d5b4c1032b8770031cb01e768d644c1031dc000032eb024e4c1032b877003a4c72c079da34c1031dc00c72c079dc068d3040c770031cb0263861a34c1031dc00cbac08613040cae1dc260031cb027368d3040cae1dc00dd71cb01a34c0f52b8770031cbd2c0861a34c0ae1dc00c72c0a0e184c0f52b8770031cb021868d3040cc41dc00cff2eb02184c1032b8770031cb021868d3040caa1dc00c72c0861a34c0f82b8770031cb01d868d3040cae1dc00c72d768d754c1032b8770031cb02655b13040cae1dc00c731168d3040cae1dc620031cb024068d3040cae1dc00dab1cb5ac068d3040cae else 0x31cb02184c1032cc7711400c72c0861a34c1032c8770031cc466f68d3040cae1dc00c72c08613040cd21dc550031cc45a35913040cae1dc00c72c0995a34c1032b87c0031cb02374c1032b87711400c72c0861a34bd032b8770031cb021868d30490ae1dc00c72c0861b14c103330770032eb02184c1222b87711400c72c068d754c11b2b8770031cb022d68d3040cae1dc00c72c0a61a35193040c770031cb0265709a34c1032b8000031cb028679da34c0770031cc45a34c1032b87707c00c72c0861a34c1022b8770033fc72fab021840cae1dc00cff1cb023f4c1032b87700000d5b1cb01a34c1031dc00c72c08c1a34c1032b8770031cb02186cd3040cae1dc00c72c0779a34c1032b8770031cc45b568d3040cae1dc00c72c068d754c0fa2b8770031cb027e8613040cae1dc00c72c08893040cae1dc4500000e332eb02184c1031dc00c731168d3040cae1dc450031cb025768d30494ae1dc00c72c0861724c1032b877) else (if i < 992 then 0x31cb020a68d3040cae1dc000031cc453040cae1dc450031cb021868d3040cc01dc00c72c068d854c1032b87700321b021868d3040cae1dc00c72c0995a34c103358770031cb026568d3040ccb1dc00c72ce861a34c1032b8770039ec72c0861a340cae1dc00c72c08613040cae1dc4f0031cc45a35853040cae1dc00cff1cb02184c1252b87700345c72c0861a34c0f52b800cbb1cb02654c1032b87700345c731168d3040cae1dc00c72c0861a34c1222b87f00381c72c068d3040cae1dc00ddb1cb01a34c1032b8770031cb021868d30400ae1dc00d12c0995a34c1032b8770031cc470268d3040cae1dc00c72c09961868d514c07700333c731168d3040cae1dc00cff1cb02184f9032b8770031cb02184c1032b87711800c72c068d755193040c770031cb021868d3040ce81dc00c72c0995e268d3040c770031cc45a34c1032b8771b800c72c05d53040cd01dc450031cb024e4c1032b87f1dc00c72c08613040c9f1dc45 else 0x31cb02184c1032b87712800c72c0995a34c1032b8770033fc72c08613040cea1dc00c72c0a19e768d302b8770031cb026568d3040c911dc00e931cc45a34c1032b877003a2c72c079da34c1031dc00c7311701a34c1032b8770032eb02184c1032b8770a800c72c0845a34c1032b8770031cb01e7709a35d53040c00cff1cb02655853040c7700389bba1868d3040cae1dc00c72c06a5754c1032b8770031cb02a94c1032b87711400c72c0a81a34c0f52b8770031cb021868d503d4ae1dc000031cc468668d302b8770033fc72c07253040cae1dc000031cc45e768d3040c7700375c72c0a19a34c0ae1dc00c9ec08fda34c1032b87700000c72c086130488ae1fc00c72c0995a34c103250770031cc45a35d53040cae1dc00c72c068d894c1032b87700375c72ee68d3040cae1dc00c72c0a19e768d3040c770031cb01e768d3040c7700c00c72c0995a34c1032fc770031cb02534c1032b87715800e2f1cc2ec068d302b877))))) else (if i < 1536 then (if i < 1280 then (if i < 1152 then (if i < 1088 then (if i < 1056 then 0x31cb021868d3040cbf1dc00e8b0bb01a34c1032b87700356c72c068d3040cae1dc00cff1cb0218545302b8770031cb021868d303d4ae0e800c72c0861a34c103338770031cb02b279da34c1031dc00c72cb861a34c1032b8770031cb0da35d53040cae1dc00c72c0765a34c1032b8770031cb021868d303f8ae1dc00c72c09953040cae1dc560031cb027c68d3040cae1dc00c72c0861fb545302b8770031cb029168d3040cae1dc00c72c0861a34fd033307700327b01a35e93040cae1dc00c72c08ddc04c1032b8770031cb01cb68d3040cae1dc00c72f9b026568d3040c770031cb021868d3040cb81dc00c72c068d754c1032a4770031cb021868d3043cae1dc00c72c0861a34c1032d8770031cb028fa1a1868cae1dc00c72c079da354d3040c770031cb02a179da34c1031dc00cff1cb02374c1032b8770031cb020768d3040cae1dc00c72c0861a3545301dc5c0031cb025768d614c1031dc00c72c0861a34c1032f077 else 0x381c72c04c1032b87715800dab3fc72c04c1032b8770031cb021868d30418ae1dc00c72d2861a34c10323c770031cbbec0995a34c0ae1dc00c72c068d754c103330770031cb021868d3047cae1dc00c72c068d784c1032b8770031cb023168d3040cae1dc00d271cb01a34c1032b8770031cb02184c1032b87715800c72c08613040cae1dc6a0031cb0286709a35d5302b800d56c068d754c1032b8770031cb021868d4340cae1dc00c72c0861a34c1032e8770031cb020668d3040cae1dc00e771cb02184c1032b87f0031cb022a6a53040cae1dc00dc71cb02b74c1032b8770031cb01e768d3040cee1dc00c72c08b1a34c1032b8770033fc72c07393040cae1dc00c72c0751a34c1032b8770031cb01a3659614c1031dc00c72c0861a34c1232b8770033bc731168d3040cae1dc00dd71cb01a34c11b2b87700344b021868d3040cd81dc00c72d2861a34c1252b8770033fc72c09c53040cae1dc00c72c0861a34c10328877) else (if i < 1120 then 0x33fc72c080d3040cae1dc00c72c08e5a34c1032b8770031cc45c268d754c1032b800c72c0861a34c10a2b87700372c72c068d3040cae1dc00c72c068d754c1032b8770031cb028068d754c0ae1dc00d471cb01a34c1032b8770031cb01a36313040cae1dc00c72dd861a34c1032b8770032eb02184c1032b87f1dc00c72c095d3040cae1dc450031cb026568d3040c951dc00c72c0995a34c1162b8770031cb020368d3040c9c1dc00cff1cb017e4c1032b8770031cc45a34c1032b87700c00c72c0861a34c1042b8770031cb02184c1033407715800c72c0a266568d302b8770031cc468668d3040cae1dc00c72c0861a34c103294770031cb01a35d530494ae1dc00c72c0861a34c0fd2b8770031cb026568d514c08f1dc00c72c08613040cae1fc6f00344b021868d3040cae1dc00c72c079da355d3040c770031cb021868d484c1031dc00c72c0949a34c1032b877003acc72c068d3040cae1dc00cff1cb02284c1032b877 else 0xc72c08613040cae204770000000000000000000000000c72c068d754c1032d0770031cb4a1868d614c1031dc00c72e0b026568d3040c770000000000000000000000000000000000000000000000031cb01a35f13040cae1dc00e4f1cb021868d302b8770031cb024e4c1032b87711400c72c068d754c103360770031cb02186ed3040cae1dc00deb1cb01a34c1032b8770031cb01a35d53040cd01dc00db31cb01a34c1032b87700381ccf1c68d3040cae1dc00cff1cb8ec08613040c770031cb021868d303f0ae1dc00c7311a85a34c1032b8770031cb01e768da34c1031dc00c72c099da34c1032b8770031cb9ec079da34c1031dc00dd71cb01a34c1033ac770031cb021868d30414ae1dc00c72c0745a34c1032b8770031cb029868d3040cae1dc00c72c0861a35193040c77003a2c731168d3040cae1dc00c72c079da34c11d40c770031cb02655bd3040cae1dc00c72c0a71a34c1032b877)) else (if i < 1216 then (if i < 1184 then 0x31cb01ca68d3040cae1dc00c72c068d754c11940cae0031cb01c868d3040cae1dc00e2f1cb021868d302b8770031cb021868d3040cdc1d800c7311ac9a34c1032b8770031cb023368d3040cae1dc00000000000000000000000000000000000000000000000c72c08613040cae1fc350000000000000000000000000c72c08a9a34c1032b8770031cb01e768d3040c770bc00c72bc861a34c1032b8770032eb02184c1032b87707c00c731168d3040cee2b8770031cb02094c1032b87711400c72c079da35653040c7700375c72c068d3040ccc1dc00c72c0861a34c1162b8770031cb021468d3040cae1dc00da31cb026568d3040c770033fc72c086130488ae1dc00c72c0939a34c1222b8770031cb02184c1032707711400c72c09393040cd01dc450033fc72c0861303d4ae1dc000031cb01e768d3040c770031cb01e768d304c1031dc00c72c068d754c103314770031cb02a768d3040cae1dc00e8b1cb02184c1032b87f else 0x33fc72c0a1a184c0ae1dc00000000000000000000000033cc72c08613040cae1dc00c9ec08613040cae1dc450000000000000000000000000c72c095dc04c1032b8770031cc45a34c11d40cae1dc00c72ba861a34c1032b87700355b024868d3040cae1dc00cff1cb021879d3040c770031cc45a355d3040cae1dc00c72c09953040c8f1dc450032eb02654c1032b87711400cff1cbba184c1032b8770031cb02184c1032b87712000c72c0861c055d303d4ae0031cc46e768d3040cae1dc00c72e0b021868d3040c770000000000000000000000000d3f1cb01a34c1032b87700357c72c09953040c7711400000000000000000000000031cb020e68d3040cae1dc00cff1cb01eb4c1032b8770031cb022768d3040cae1dc000000000000000000000000381c72c05bd3040cae1dc00c72c08616f4c1032b8770000000000000000000000000c8ec0861a34c1032b8770031cb022168d3040cae1dc0000000000000000000000) else (if i < 1248 then 0x31cb02184c11d40cae1fc00c72c0921a34c1032b8770000000000000000000000000c72c0989a34c1032b8770031cb02656f13040cae1dc00cff1cc4ac04c1032b8770031cb0218701a34c0f52b800c72c0861a34c103368770031cb01754c1032b87f11400c72c0975a34c1032b8770031cb01754c1032b8771180000331c71a34c1032b87700000c72ba8613040cae1dc00c72c0939c04c1032b87700379c72de68d3040cae1dc00c72d6b026568d3040cae0031cb025768d4540cae1dc00c72c09953040cae1dc550000000000000000000000000c72c0999a34c1032b8770031cb02185693040cae1fc00c72c0995a34c1032b87f0031cb9a1868d3040c9c1dc00dab1cbeac068d032b8770031cb021868d3040caf1dc00c72c0a0e184c1032b8770031cb025868d3040cae1dc00c72c068d754c1032b8790031cb02244c1032b87711400c72c0995a3585534c0770031cb021868d3040cc11dc00daf1cb01a34c1032b877 else 0x31cb02184c1032b87714400c72c08619e4c1032b8770000000000000000000000000c72c08613040cae1dc550031cb01e768d3040c7702800c72c08613040cae1fc080031cb021868d3040cb31dc00000000000000000000000000000000000000000000000c72c0861a34c10327c770000000000000000000000000c72c083da34c1032b87700000c731168d3040cae1dc00c72c068d774c1032b8770031cb02187013040c9c1dc00c72c08dda34c1032b8770031cc45a35653040cae1dc00cbac0861a34c1222b8770031cc45a34c13040cae1dc00cc71c68d964c1032b8770000000000000000000000000c72c0861a34c103344770031cb020c68d3040cae1dc00000000000000000000000031cb02097013040cae1dc00dd71cb01a34c1033607700000000000000000000000000000000000000000000000000c72c09953040cae1fc00cff1cb5e184c1032b8770000000000000000000000000c72c0889a34c1032b877))) else (if i < 1408 then (if i < 1344 then (if i < 1312 then 0x31cb02185653040cae1fc00cff1cc46184c1032b8770033fc7311b013040cae1dc00cbb1cb01754c1032b8770031cb02184c1032b87713400de31cb01a34c1032b8770031cb02184c13040cae1fc00c72c0861a34c1033407f0031cb028fa19a35d4ae1dc00c72c08a5a34c1032b8770031cc45a368d3040cae1dc00000000000000000000000031cb02656e53040cae1dc00000000000000000000000031cb02184c1032b8771b000cff1cb02184c11b2b8770033fb01a36593040cae1dc00c72c0995c04c10323c770033fc730fb013040cae1dc00d5f1cb02657013040c770031cb02186f13040cd81dc00c72c0995a3585301dc6e0031cb025168d3040cae1dc00c72de995a34c10323c770031cb01c268d754c1032b8000032eb02184c1222b8770031cb01a35d53040cae1f000cff1cb02185193040c770031cb01e768d3040c7706000c72c0955a34c1032b8770031cb021868d3040cae1fc00cff1cc2ec04c1032b877 else 0x31cb023f4c1032b87711400c72c09d9a34c1032b8770033fc72c06693040cae1dc00c72cf861a34c1032b8770031cb026768d3040cbf1dc00000000000000000000000000000000000000000000000000000000000000000000031cafe1868d3040cae1dc00c72c086130494ae1dc450037bc72c079da34c1031dc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c72c08ada34c1032b8770031cb01a35fd3040cae1dc00c72c068d754c1032fc770031cb02a968d3040cae1dc00d12c068d754c1032b87700345c72c0861a34c103360000033fb01964c1032b8770031cb021868d4540c9c1dc00dab37c72c04c1032b87700000c72c0a19c268d302b800c72c095db74c1032b87700000c72c079dc268d3040c00c72c09a1a34c1033307700375c72c06cd3040cae1dc00c72c074da34c1032b877) else (if i < 1376 then 0x31cb02184c1242b87715400c72c075da34c1032b8770000000000000000000000000c72c0805e768d3040c770031cb029f68d3040cae1dc00c72c079da34c1031dc340031cb02656ad3040cae1dc00c72c086130488ae1fc770031cb02655853040c771140000358c72c079da34c0770031cc45a34c1032b87706000000000000000000000000031cb02186f93040cae1dc00c72c079da34c10337c770031cb01c94c1032b87711400dd73fccda34c1032b8770000000000000000000000000c9ec0861a34c11b2b877002d1b01a35d53040cae1dc00c72c068d754c1062b8770031cb01fe79da34c1031dc00000000000000000000000031cb02656bd3040cae1dc00c72c0861a34c0fb2b87700355b0265861a34c1031dc00000000000000000000000000000000000000000000000c72c05d53040cae1dc560031cb021868d5040cd81dc00000000000000000000000031cb024e8613040cae1fc0000000000000000000000 else 0x33fc72c09953040cae1dc00c72c0861514c0ae1dc450033fc72c08613040ccc1dc00000000000000000000000031cb023f7013040cae1dc00000000000000000000000031cb021868d3040cb51dc00dcf1cb01a34c1032b8770031cb021868d3044cae1dc00c72c0951a34c1032b8770000000000000000000000000c72c0861a34f5032b8770033fc72c08993040cae1dc00c72c092da34c1032b8770000000000000000000000000c72c0861a340cee2707700369c72c068d3040cae1dc00c72c0861a34c1072b8770031cb02184c1033a8771140000375cff334c1032b8770031cb021b68d3040cae1dc00c72c0995a34c10335c8f0031cb021868cf52b88f1dc00c72c09ba094c1032b87700355c72c0995a34c1031dc00c72c068d754c1042b8770033fccec05f93040cae1dc00000000000000000000000031cc45a34c1032b87702800c72c09a1a34c1032b8770031cb01a360d3040cae1dc00c72c0995a34c10324077)) else (if i < 1472 then (if i < 1440 then 0x33fc72c08153040cae1dc00e8b2eb02184c1032b8770031cb8ec0ade184c1031dc00d56c0861a34c103270770036ac72c04c1032b87711400def1cc45a34c1032b8770031cb01a35d530458ae1dc00c72c0861ab4c1032b8770031cb021868d3240cae1dc00c72c09dda34c1032b8770031cb021868d3040ca01dc00dc71cb01a34c1032b8770000000000000000000000000000000000000000000000031cb021868d5740c9c1dc00d573fb02184c1032b8770031cb025768d3040cae1dc00c72c0995a340cee23c770031cb021870130494ae1dc00c72c0995a34c103270770031cb027568d3040cae1dc00c72c0861a3501032b87700000c7311709a34c1032b800c72c09c53040cae1dc450031cbbec068d754c0ae1dc00dd744b01a34c1032b8770031cb01d068d3040cae1dc00c72c08613040cae1fc180033fc72c06113040cae1dc00c72c0a19c268d3040cae0031cb02186993040cae1dc00c72c07393040cae1dc45 else 0x31cb01a35d93040cae1dc0000358c731168d302b87700327b026568d3040cae1dc00c72c0861a34c103274770031cb0218781a34c1031dc00de71cb01a34c1032b8770031cb09a35d53040cae1dc00c72c079da34c1031dc370031cb021868d3040ca81dc00c72c05f93040cae1dc450031cb029a8613040cae1dc00c72c0861a34c10328c770031cb02654c1222b87711400c72c0861a34c1032787700000c72ebb013040cae1fc00c72c0861a34c1122b8770031cb023d68d3040cae1dc00c7319b01a34c1032b8770000000000000000000000000c72c0939a34c1032b8770031cb026568d5740c8f1dc00c72c071da34c1032b8770000000000000000000000000000000000000000000000000000000000000000000000c72c0861a3515252b87700344b02186f13040cae1dc00000000000000000000000031cb021f68d3040cae1dc00000000000000000000000031cb02a1709a34c1032b80000000000000000000000) else (if i < 1504 then 0x31cb0286739a34c0ae1dc00cfec0861974c1032b8770031cb0218701514c0ae1dc00c72c09ada34c1032b8770031cb01cc68d3040cae1dc00c72c0981a34c103270770031cb021868d303dcae1dc00c72efb82c0861a34c0770031cb01e768d3040c771dc00cff1cb02184c103360770033fca2c08613040cae1dc00d631cb01e768d3040c770031cc46c05ad3040cae1dc00d16c068d964c1032b8770031cb01a35d53040caf1dc00c731168d3040cdf2b8770031cb026568d3040cc21dc00c72d2995a34c1032b8770033fc72c0a19754c0ae1dc00cff1cb02184c1033407700377c72c068d3040cae1dc00c72c0861a34a9032b8770031cb82c068d754c1031dc00d5b1cc2ec068d3040c770031cb024e68d3040cd01dc00c731168d3040cae1dc3400320b021868d3040cae1dc00e073fc72c04c1032b8770031cb020968d3040cae1dc00c72c0861c04c1033a8770031cb021868d3040c9c1dc00c9ec0861a34c10333077 else 0x32eb02184c11d40cae1dc00c72c06f1754c1032b8770031cbce1868d303d4ae1dc00dd71cb31a34c1032b8770031cb02184c1222b8771a400c72ee9f6184c1032b8770031cb0265701614c1031dc00c72c0861a34c10326c770033fc72c086130465032b800cbac08613040cae1dc080031cb021d68d3040cae1dc00dab1cb01c04c1032b8770031cb01db68d3040cae1dc00cbac05d53040cae1dc450031cb02524c1032b87715400c72c09953040cae1dc5b0031cb02184c1222b87711400c72e2b021868d3040c7700000d631cb02184c0ae1fc00c72c08613040cdf2b87f0031cb023868d3040cae1dc00c72de861a3545302b8770031cb026568d3040c8f1dc00c72d79c5a34c1032b8770031cb02717013040cae1dc00c72c0abe094c1032b8770031cb01e768d3040c7708400c72c0861303d4ae1dc450033fc72c09113040cae1dc00cff1cb028c4c1032b87700357c72c0995a34c1031dc00cff1cb01e75d53040c77)))) else (if i < 1792 then (if i < 1664 then (if i < 1600 then (if i < 1568 then 0x31cb0286861302b87711400cbac0861a34c1032b8770031cc45a34c1032b8770dc00c72c068d754c1032b87f0031cb02656c13040cae1dc00c72ee8613040cae1dc450031cb01c05f93040cae1dc00c72c0995a34c12c40c770038bdd71cb01a34c0ae1dc00dd71cb013040cae1dc560031cb023f68d3046cae1dc00c72c08fda34c103330770031cb02187013040cd21dc00c72fab026568d032b8770031cb021868d5d4c09c1dc00e4b1cb01e768d3040c770031cb9ec0861a3545301dc00c72c0861a35854540c7700327b021868d3040cae1dc00dd745ccda34c1032b8770031cb01754c1032b87715400c72c09e9a34c103360770031cb02186dd30494ae1dc00c72c0861a34c1033b07700338c72c08613040cae1dc00c72c088da34c1032b87700000c72c0995a3545301dc000032eb02654c1032b8770031cb022468d3040cae1dc00c72c068d744c1032b8770031cb02184c1223407711400c72c068d904c1032b877 else 0x31cb027a68d3040cae1dc00c72c0a3de768d3040c770031cb026368d3040cae1dc00c72c0861a04c1032b87700355b026568d3040c8f1dc00cff1cb02184c1032b87700381c72c068d3040c8f1dc00c72c0861a3519301dc6e0031cb026568d30494ae1dc00c72c08bda34c1032b8770032eb02184c13040cae1dc00c72c0995a34c1032847700375c72e0b01a34c1031dc00cbac0861a34c103340770031cb026568d3e40cae1dc00cff1cc45754c1032b8770031cb024268d3040cae1dc00c72c0a8da34c1032b87700000c72c05d53040cae1fc00c72feb01e768d3040c770031cb021850d032b87715400c72c0a1a186d5302b8770031cb024e4c1032b87f11400c72c08dda34c1162b8770031cb02186893040cae1dc00c72c09396c4c1032b8770031cb021968d3040cae1dc00d631cc45a34c1032b8770031cb024168d3040cae1dc000031cb026568d2c40c770031eb02184c1032b87711400c72c08613040cae1dc4b) else (if i < 1632 then 0x31cb5e1868d614c0ae1dc00c72c0861a34c1032c4770031cb01a36353040cae1dc00c72c0861a35793040c770031cc45a35f93040cae1dc00c72c08619f4c1032b8770031cb021870130488ae1dc00c731168d3040cae1dc77002d0b01a35d53040cae1dc00c72c0861a34c1032e4770031cb0292a19a34c0ae1dc00c72c0a49e768d3040c770031cb020d68d3040cae1dc00c7ec0861a34c1032b8770031cbeac0861a340cae1dc00c731168d3040cae1dc210033fc72c06153040cae1dc000031cb028fa19a32b8770031cb02184c1032b87f0dc00c72c08fda34c1032b8770031cb028fa19a34c0ae1dc00d631cb02184c1032b87f0031cb01cd68d3040cae1dc00e0757c72c068d3040c770031cb02187f13040c9c1dc00c72c084da34c1032b8770031cb025b68d3040cae1dc00c72c079da34c1031dc420031cafda35d53040cae1dc00c72c068d804c1032b8770032eb026568d3040cae1dc00cbac0861594c1032b877 else 0x31cb0286861c04c0ae1dc00c72f6b026568d614c0770031cb024f68d3040cae1dc00c72c09a53040cd01dc4500356c72c0861a34c1031dc00c72c0929a34c1032b8770031cb0286709a34c0ae1dc00c76c0861a34c1032b8770031cb01dd68d3040cae1dc00d133fb02184c1032b8770031cb01e7709a34c1031dc00c72c0861a3525032b8770031cb02654c1032b87f1dc00e731cbb9a34c1032b8770031cb01e768d3040c7702c00c72c08613040cae1fc770031cb01a35e93040cae1dc00d371cb01a34c1032b8770032ec72c09393040cae1dc00c72c0995a35453040c770031cb021868d30494ae1dc00c72c0861a34c11e2b8770031cc02c079da34c1031dc00cff1cbd2c0861302b8770031cb02694c1032b87711400c72c0a1a1879da34c0770031cb82d6b021868d3040c00c72c0861303fcae1dc450031cb026568d3040cea1dc000031c68d5b4c1032b8770033fc72c08613040cae1f000c72c0809a34c1032b877)) else (if i < 1728 then (if i < 1696 then 0x31cb01c168d3040cae1dc00c72c0725a34c1032b8770031cb029b79da34c1031dc00c72ee861c04c1032b8770031cb01a35d53440cae1dc00c72bd861a34c1032b8770031cb028d68d3040cae1dc00d56c0861a3545302b8770031cb01dc68d3040cae1dc00c72c068d754c1032d4770031cb02184c1032b87711c00c72c0ac6184c1032b8770031cb022868d3040cbf1dc00c72c0995a35853040c770031cb021868d3a40cae1dc00c72c0861a34cd032b8770033fc72c07653040cae1dc00cfec05d53040cae1dc5c0031cc46fe68d3040cae1dc00c72c0861a355d3040ccc0033fccec06113040cae1dc00cff1cb02187093040cae0031cb02364c1032b87711400cff1cb02184c1032fc7700392c731168d3040cae1dc00e8b1cb021868cf52b8770031cb02184c11b2b87711400c72c0861a357d303d4770031cb026568d514c0ae1dc00c72c08613040cd01fc770031cb01a35d53041cae1dc00c72c0841a34c1032b877 else 0x31cb01e068d754c1031dc00c7311b028668d302b8770031cc469268d3040cae1dc00c72c09c5a34c1032b8770031cb01ce68d3040cae1dc00c72c0995714c1032b8770031cb02b76113040cae1dc00c72c0861a3545302b8770031cb01a35e53040cae1dc00dbf1cb01a34c1032b8770031cb02b79953040cae1dc00c72c08613040cae1fc5500000b01e768d594c1031dc00c72c079da34c1031dc580000000000000000000000000000000000000000000000000000000000000000000000cff33b02654c1032b8770031cb026568d3040c921dc00c72c0861a355d512b8770031cb01fd79da34c1031dc000031cb026368d3040c770031cc45a34c1032b87710800c72c0861c04c0f52b8770031cb01934c1032b87711400c7311a3da34c1032b8770031cb021868d3040cea1dc00c72c0861a34c1092b8770031cb01ab5d53040cae1dc00cbac08613040cae1dc180031cbba1868d464c1031dc00c72c0a3e8668d032b877) else (if i < 1760 then 0xc72c0861a14c1032b8770000000000000000000000000c7311709a34c1032b8770000000000000000000000000c731168d3040cae1dc0b0031cb027168d3040cd81dc00c72c08993040cae1dc450033fc72c079da34c1031dc000000000000000000000000381c72c068d614c1031dc00cff1cb029c4c1032b8770031caca184c1032b87715400c72c0861a34c103378770031cb01a35d53040c9c1dc00dab1cb01a34c1032b8770031cb021868d3040cbe1dc00c72c079da358d3040c7700000cbaebb013040cae1dc00c7311c01a34c1032b8770031cb5e1868d303b8ae1dc00c7311a1a1868d302b8770000000000000000000000000cff1cb01754c1032b8770031cb02a1a3da340cae1dc00e8b1cbba1868d032b877003b2c72c0995a34c1031dc00c7311b01e768d3040c770032eb02184c1032b8770e000c72c085da34c1032b8770031cb061868d3040cae1dc00cff33b02184c1032b877 else 0xcff1cb01e74c1031dc00c72c098dce68d3040c770031cb027468d3040cae1dc00dbb1cb01a34c1032b8770031cb017e5b53040cae1dc00000000000000000000000031cc36c068d3040cae1dc00000000000000000000000031cb01a35f93040cae1dc00c72c08613040cae1dc490031cb01a35cd3040cae1dc00cff1cb01914c1032b8770031cb026568d30488ae1dc00c72c0861a34c103320770000000000000000000000000000000000000000000000031cb02928613040cae1fc00df31cb01a34c1032b8770031cb021868d3040cc31dc00000000000000000000000031cb026568d303d4ae1dc00c72c06113040cae1dc450031cb02654c1032b8771a400c72c080da34c1032b8770031cb021868d30404ae1dc00c72c08613040ccc1dc450031cc45755ad3040cae1dc00d7f1cb01e768d3040c770031cb021868d3040cd41dc00c72c0895a34c1032b8770033fc72efb02184c0ae1dc00c72c0861a34c1032b077))) else (if i < 1920 then (if i < 1856 then (if i < 1824 then 0x31cb021868d303d4ae1dc00cff1cb82c08613040c770031cb026568d3040c931dc00c72c0861ae4c1032b87700000c45a35653040cae1dc000000000000000000000000375c72c06ad3040cae1dc00eab3fb02184c1032b87700344b01a36353040cae1dc00e3b1cc45a34c1032b8770000000000000000000000000c72c7861a34c1032b8770031cb2a184c1032b87711400000000000000000000000031cc45a34c1032b87716000c72c0861a34c103328770031cb028c4c1032b87711400c7311a6da34c1032b8770031cb02654c1032b87711400c72c068d754c5032b87700000d632eb02184c0ae1dc00cff1cb022a4c1032b8770000000000000000000000000c72c079da34c103374770033fc72c086130458ae1dc00c72e3b021868d3040c7700327b01a35d53040cae1dc00c72c09953040cd01dc450032eb02184c10337cae1dc00c72c0a327d4c1032b8770031cb021868d3040cd21dc00c72c05d530488ae1dc45 else 0x390b021868d303d4ae1dc00c72c5861a34c1032b8770031cb021868d30488d01dc00dd71cb01a34c103270770031cbce1868d3040cae1dc00c72c08613040cd81dc450031cc45a358d3040cae1dc00c72c0a19b55d5302b87700370c72c068d3040cae1dc00c72ee995a34c1032b8770000000000000000000000000c72f4b02b7861302b87700375cff1cb013040cae1dc00cbac068d754c1032b8770031cb026579da34c1031dc00c7311c2da34c1032b8770031cb01e768d3040c7717000c72c079da34c10320c770031cb02865d5302b87711400c72c068d874c1032b87700394cbac08613040cae1dc00cff1caea184c1032b8770031cbdec0861a34c0ae1dc00e071cb013040cae1dc450031cb021868d30488ae1dc00c72c0861ad4c1032b8770031cc45fd68d3040cae1dc00c7311c45a34c1032b8770031cb020b68d3040cae1dc00c72c0861a34c1082b8770031cb021868d3040ca61dc00c72c0a1a6568d302b877) else (if i < 1888 then 0xb02185653040cae1fc00c72c0995a3515032b8770031cb021868d30464f52b800e4b1cb026368d3040c7700000cff1cc453040cae1dc00c72e6861a34c1032b8770031cbeac068d7540cae1dc00c72c08613040cae1fc140031cb021868d3740cae1dc00c72c0b01e768d3040c770031cb021668d3040cae1dc00c72c079da34c1031dc2a0031cbba1868d3040cae1dc00d7f1cc45a34c1032b8770031cb02657013040cae1dc00cff1cb02484c1032b8770031cbc6c0861a34c0ae1dc00c72c0861b24c1032b8770031cb5e6568d3040cae1dc00c72c09113040cae1dc450031cb01e768d3040c891dc00c72c0abe0b4c1032b8770031cb026168d3040cae1dc00cbac09393040cae1dc450031cb02267013040cae1dc00c72c0861c04c103330770031cb025e68d3040cae1dc00c72c07ada34c1032b8770033fc731168d3040cae1dc00c72c0965a34c1032b8770031cbba8c68d3040cae1dc00c72c0919a34c1032b877 else 0x31cbeaefb021868cae1dc00c72c068d8e4c1032b8770031cb01754c1032b87f1dc00c72c0a1a7868d302b8770031cade184c1032b8770e800c72c09e1e768d3040c770039cc72c068d3040cae1dc00c72c0995a34c11b2b8770031eb021868d3040cae1dc00db71cb01a34c1032b8770031cb021868d303e4ae1dc00d12c09c5a34c1032b87700331c726568d3040cae1dc00d56e7b021868d3040c7700375c9ec068d3040cae1dc00cff1cb02184c1032b87f0031cb026568d2d40cae1dc00c8ac08613040cae1dc450031cc45a34c103374ae1dc00cff1cb01c25d53040cae00000e331cc45a34c1031dc00c72c0a31c04c1032b87700375c72c04c1222b87711400c72c0861a34c1032ac770031cb028679da35d5301dc00c72c05d53040cae1dc6b0031cb023b68d3040cae1dc00c6ec0995a34c1032b8770031cb024e68d3040cae1fc00c72c0995ac4c1032b8770031cb021268d3040cae1dc00c72c0855a34c1032b877)) else (if i < 1984 then (if i < 1952 then 0x31cafa1868d3040cae1dc000038cc72c08613040c7f0031cb86c0861a34c1031dc00c72c0861aa4c1032b8770031cc45a34c1032b8891dc00c731168d3040cae1dc5c0031cb02187013040cd81dc00cff1cb02a94c1032b8770031cb020868d3040cae1dc00c72c0861b84c1032b8770031cb02186b13040cae1dc00d171cb01e768d3040c770031cb028c68d464c1031dc00c72c0995a35193040c770031cb02184c1032c87711400c72c0861a34c11b330770032eb02184c1032b8770dc00c72c0a19c05d5302b8770031cb521868d3040cae1dc00cbac08613040cae1dc770031cb01a35d53a40cae1dc00c731168d3040cae20c7700383c72d768d3040cae1dc00e8b57b026568d3040c770031cb024568d3040cae1dc0000355b026568d3040c770031cb01a36653040cae1dc00c72f6b021868d464c0770031cb024768d3040cae1dc00c72c0a1a1868d302b8770038cc72c079da34c1031dc00c72c05d56b4c1032b877 else 0x33fb02656593040cae1dc00e4b1cb026568d614c0770031cc46c068d3040cae1dc00c72de995a34c1032b8770031cb021868d30438ae1dc00c731168d3040cae1dc2a0031cb02656a53040cae1dc00d6f2eb02184c1032b8770031cb021868d3046cae1dc000031cb024e4c1032b87f0031cbba1868d30465032b800c72c08613040cbb1dc450031cbeae0b021868d031dc00c730fb01a34c1032b8770031cb01a45d53040cae1dc00c72c068d754f9032b8770031cc72c079da34c1031dc00c72c09a5a34c1032b8770031cb023668d3040cae1dc00e8b1cb028c68d032b8770031cb01a35d53040cea1dc00e071bb01a34c1032b87700331c72c068d3040cae1dc00c7311995a34c1032b87700331c721868d3040cae1dc00d12c0861a3585302b8770031cb023468d3040cae1dc00c72c0749a34c1032b8770031cb02184c1222b87f11400c72c0861a34c0ff2b8770031cb021868d303e8ae1dc00c72c068d864c1032b877) else (if i < 2016 then 0x38cc731168d3040cae1dc000031cb01934c1032b8770031cb6e1868d3040cae1dc00c72c068d9a4c1032b87700357c72c079da34c1031dc00c72c0861a34c10b2b8770031cc21a35d53040cae1dc00c72c068d754cd032b87700344b02184c1032b87711400cbac0861a34c1032b87f0031cb021868d474c1031dc00c72c0861a3551302b87700346c731168d3040cae1dc00c72c079da34c10323c770031cb026d68d3040cae1dc00c731179da35d53040c770031cbba184c1032b87716800cff33b01754c1032b87700000c730fb013040cae1dc00c730bb01a34c1032b8770031cb01a364d3040cae1dc00c72c0861a3581302b8770031cb021a68d3040cae1dc00c72c0861a357d3040c770031cb01e768d3040c7704c00c72c08f1a34c1032b8770031cb01a36093040cae1dc00e071cb01c04c1032b87700340c9ec08613040cae1dc00c72c068d75545302b8770032eb01a35dd3040cae1dc00c72c097da34c1032b877 else 0x31cb0299861a34c1032b877000000000000000000000000000000000000000000000c72c0861a34c1032b8771140000000000000000000000c72c09e1a35d53040cae1df1cb02184c1032b87711418c72d9b026568d3040cae1df1cb02c068d754c1032b877c72c0861a34c1032b8770af1cbe2c0861a34c1032b877e4b1cb02a1861a34c0ae1dc0000000000000000000000dd71cb01a34c11d40cae1dc00c72c0739a34c1032b877c72c0861a34c1032b87717f1cc06c0861a34c1032b877c72c0995a34c1033b8ae1df1cb021868d584c1032b877c72c08d61868d3040cae1df1cb021868d3040cae1dc04c72c09b21868d3040cae1df58c72c068d754c1032b877c72c0861d668d3040cae1df1cb021868d3040cf42b877cff1cb01a35d53040cae1dc00c72c0861a34c1032907700375c72c068d30494ae1dc00c72c079da34c1031dc3a00345c72ba8613040cae1dc00c72c0861c04c1242b877)))))) else (if i < 3072 then (if i < 2560 then (if i < 2304 then (if i < 2176 then (if i < 2112 then (if i < 2080 then 0xc72c068d754c11d40cae1df1cb026568d3040cae1dc2ae8b1cb020368d3040cae1df1cb024e68d3040cae1dc45c72f6b026568d3040cae1df1cb01a35d53040cae1dc1fc72c068d754c1032b8771639ac72c0861a34c1032b8770038ccff1cb02184c1031dfa2cff1cb02184c1032b8770038cc72ebb01a34c1031df1cb9ec0861a35853040c77c72c0861a34c1032b8770c400b02185653040cae1dc45c72e7b01a35d53040cae1df1cb021868d3040cae1dc74c72c0861c04c1032b8770631cb027168d3040cae1dc6e0000000000000000000000399c72c0861a34c1032b877c72c0a126568d3040cae1dc00c72c0899a34c1032b877000000000000000000000031cb02b3861a34c1032b877c72c0861a34f93040cae1df8cc72c068d754c1032b8770031caaa0968d3040cae1df1cb021868d3040ccc2b877ebf1cb021868d3040cae1dc0000000000000000000000c7307b021868d3040cae1df1cb021868d3040cae1dc61 else 0x31cb82c0aca1868d3040c7700358c72c0861c04c0ae1df1cb021868d844c1032b877d971cb021868d3040cae1dc0000000000000000000000000000000000000000000031cb01a35d53040cae1dc29edf1cb021868d3040cae1dc0000000000000000000000c72c0995a34c1032b87717000c72c0861a34c10336077c72c0995a34c1032b8831df1cb021868d3040cae1dc1400358d1b1cb021868cae1df1cb021868d3040cee2b877c72c0995c068d3040cae1dc0000000000000000000000c72c068d754c1032b87702b1cb026568d3040cdf2b877c72c0861a34c1032b87710f75d171cb01a34c1032b877c72c068d754c1032b87718b1cb026568d594c1032b8770031cb021868d3046cae1df1cb0257861a34c1032b87700358c72c0861302b87711400c72c0861a34c1033a877c72c0995a34c1032b8770d357cff1cb02184c1032b877) else (if i < 2144 then 0xe631cb021868d3040cae1df1cb9ec08613040cae1dc56c72c0861a34c1032b87f11792d16c0861a34c1032b877d171cb01a35d53040cae1df58c72c08613040cae1dc45dd71cb02a168d3040cae1df1cb026568d3040cae1dc42c72c0861a34c103324ae1df1cb028c68d3040cee2b877e931cb026568d3040cae1df1cb021868d3040cf12b877c72c0861a34c1032b8770ab1cc32c0861a34c1032b877000000000000000000000000000000000000000000000c72e7b021868d3040c8f1df1cb026568d574c1032b877c971cb021868d3040cae1dc0000000000000000000000c72c0861a35653040cae1df1cb021868d3040cae1dc10c72dcb021868d3040cae1dc00c72c095da34c1032b877cff1cb02184c1032b87711400c7300b02654c1032b877c72d5b021868d3040cae1df1cb021868d3040cdf2b8770000000000000000000000000c72e0b021868d3040c77 else 0xc72c0861a34c1032b89a1df1cb021868d3040cae1dc27c72c0861d568d3040cae1dc00c72c0861a34c1222b877e131cb021868d3040cae1df3fc72d9b02184c1032b877c72c0995a34c1032b87706000b026568d594c1032b877c72c068d754c1032b8770eb1cb021868d9c4c1032b877c72c0911a34c1032b87710b1cb021868d3040cae26077c72c0861a34c1032b87708396c72c0861a34c1032b8770031cb021868d30494ae1df47c72c0861a34c1032b877c72c0861a355d3040cae1df92c72c0995a34c1032b8770031cb021868d3040cd01df3fc72c0861c04c1032b877c72c0861a34c11b40cae1df1cb026568d3040cdd2b8770031cb01754c1032b8771171cb029b68d754c1032b877c72c0861a34c10c40cae1dc00c72c068d844c1032b877c72c0995a34c1032b8771bb3fc72c08613040cee2b877c72c0995a368d3040cae1df8dc72c0861a34c1032b877c72c07f5a35d53040cae1df1cb021868d3040cae22c77)) else (if i < 2240 then (if i < 2208 then 0xc72c0861a34c12240cae1df1cc72c068d754c1032b8770031cb0286861a34c0ae1df3fc72c0861594c1032b877c72c0861a34c1032b8770d31cb01a35d5534c1032b877c72c0861a3585302b8771bb3fc72c08613040cdf2b877c72c0861a34c1032b877140000031cc45a34c1032b877c72c0861a34c1032b87c1df3fc72c08613040cae1dc2ac72c0861a768d3040cae1df3fc72c08613040cae1dc3400358c72c0995a34c0ae1df1cb021868d3040cdd2b877c72c0861a34c1032b8770631cb021868d3040ced2b877c72c0ad61868d3040cae1dfa2c72c0a4a1868d032b877c72c0995a34c1032b8891df1cb021868da34c1032b877c72c0861a34c103354ae1df3fc72c0861844c1032b877c72c0a85a35d53040cae1df1cb02184c1032b8771141fc72c09bda35d53040cae1dc0000000000000000000000c72c0861c968d3040cae1df1cb026568d3040cae1dc21000000000000000000000000000000000000000000000 else 0xc72c0b026568d3040cae1df1cb021868d30451032b877cff1cb021855d3040cae1df1cb021868d3040cae1dc1dcff1cb026568d3040cae1df1cb02a19e1a34c1032b8770031cc02ebb013040cae1dfa6c72c0861a34c1032b8770033fc72c06113040cae1df97c72c0861a34c1032b877c72c0861a34c1032b88e1df3fc72c08613040cae1dc5c0031cb01c968d3040cae1df1cbba1868d3040cee2b877c72c0861a34c1032b8891df1cb021868d3040ce32b877c72c0861a34c1032b87d1df1cb021868d3040cae1dc53c72c0861a34c1032b88d1df64c72c0861a34c1032b877c72c0861a35b93040cae1df95c72c0861a34c1032b877c72c068d754c1032b87704f1cc6ac0861a34c1032b8770031cb02184c1032b8771573fc72c08613040cae20c770031cb021868d514c0ae1df1cb021868d304ad032b877c72c09961868d614c1031df1cb0218765a34c1032b877002c0861a35653040cae1df1cb026568d754c1032b877) else (if i < 2272 then 0xce71cb01a35d53040cae1df3fc72c08613040cdd2b877c72c0861a34c1032b8770e71cbfac068d754c1032b877c72c0a1a1868d3040cae1df3fc72c0861a34c1032b877c72c0861a35a93040cae1df3fc72c08613040cae1dc180031cb02184c1032b87f1df1cb0218825a34c1032b877c72c0861a34c103380ae1df1cb021868d3040cae1dc5ec72c0aa21868d3040cae1dc00c72c0995a35853040c77e031cb021868d3040cae1dc00c72c0765a34c1032b877c72c9b021868d3040cae1df1cb026568d964c1032b877c72c0861a34c1032b8771d792c72c0861a3585302b877c7303b021868d3040cae1dfa4cff1cb02184c1032b877cff1cb02184c1032b87710b58c72c0995a34c1032b8770031caaa6568d3040cae1df1cb021868d3040cae1dc07dd71cb01a34c13040cae1df1cb021868d3040cae1dc60c72c0861a34f9032b8770df55c72c0861a34c1032b87700358c72c0861a34c0ae1df1cb021868d3040cae1dc21 else 0xc72c0861a34c1032b8771131cb2ac0861a34c1032b877c72c0861a34c1032b88a1df1cb02187fda34c1032b877c72c0995a34c1032b87718b1cb021868d3040cae1dc0cc72c0861a34c1032b8871df1cb026a861a34c1032b87700355b021868d3040cae1df1cb026568d30475032b877c72c068d754c13040cae1dc00cfec0861594c1032b8770031cb021868d30458ae1df1cb027b995a34c1032b877e0775c72c068d3040cae1df1cb9ec0995a34c1032b877c72c0995a34c1032b87707f2eb021868d3040cae1dc45d631cb021868d3040cae1df1cb026568d3040cae1dc30002ebb01a35653040cae1df1cb021868d3040cae23077c72c09e26568d3040cae1df1cb026568d3040cae1dc58c72c0861a35453040cae1df1cbaac0861a34c1032b877c72c0861a34c1033a4ae1df66c72c0861a34c1032b877c72c0995a34c1032b8770971cb021868d464c1033b877e331cb026568d3040cae1df1cbaac0995a34c1032b877))) else (if i < 2432 then (if i < 2368 then (if i < 2336 then 0xcff1cb02184c1032b8771bb1cb021868d3040cae1dc690031cb01a35d53040cae1df48c72c0861a34c1032b877c72c0861a352d3040cae1dfb4c72c0861a34c1032b877c72c0861a3545302b88f1df1cb021868d3040cae1dc6dc72ebb01a35d53040cae1df1cb021868d3040cae1dc1f0031cbaac068d3040cae1dfa7c72c0861a34c1032b87700375cff1cb013040cae1df1cb021870130475032b877c72c0ae21868d3040cae1df92cff1cb02184c1032b877e331cb021868d3040cae1dfb3c72c0861a34c1032b877c72c0ab61868d3040cae1df1cb021868d3040cae1dc0d0031cb026568d3040c8f1df1cb021868d3040cae1dc58cff1cb02184c1032b8891df1cb021868d3040ce42b87700358cff1cb02184c0ae1df1cb0265861a34c10323c77c72c0861a34c12940cae1dc00c72c0825a34c1032b87700358c72ebb01a34c0ae1df1cb021868d394c1032b877c72c0861a34c1032b87703f1cb02b4861a34c1032b877 else 0xc72c0861a34c1032f4ae1df1cb022a68d3040cae1dc21cfb1cb021868d3040cae1dc00c72c09953040cae1dc45c72d0b021868d3040cae1df3fc72c08614b4c1032b877d633fc72c08613040cae1df27b021868d3040cae1dc3ac72c0861c568d3040cae1df1cb01a35d5614c1032b877d171cb026568d3040cae1df1cc26c0861a34c1032b877c72c0861a35953040cae1df1cb021868d354c1032b877c72c0861bc68d3040cae1df28c72c0861a34c1032b877d12c0861a34c1032b8771bb33c72c068d754c1032b877c72c0861a34c103358ae1df1cb021868d3040cae1dc15c72c0861a35f93040cae1df1cb024868d3040cae23c770031cb024868d3040cae1df3fcff1cb02184c1032b877ec31cb021868d3040cae1df3fc72c0b02184c1032b877c72c08de1868d3040cae1df7bc72c068d754c1032b877c72c0861a34c11d40cae1df3fc72c08613040cae1dc21d5f1cb9ec0861a34c1031df1cb021868d3040cae1dc72) else (if i < 2400 then 0xc72c0861a34c1032b8841df1cb021868d3040cae1dc28c72c093a184c1032b87711745c72c0861a34c1032b877cff1cb02788613040cae1df1cb02186b1a34c1032b8770033fc72c05d53040cae1dc00c72c068d7e4c1032b8770031cb02657013040cae1df1cb6ac0861a34c1032b877c72c068d754c1032b8771df1cb02b268d754c1032b877c72c0861a34c1032b8881dc00c72c08dda34c1032b8770031cb01e768d754c1031df1cc02c068d754c1032b877c72c09c61868d3040cae1df1cb02657f5a34c1032b877c72c0aa5a35653040cae1df1cb021868d3040cea2b8770031cb02184c1032b87715bb5c72c0861a34c1032b877e8b57b021868d3040cae1df1cb021868d3040ccb2b8770031cbaeaa68d3040cae1df1cb026568d3040cae1dc3ac72c0a6e6568d3040cae1df1cb0281861a34c1032b877003a4e331cb021868d3040f1cb02186a1a34c1032b877d1b1cb026568d3040cae1df75c72c068d3040cae1dc77 else 0xc72f6b021868d303b8ae1df1cb01a35d53040cae23c77cff1cb02184c1032b87718b1cb021868d30481032b877c72c09966568d3040cae1df1cc72c0995a34c1032b877c72c068d7558d3040cae1df81c72e7b01a34c1032b877c72ecb021868d3040cae1df1cbfec0861a34c1032b877c72c0995a354d3040cae1df61c72c0861a34c1032b877c9f1cb021868d3040cae1dc00c72c0861a34c0f52b877d56c0861a34c1032b88f1df1cbbac0861a34c1032b877c72c08a1a34c1032b87707f1cb021868d3040cae1dc3ac72c0861a34c1032b8771973fc72c086130475032b877cff33b021868d3040cae1df1cb021868d3040cd82b877c72c0a7a187013040cae1dc00c72c0709a35d53040caec72c0861c668d3040cae1df1cb021868d3b4c1032b877c72c0861304c1032b8771173fc72c08613040cae1dc58cff1cb02184c1032b87707f1cb026f995a34c1032b877c72c0861a34c1032b8770cb1cc16c0861a34c1032b877)) else (if i < 2496 then (if i < 2464 then 0xc72c0a8a1868d3040cae1df1cb021868d3040cf52b877c72c0861a354d3040cae1df33c72c068d7e4c1032b877d9f1cb021868d3040cae1df57c72c09961868d3040c77c72c0861a34c1032b87706f1cc2ac0861a34c1032b877c7311b01a35d53040cae1df1cb021868d3040cae1dc73c72c0861a34c10339cae1dfa8c72c0861a34c1032b877e8b1cb021868d5740cae1df1cb021868d3040cae1dc2d0038cc7300b02184c1031df1cb026f861a34c1032b877e8f1cb021868d3040cae1df1cb02a6861a34c1032b877c72c09e21868d3040cae1df1cb021868d3040ccc1dc3ac72c0995a34c1032b87704f1cb02a1861a34c1032b877d831cb021868d3040cae1dc00c72c09393040cae1dc45c7304b021868d3040cae1df98cff1cb02184c1032b877dd71cb029268d3040cae1dfa5c72c0861a34c1032b877cff1cb02185d53040cae1df1cb021868d3040cae284770031cb027168d3040cae1df75c72c068d3040cae1dc37 else 0xc72c0861a34c103340771171cb9ec0861a34c10337477dd71cb01a34c1032b8771071cb02186ada34c1032b87700357c72c0995a34c1031df1cb021868d704c1032b877c72feb021868d3040cae1df3dc72c0861a34c1032b877c72c0861a3585534c0ae1df1cb021868d3040cae1ec77c72c0a49a35d53040cae1df1cb01a35d53040cae1dc37c72c0995a358d3040cae1df3fc72c0861fd4c1032b8770031cbaec04c1032b8771171cb021868d3040cae24477ee71cb021868d3040cae1df1cb5ac0861a34c1032b877ce71cb026568d3040cae1df1cb021868d3040cae1dc13c72c0861a34c11040cae1df1cbfac0995a34c1032b877d173fc72c08613040cae1df1cb02ab861a34c1032b877c72c0a761868d3040cae1df1cc72c0861a34c1032b877e171cb021868d3040cae1dc00c72ecb01a34c1032b877002c0aa5a35653040cae1df1cc0ac068d754c1032b877d3b1cb021868d3040cae1df7ec72c0995a34c1032b877) else (if i < 2528 then 0xcff1cb026f8613040cae1df1cb021868d3040cae1dc05c72c0861a34c1032b8771a31cb021868d3040cae24077cff1cb02a18613040cae1df1cb02184c1032b8771dc45c72c0861a35353040cae1df1cb02b2995a34c1032b877e4b1cb01ce68d3040cae1dc00e331cb01c968d3040c77caf1cb021868d3040cae1df87c72c0861a34c1032b877ea71cb021868d3040cae1df1cb021868d3040cae200770031cb026568d3040cae1df1cb026568d304c1032b877c72c09961868d3040cae1df3fc72c08613040cae1dc3ac72c0861a34c1032b8771677ec72c0861a34c1032b877c72c0861a34c1032b8770731cb22c0861a34c1032b877c72c0709a35d53040cae1df1cb021868d30488ae1dc450038cb021868d594c1031df1cb0244861a34c1032b8770031cb021868d3040c9c1df1cb021868d303b8ae1dc6ec72c068d755913040cae1dc00c9ec0861a34c1032b877c72c0861a34c1033a8831df1cb021868d3040cae1dc3c else 0xc72c0861a34c13040cae1dc00c72c0861a34c1032b877cff1cb021854d3040cae1df57c72c0765a34c1032b877c72c08dda34c1032b8770bb3fc72c08613040cae1dc13c72c0aca1868d3040cae1df3fc72c08613040cae1dc59cb31cb021868d3040cae1dc00c72c0911a34c1032b877d1733b021868d3040cae1df6ac72c0861a34c1032b877c72c0899a34c1032b8770631cb02187013040cae1dc77c72c0861a35393040cae1df3fc731cb02184c1032b877c72ebb026568d3040cae1dfb6c72c0861a34c1032b877d8f1cb021868d3040cae1df1cb021868d4a4c1032b877c72c0861a34c12540cae1df1cb02184c11d40cae1dc450038cdd71cb01a34c1031df1cb029e861a34c1032b877c72c068d754c1032b87702fa2dd71cb01a34c1032b877c72c0861a34c1032b87706b1cb021868d3040cae1dc4ee333fc72c08613040cae1df1cb02a1995a34c1032b877c72c0861a358d3040cae1dc00e3358c72c0861a34c077)))) else (if i < 2816 then (if i < 2688 then (if i < 2624 then (if i < 2592 then 0xc72c068d754c1032b87700fa9cff1cb02184c1032b877c72c0861a34c1032b8861df1cb021868d3040cae1dc52c72c0861a34c1032b87719f1cb0270995a34c1032b8770000000000000000000000000c72c0861a34c103330770038cc72c068d754c1031dfa2c72c068d754c1032b877c72ebb021868d3040cae1df3fc72c0996184c1032b877c72c0a3da35d53040cae1df29c72c0861a34c1032b8770038cc72aa861a34c1031dfa2e4ac0861a34c1032b877c72c0995a35853040cae1df1cb021868d3040cae1dc66c72c093a1868d3040cae1df1cb021868d3040cd81dc6ec72c0a321868d3040cae1df33c72c0995a34c1032b877cff1cbfac08613040cae1df92c72f6b021868d302b877d071cb021868d3040cae1df1cb021868d3040cae1dc5de071cb026568d3040cae1df1cb026568d3040d032b877def1cb026568d3040cae1df1cb021868d3040cbf1dc1fc72c0861a359d3040cae1df1cb025768d3040cae1dc5c else 0xc72c0861a34c103384ae1df1cb026568d3040cae1dc77ec71cb021868d3040cae1df44c72c0861a34c1032b877d8f3fc72c08613040cae1df1cc02c0995a34c1032b877c72c0861a34c1032b8991df1cb023f68d3040cae1dc3a0031cb022a68d3040cae1dc00c72c0a31a34c1032b877c72c0861a34c1252b8771731cb021868d8b4c1032b877ee31cb021868d3040cae1dc00c7303b02184c1032b877c72d3b021868d3040cae1df33c72c0861a34c1032b877c72c08613040cae1dc450231cb021868d3040cae1dc06003a4d631cb021868d302b800cff1cb02654c1032b877c72c0aaa0968d3040cae1df1cb02b7861a34c1032b8770036ac72c068d3040cae1df3fc72c0861634c1032b877def1cb021868d3040cae1df57c72c068d754c1032b877c72c08613040cae1fc771171cb021868d3040cae1dc3fc72c0a4a184c1032b8771171cb021868d3040cae1dc40dab1cb02b268d3040cae1df1cb02184c1032b87711437) else (if i < 2656 then 0xcff1cb02184c1032b87719b1cb021868d3040cae1dc17c72c0701a35d53040cae1df1cb026568d3040cae21477000000000000000000000000000000000000000000000c72c0aba1868d3040cae1df1cb02b0861a34c1032b877c72c0861a34c1032b8771df1cb021868d304a1032b8770000000000000000000000000000000000000000000000031cb020368d3040cae1df1cb021868d3040ce62b877000000000000000000000031cb021868d3040cae1dc12000000000000000000000031cb021868d3040cc22b877c72c09c21868d3040cae1df1cb026568d3040cae23c77ebb1cb021868d3040cae1dc00cff1cb02184c1032b877d4f1cb021868d3040cae1df1cb02ac861a34c1032b877cff1cb02184c13040cae1df3fc72c0aca184c1032b877cff39c72c08613040cae1dc00c72c0939a34c1032b8770031cbaec068d3040cae1df8ac72c0861a34c1032b877e071cb021868d3040cae1df1cb021868d3040cae1dc16 else 0x33fccf1cb02184c1032b877c72c0861a34c1032b8771c00000000000000000000000000000000000000000000000000000000000000000000e3f1cb021868d3040cae1dc000031cb01e768d3040c77cff1cb02b78613040cae1df1cb32c0861a34c1032b877def3fc72c08613040cae1df1cb02a1a49a34c1032b8770031cb021868d3040cae1ff1cb021868d3040cae23c77dd71cb01a35653040cae1df1cb021868d624c1032b877cff1cbaec08613040cae1df1cb02186a5a34c1032b8770000000000000000000000375c72c068d3040cdf2b877c72d1b021868d3040cae1df1cb66c068d754c1032b877c72c0861a34c1032b87709341cff1cb02184c1032b877c72c068d754c1033b8ae1df1cb026568d694c1032b87700381c72c068d3040cae1df75c72c068d3040cae1dc2ac72c0861a34f13040cae1df1cb021868d3040cf32b8770031cb021852d3040cae1df42c72c0861a34c1032b877)) else (if i < 2752 then (if i < 2720 then 0x31cb46c068d3040cae1df1cb021868d4c4c1032b877c72c0861a34c1032b8770071cb01a35d53040cae1dc2ac72c068d755653040cae1df1cb026568d644c1032b877c72c08fa1868d3040cae1df1cb023f861a34c1032b877c72c08ba1868d3040cae1df1cb028a861a34c1032b877cbb1cb021868d3040cae1dc00d12c0861a34c1032b877c72c0995a34c1032b8770dc00c72ee861a34c1032b877c72c0995a34c1032b8770bb1cb9ec0861fd68d3040c77c72e8b021868d3040cae1dc00d631cc02c0861302b877e8b1cb02184c1032b8771171cb021868d3040cae1dc55c72c068d754c1032b8770d31cb021868d3040cae1dc020038cc72c08613040c771171cb021868d574c11d40caec72c0861a34c12740cae1dc0000000000000000000000c72f6b021868d30474ae1df3fc72c0861614c1032b877c72c0ada1868d3040cae1dc0000000000000000000000c72c0861a34c1032b87707b1cb021868d3040cae21477 else 0xdd71cb01a34c1032b88c1df75c72c068da34c1032b8770031cbeac0861a340cae1df1cb021868d3040cae1dc08c72e9b021868d3040cae1df1cbeac0861a34c1032b877c72fab02b2861a340cae1df1cb021868d3040cae1fc770031cc45a35d53040cae1df1cb0292995a34c1032b877c72c0861a36753040cae1df1cb021868d3040cae1dc37c72c0861a34c12140cae1df1cb0286861a35d5302b877c72c095a1868d3040cae1df1cb021868d3040cae1dc6300358b021868d594c0ae1dc00c72c0861a35193040c77c72c0861a35853040c771731cb01a35d53040cae20c77e0b1cb021868d3040cae1df1cb021868d664c1032b877dd71cb01a34c1032b8770631cb02a5861a34c1032b877cff1cb01a36113040cae1df1cc0ac0861a34c1032b877cff1cb02184c1032b8771df1cb01a35d53040cae1dc45c72c0861a34c1032b87703b3fc7300b02184c1032b877c72c0ae61868d3040cae1df1cb01a35d53040cdf2b877) else (if i < 2784 then 0xc72c068d754c103374ae1df1cb021868d3040cae1dc3e0000000000000000000000000cff1cbaec04c1032b877c72c0861a34c11a40cae1dc00dd6c068d594c1032b877c72c068da35d53040cae1df1cb01a35d53040cae1dc1800375d631cb01a34c0ae1dc00cff33b02184c1032b8770031cb023f68d3040cae1dfadc72c0861a34c1032b877e931cb01a35d53040cae1dc00e331cb02187013040c77c72c0abe1868d3040cae1dc00c730bb01a34c1032b877c72c08c9a34c1032b8770ab1cb0292861a34c1032b877c72c0861a34c11940cae1df2ac72c0861a34c1032b877c72c0861a34c1032b8770271cb021868d3040cae1dc110031cb02186b13040cae1dc00c7311b01a34c1032b877c72c068d754c1032b87710b1cbb6c0861a34c1032b877c72c0861c268d3040cae1df1cb026568d3040cae1dc36cff1cb02184c1032b88f1df1cb01a35d53040cae1dc5cc72c0861a35053040cae1df1cb01a35d5574c1032b877 else 0xc72c08613040cdf2b87711400000000000000000000000000000000000000000000357c72c0995a34c1032b8770031cb02a968d3040cae1df1cb01a35d53040cae1dc21000000000000000000000031cb021868d3040cae25477dd73fc72c068d3040cae1dc00cbac0861a34c1032b877002c068d755653040cae1dc00e331cb026568d3040c77e1b1cb021868d3040cae1df1cb021868d3040cae20877e8b1cb026568d3040cae1df1cb021868d3040cae1dc41c72c08613040cae1dc450535cc72c0861a34c1032b877002aa861a35653040cae1dc00c7302b01a34c1032b877c72c0861a34c1032b8770db1cb01a35d53040cae1dc6ec7306b021868d3040cae1dfa2c72c0861a34c10327077e4b1cb01a35d53040cae1df1cb021868d3040c8f1dc5cc72c0861a34c11b2b8770eb1cb021868d614c103374770000000000000000000000382cff1cb02184c1032b8770031cb028668d754c0ae1dc00c72c0861a34c1032fc77))) else (if i < 2944 then (if i < 2880 then (if i < 2848 then 0xc72c0861a34c1032b8770b38cc72c0725a34c1032b877c72c0861c05653040cae1df1cb021868d3040cae25077e8b1cb021868d3040cae1df1cb02187013040cae1dc2a000000000000000000000000000000000000000000000c72c0861a34c1033c8ae1df1cb02187013040cdf2b877c72c0a19a35d53040cae1df1cb021868d3040cae1e877c72c0861594c1032b8771140000000000000000000000c72c0861a34d93040cae1dc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000031cb0218739a34c1032b877cff1cb02185913040cae1df75d631cb01a34c1032b877c72c0995a34c103394ae1df1cb021868d3040cae1dc3d00358c72c068d754c0ae1df1cb021868d3040cb72b877cff1cb02928613040cae1df1cb02184c1032b8771142ac72c0861a34c1032b89c1dc00d631caaa1868d302b877cff1cb02184c1032b8770df1cb01a35d53040cae22477 else 0xc72c0861a34c1033b8ae1df1cc72c0861a34c1032b877c72c0861a34c1032b8770eb1cb021868d534c1032b877c72c0861a34c1032b87707f1cb021868d3040cae1dc13c72c0861a34c1032b8891df1cb026f861a34c1032b8770031cb01a35d53040cae1df1cb0265861a34c1032b877c72c089a1868d3040cae1df75c72c068d3040cae1dc1fc72c0861a34c1033bcae1df1cb01a35d5754c1032b877c72c0861a35a13040cae1df1cb021868d574c0f52b8770031cb02184c1222b8771171cb021868d3040cf02b877c72c0861a34c1032b87700fabc72c0861a34c1032b877c72c0a666568d3040cae1dc00c72c0861ab4c1032b877c72c0861a34c103388ae1df1cb021868d3040cae1dc33c72c0861a34c1032b8771931cb021868d3040cae1dc560038cc72c0861a34c1031df1cb026568d3040cae1dc45c72c0861e168d3040cae1df57c72c0861a34c1032b877c72c0861e468d3040cae1df1cb021868d3040cae1dc71) else (if i < 2912 then 0xc72c0a4a1868d3040cae1df1cb021868d634c1032b877c72c0861a355d3040cae1df1cb021868d3040cae1dc2ac72c0861a34c11d40cae1df57c72c0861a34c1032b877c72c0861a34c1032b8770dc00cff1cb02184c1032b877e8b1cb021868d3040cae1dc00d631cb021868d302b877c72c0861a34c1032b8770631cbfac0861a34c1032b877c72c0861a35653040cae1dc0000000000000000000000000000000000000000000031cb02b2861a34c1032b8770031cb021868d3040cae1df7bc72c0861a34c1032b877000000000000000000000031cb021868d3040cae1dc34e331cb021868d3040cae1df1cb021868d3040cdd2b877000000000000000000000031cb021868d3040cdf2b877d171cb021868d3040cae1dc00c72ebb01a34c1032b877c72ebb021868d3040cae1df33c72c0861a34c1032b877c72c0861a34c1032b88f1df1cb0278861a34c1032b877c72c0861a34c1032b8771df1cb021868d3040cae1dc58 else 0xc72c0861a34c1032b877002c0861a35653040cae1df1cb021868d3040cae1dc21d631cb021868d3040cae1df1cb021868da34c1032b877cff1cb021868d3040cae1df1cb02a1861a34c1032b877c72c0861a34c1032b8771171cb021868d304c1032b8770031cb026568d3040cae1dc00e331cb021868d3040c77)) else 0))) else 0))
  (tab >>> (90*(i % 32))) &&& 0x3ffffffffffffffffffffff

def delta517 (i : Nat) : Nat :=
  let tab : Nat := (if i < 1024 then (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then 0x1044320000000000000034120400004300c018001c010180c00070002c00040e00000000180000000100000000583800000402c1e09028000c00008240000000040400000000000 else 0x3000020000008000008804060d0100004030202004020700c00000000800040000002030a00000000102800000080000000000006000880012040000442000400c4c150100c0005) else (if i < 192 then 0x4040d00010100119800001a0d81804060080402000003418050000c420300020260301014100b0000000020383c0810000040001068400000020000604018080400050100000 else 0x1400020000008010000800080c8b0440d0101006000080c00001500c84060100400010300000000c80006010084404030181004050080c0c00018000001050000c01030180030)) else (if i < 384 then (if i < 320 then 0x180006030700c000100020002d000c4141c1180024021680830030318c00560c0b400270388434000780c020000054140100800160c068300002070080000000040e00028040202 else 0xc0000d008000000010080006000000601010201a0100800020708800000d200c80004188001602000600c040381420000015000030180006010b00000070000c00041d8000c20) else (if i < 448 then 0x1c0c02010007810000000200010180004030280400030080800008000400000400420000483007040040000100441400000040000000000600000000001000100c00000080c01 else 0x180000040000400030000808010300000000001c00000103c000f06000000800808020100000000b0202400070002410010902c0400000100400060000000000080422000140200))) else (if i < 768 then (if i < 640 then (if i < 576 then 0x80002000000400040400000001a0002e010184c001000000020a000000400028002e00108001603010442a020004808000001c000b0001006050200000000a0001202008240003 else 0x1000080198c04001100004010100c0a000d0180019060040800000000408060040402020040013110e804010080892040081404100204c00000e000140b0302c060100800002b) else (if i < 704 then 0x18000a19040180c00038000006010000000078001207018001c070180c0805028100a1100800047a0102c020204824000400000140441848c401030043e0003808120b008f40235 else 0xc001c0880c08030003404010400832001182400060181c26230280c1a03080300a04028c402920301808090301474010380800052e924a016018001209000b80000028340000)) else (if i < 896 then (if i < 832 then 0x68200a010100002421b000480b0e0001a011300d16010203000000039c00001e018020107034060d28a98027c0103802003c0040e00008300800038dc0201060f8147d3d8001c2c else 0x438250009c26027681c0200004d4002803868120a058042c0a030001c280000408420280036003881002000180486240081002000105c0603011c000001683c0000070700000) else (if i < 960 then 0xd00138090c818000000001c80432800020b05024522f0380f9e1c0680001e11400800010010c0068140b0000a92000d8190000000030281070100580c0004078004a037a0fc33bd else 0xc81000010000402060080c00000000002030005c04020000008000403c1402040200002018000a0700800080b0080400050e028020203804120102000000015800009035f4007f9)))) else (if i < 1536 then (if i < 1280 then (if i < 1152 then (if i < 1088 then 0x48040401238100006008000000078c004000002c04000087c0004000580000020000000000340a000100000580081802070700004010600810000300094000001400020080c0e01 else 0x52000500004000040400000187a010201e07018040001000004800008000a12030a82c0812000040906008000d008000206008001202000000015038000002000001200018140a03) else (if i < 1216 then 0x20001402058002c0202804000a0a828040100824160000008060000000020301800000c008640000020040010012d42404110309c0002014006f0080c0a000382c06090000c000b else 0x38044e1f500680a05040641a07000040000000a4240200078026e0281c000006000060007800020304008002c000140000018040808028480010000601800000002e00028000601)) else (if i < 1408 then (if i < 1344 then 0x11c0003000b41a0111808040f010b800001280032220100c042300000be0a09234107208a0452001682800100080402010892126070037000003700c18006828914040617c3c0b else 0x43300800360f000000000000100001000001400000003c03000100000018102e001208e9602b080498000a8202600008a434070000402001a8001a02) else 0)) else 0))
  (tab >>> (9*(i % 64))) &&& 0x1ff

def six517 (i : Nat) : Nat :=
  let tab : Nat := (if i < 2048 then (if i < 1024 then (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then 0x14479200f9444d41984d210fe448db1e451201113e4d41e45120111448d418880144e83d08f14479200f9444d42181d200f9445101e451201113e4d414479200f9444d41886320cfe449131fc83144e83d10d14479200f9444d419880208ff37ca3214621b8ec340f41e45120111448d41e45120111448d4144792010c444d4144792010c444d41984d210f4448db14479200f9444d4074862011144d1014479200f9444d418881220fe431132245122107430e02244d1bccd384db1e45120111448d41e451201113e4d41984d210fe448db1e45120111448d419880144e83d0ec21879200f9445101e451201113e4d41e45120111448d418881220fe4311314479200f9444d41bc86208df269112244d1bccd385112244d20cfe448db22488219053810c1886320d114491300000000000000021879200f944510144662010e44cd300000000000000021879200f9445101e45120111448d41886320cfe361131fc6f144e83d10d2148620d0e3b4f42148620d0e3e4f400000000000000000000000000000022481220fe431132186f2089a37d111fc83145113d10d1fc83144e83d10d22481220fe44113220662011144d1022481218e642d132148620d0d26cf4000000000000000000000000000000000000000000000000000000000000 else 0x1e45120111448d414479200f9444d42245122107430db21879200f9445101fc83144e83d10d22481220fe431131fc83144e83d10d19888200f944510224882190544d0c1e451201113e4d40000000000000000000000000000000000000000000000000000000000001e45120111448d419888200f9445100000000000000000000000000000000000000000000001e45120111448d42245122107430db1e45120111448d421879200f9445101e451201113e4d400000000000000000000000000000000000000000000021879200f9445100000000000000001e45120111448d41447f20d0e430b400000000000000000000000000000000000000000000000000000000000000000000000000014479200f9444d41e45120111449071e45120111448d41e451201113e4d41e45120111448d418881220fe4411314479200f9444d41bc7f144f43a10d2244d220cd42cdb14479200f9445071984d210f4448db1fc83145113d10d14479200f9444d42244d1bccd42cdb21879200f9445101e45120111448d422481218e642d1314479200f9444d41fc6f144e83d10d1e45120111448d418880145113d08f14479200f94450714479200f9444d41fc85144e83d10e1886320cfe449131fc85145113d10e1e45120111448d41e451201113e4d4) else (if i < 192 then 0x1e4511b909448d41e4511b909448d41441d200f9444a71441d200f9444a719888200f9445101441d200f9444a71e4511b909360d41441d200f9444a72181d200f944510188791bcfe42d1314479200f9444d41441d200f9444a71e4511b911448d419880144d73d0ec1441d200f9444a7144791b8d8424d41441d200f9444a72244d1bccd384db144791b8f9424d4144791b8d8424d41441d200f9444a707451201113e4d31fc6f144e83d10d1e4511b909360d418880145113d08f14479200f9444d41441d2010c444a71984d1bcfe3e5111fc83144d73d10d144791b8d8424d41441d200f9444a71984d190a9384db144791b8d8424d41e4511b909448d400000000000000019880144e83d0ec1e4511b909448d41984d20cfe448db144791b8d8424d41441d200f9444a714479200f9424d40000000000000001e4511b90942cd41984d20cfe448db14479200f9444d41984d190a9384db1441d200f9444a714479200f9444d41e4511b909448d41447f20d0e3f8b422479144d43810c144792010c444d414479200f9444d41e45120111448d41e45120111448d414479200f9444d42145115cdf435131888120cd342d13220662011144d100000000000000001883a144e83d10e2206620111449101e451201113e4d407486201113e510 else 0x1984d20cfe448db14479200f9444d414479200f9444d40000000000000001e4511b909448d41984d190cd384db1984d208f4448db14479200f9444d421879200f9445101e4511b909448d414479200f9444d4198511bcfe448db1441d200f9444a707486201113e5101e45120111448d41984d208f4430db144791b8d8424d4144791b8d8424d41984d1bcfe3e4db144791b8d8424d413479200f9444d414479200f9444d41984d20ccd448db00000000000000018880144e83d08f19880144e83d0ec14c83144e83d10e1441d200f9444a719880144e83d0ec18881220fe431131e4511b909360d418881220fe43113144791b90c424d41984d190cd448db1886320cfe449130f8511e8f4448d31e4511b909448d407451201113e4a71e451201093e4d4198511bcfe448db1e4511b909360d41984d1bcfe3e4db1fc80144e83d0ec1441d200f9444d41984d208f4448db1984d210f4448db1e451201113e4d41e4511b909360d41441d200d8444a7144791b8d8424d41e45120111448d4144791b8d8424d41e4511b909448d4144791b8d8424d414479200f9444d4144791b8d8424d41441d200f9444a71fc83144d73d10d14479200f9444d41984d208cd448db1441d200f9444a71441d200f9444a714479200f9444d41e45120111448d4)) else (if i < 384 then (if i < 320 then 0x1886f144e83d08f19851221073e4e01e4511b909360d41e451201113e4d41441d200f9444a714479200f9424d41883a144e83d10e1e4511b909360d41984d190a9384db14479200f9444d41e4511b909360d4214861b8ec340e6198511bcfe448db144791b8d8424d41441d200f9444a71e451201093e4d4144791b8d8424d41984d190cd384db1e4511b909448d4198511bc9b448db1e4511b909448d414479200f9444d41441d200f9444a71441d200f9444a71e451201113e4d41e4511b909360d41e4511b909448d41e4511b909448d41347f2010e44c931e45120111448d41441d200f9444a7144791b8d8424d41441d200f9444a7144791b8d8424d418880144e83d08f1e4511b909360d414479200f9444d4144791b8d8424d40e886144f43a10e1e45120111430d41e4511b909448d41e4511b909448d41fc6e15d0d37ca31e45120111448d419880208ff37ca31e4511b909430d41984d20cfe448db1984d1bcfe3e4db1e4511b909448d41e45120111448d41441d200f9444a714479200f928cd42181d200f9445101e4511b909448d41441d200f9444a71984d190a9384db07451201113e4a71984d210f4448db18880144e83d08f1886320cd3449131984d208f4448db14479200f9444d41441d200f9444a71e4511b909448d4 else 0x1441d200f9444a714479200f9444d40000000000000001441d200f9444a700000000000000000000000000000020062144f43a08f1984d20cfe448db1984d210f4448db1886320cfe449131984d220cd448db1e4511b909448d400000000000000000000000000000014479200f9444d41e45120109448d41441d200f9444a71e4511b909448d40000000000000001e451201113e4d41e4511b909448d4144791b8d8444d41e451201113e4d41e4511b909448d41fc85144e83d10e18880144e83d08f19888200f9445101441d200f9444a71e4511b909360d414479200f9444d41441d200f9444a714479200f9424d4144791b8d8424d414479200d8444d41984d20cfe448db1984d190cd384db00000000000000019880144e841cec1fc6f144e83d10d1441d2010c444a7000000000000000144791b8d8424d40000000000000002244d1bccd384db1e4511b909360d41e4511b909448d41e4511b909448d41984d210f4448db14479200f9444d414479200f9424d41e4511b909448d41441d200f9444a7198511bcfe448db1e4511b909448d41984d210f4448db1e4511b909448d41888120cd342d1319851190fe384db1e451201113e4d414479200f9444d407451201113e4a71984d208f4448db1441d200f9444a71984d20cfe448db) else (if i < 448 then 0x14479200d8444d41984d208f4448db19880208ff37ca31e4511b909360d4144791b8d8424d4144791b8d8424d4074511b909360e60000000000000001441d200f9444a71e4511b909448d41e4511b909448d41984d208f4448db144791b8d8425101e4511b909448d4144791b8d8424d41e4511b909360d41886320cd3449131e4511b909448d4214862010d26ce61441d2010c444a71886320cd34491314479200f9444d4198511bcfe360e013479200f9444d41fc80144e83d0ec1441d200f9444a72008120cfe449131441d200f9444a700000000000000000000000000000014479200f9444d418880144e83d08f2244d1bccd384db0000000000000000000000000000001e4511b90944910144791b8d8424d41984d220cd448db144791b8d8424d41984d20ccd448db0000000000000001e4511b909448d41e4511b909360d41e45120111448d41886320cfe361131984d210f4448db0e862144f43a10e1441d200f9444a7144791b8d8424d414479200f9444d41441d200f9444a70000000000000001984d208f4448db14479200f9424d41441d200f9444a71e451201113e4d40000000000000002148620d0d26cf40000000000000001e4511b909360d41441d200f9444a7144791b8d8424d41fc6f144d73d10d2181d200f944510 else 0x1984d208cd448db198511bc9b360e01984d190cd384db198511bcfe448db14479200f9444d420066144f43a0ec1984d208f4448db1984d20ccd448db1e4511b909448d414479200f9444d4144791b8d8424d414479200f9444d41e4511b909360d4198511bcfe360e01e45120111448d41e4511b909448d41e45120111448d414479200f9444d4144791b8d8424d41e4511b909448d414479200f9444d41e4511b909448d407451201113e4a719851221073e4db144791b8d8424d42181d200f94451018880144e83d08f1e4511b909360d41e4511b909360d41984d210f4448db144791b8d8424d41441d200f9444a7144791b8d8424d41984d20cfe448db1e4511b909360d41884d20cfe448db1e451201093e4d41bc7f144f43a10d1441d200f9444a714479200f9444d41bc7f144f43a10d1984d1bcfe3e4db144791b8d8424d4144791b8d8424d41fc6f144e83d10d1984d20ccd448db07451201113e4a7144791b8d8424d41441d200f9444a71e4511b909360d41441d200f9444a71441d200f9444a707486201113e51021879200f9445101e4511b909448d41e4511b909448d40000000000000001441d200f9444a71441d200f9444a714479200f9444d41441d200f9444a70000000000000000000000000000001e4511b9093e4d4))) else (if i < 768 then (if i < 640 then (if i < 576 then 0x144791b8d8424d4198511bc9b448db1e45120109448d4144791b8d8424d41447f20d0d3f8b41984d20cfe448db1e45120111448d4144791b8d8424d4074862011144d10144791b8d8424d4144791b8d8424d41984d210fe448db1e4511b9093e4d414479200f9424d41984d1bcfe3e4db144791b8d8424d41e4511b909448d41984d20ccd448db14479200f9444d419880144d73d0ec1441d2010c444a7198511bcfe448db1886320cfe44913144791b8d8424d41441d200f9444a714479200f9444d41e4511b909448d41441d200f9444a71e4511b909448d41e4511b909448d414479200f9444d419880144e83d0ec14479200f9444d41e451201093e4d41984d1bcfe3e4db1883a144e83d10e14479200f9444d41e4511b909448d41984d20ccd448db144791b8d8424d4144791b8d8424d41984d190a9448db1441d200f9444d314479200f9444d41441d2010c444a7198511bcfe360e018880144e83d08f14479200f9444d4144791b8d8425101441d200f9444a71e45120111448d41441d200f9444a722479144d43810c19880144d73d0ec18880144e83d08f19851190a9384db1e4511b909360d41441d200f9444a72245122107430db198511bcfe360e014479200f9444d4144791b8d8424d41984d190a9384db1fc83144e83d10d else 0x1886320cfe44913144791b8d8424d41441d200f9444a700000000000000014479200f928cd41e45120111448d42244d1bcfe384db0000000000000002181d200f9445101e4511b909448d41984d20ccd448db0000000000000001441d200f9444a7000000000000000144791b8d8424d4198511bcfe360e01e451201093e4d4000000000000000144791b8d8424d41e4511b909448d40000000000000000000000000000001e45120111448d40000000000000001984d190a9448db0000000000000001e4511b909360d41441d200f9444d4000000000000000074511b909360a70000000000000002244d220cd42cdb0000000000000000000000000000001fc6f144e83d10d144791b8d8424d4144531b8ec341100000000000000001441d200f9444a71e451201113e4d41e4511b909448d40000000000000001984d20ccd44902144791b8d8424d41e451201113e4d41984d20cfe448db1984d208f4448db1e451201113e4d41e4511b909448d41e4511b909448d41e4511b90942cd41984d1bcfe3e4db144791b8d8424d4144792010c424d41441d200d8444a71984d208f4448db1441d200f9444a71e45120111448d4144791b8d8424d41984d208f4448db1e45120109448d41441d200f9444a71441d200f9444a71441d200f9444a7) else (if i < 704 then 0x21879200f9445101984d190cd384db1e4511b909360d414479200f9444d414479200f9444d41883a144e83d10e2181d200f9445102244d220cd42cdb1fc6f144e83d10d1985122107430db1e451201113e4d41f4511b909448d41984d20cfe448db1e451201113e4d414479200f9444d41984d208f44488d1e451201113e4d41e45120111448d4144791b8d8424d41441d200f9444a7144791b8d8424d41e4511b909448d41984d20ccd448db1441d200f9444a714479200f9444d419851190a9384db2181d200f94451018880145113d08f1fc83144e83d10d14479200f9444d4144791b8d8424d421879200f9445101984d210e6448db1e4511b909448d41441d200f9444a71984d20cfe448db1e4511b909448d41884d20cfe448db198511bc9b360e0188791bcfe361130000000000000001e4511b909360d41984d20cfe448db07451201113e4a71441d200f9444a71441d200f9444a714479200f928cd40000000000000000000000000000001e45120111448d41e451201113e4d41e4511b909448d419880208ff37ca30000000000000000000000000000001e4511b909360d4144791b8d8424d41e4511b90942cd414479200f9444d414479200f9444d4144661b8ec448b42244d220cd448db19888200f9445101886320cfe44913 else 0x144791b8d8424d41441d1b8d8424a71441d200f9444a71441d1b8d8424a719880144d73d0ec19880144e83d0ec1e4511b909448d41441d1b8d8424a71e4511b909360d41441d200f9424a719851190a9384db144791b8d8424d41441d1b8d8424a71441d1b8d8424d414479200f9444d41e4511b909448d41441d1b8d8424a7144791b8d8424d4144791b8d8424d41441d1b8d8424a7144791b8d8424d41984d1bcfe448db074511b909360a71441d200f9444a714479200f9424d41984d1bd07448db144791b8d8424d41441d1b8d8424a71984d1bcfe448db1441d1b8d8424a71441d1b8d8424a700000000000000014479200f9444d41441d1b8d8424a71e4511b909448d41441d1b8d8424a71441d200f9444a71984d1bcfe448db1441d2010c444a71e44d1b909448a718880144e83d08f1e4511b909448d41984d20cfe448db198511bcfe360e01e4511b909360d414479200f9444d419880144d73d0ec1e4511b909448d407451201113e4a71e4511b90942cd4188791bcfe3e5131e4511b909360d41984d220cd448db1441d200f9444a71fc85144e83d10e19880144e83d0ec1e45120109448d41e4511b909448d40000000000000001441d200f9444a71984d208f4448db18880144e83d08f144791b8d8424d41e4511b909448d4)) else (if i < 896 then (if i < 832 then 0x14479200f9424d41f4511b909360a714479200f9444d4144791b8d8424d41984d1bcfe3e4db1984d1bcfe448db1984d1bcfe448db1984d1bcfe448db198511bcfe448db1441d200f9424a71441d1b8d8424a7144791b8d8424d41e4511b909448d41e4511b909448d41e4511b909448d4198511bcfe448db1441d1b8d8424a7144791b8d8424d41984d1bcfe448db198511bcfe360e01e4511b909360d41984d1bcfe448db074511b909360a7144791b8d8424d4144791b8d8424d41441d200f9444a7144791b8d8424d418880144e83d08f144791b8d8424d420062144f43a08f14479200f9424d419880144d73d0ec19851221073e4db1441d200f9444a71441d1b8d8424a71441d1b8d8424a7074511b909360a71984d1bcfe360db1441d1b8d8424a71441d1b8d8424a71984d1bcfe448db144791b8d8424d419880144d73d0ec1441d1b8d8424a718880144e83d08f1441d200f9444a71441d1b8d8424a71441d1b8d8424a7144791b8d8424d41441d200f9444a7198511bcfe448db144791b8d8424d41441d200f9424a7144791b8d8424d41441d1b8d8424d41e4511b909448d41441d1b8d8424a70000000000000001441d1b8d8424a7074511b909360a71441d200f9444a71441d1b8d8424a71984d190a9384db144791b8d8424a7 else 0x144791b8d8424d4144791b8d8424d418880144e83d08f144211b8d8424d4144791b8d8248d41441d1b8d8424a71984d1bcfe448db1441d1b8d8424d41441d1b8d8424a707451201113e4a71441d1b8d8424a71441d1b8d8444a71441d200f9444a71441d1b8d8424a71441d1b8d8424a7198511bcfe448db1441d1b8d8424a71441d200f9444a71441d1b8d8424a71441d1b8d8424a7074511b909360a7200851bcfe449131441d200f9444a718880144e83d08f1441d200f9444a7198511bcfe360db1e4511b909448d41441d1b8d8424a71441d1b8d8424a71441d1b8d8444a71e4511b909448d4198511bcfe360db198511bcfe360db1984d1bcfe448db1e4511b909360d41e4511b909448d41441d1b8d8424a71e4511b909360d41441d200f9424a71984d20ccd448db1441d1b8d8424a71fc80144e83d0ec20062144f43a08f074511b909448a71441d200d8444a71f4511b909360a71984d20cfe448db1441d1b8d8424a7074511b909360a7144791b8d8424d41e4511b909360d4198511bcfe448db1984d1bcfe448db1984d1bcfe448db1984d1bcfe448db19880144e83d0ec19880144d73d0ec18880144d73d08f134791b8d8424a71984d1bcfe448db1441d200f9444a719880144d73d0ec144791b8d8424d41984d1bcfe448db) else (if i < 960 then 0x1441d200f9444a71441d1b8d8424a71441d1b8d8424a71441d200f9444a7144791b8d8424d418880144d73d08f14479200f9444d4214641b8ec340b41441d1b8d8424a71441d1b8d8424a71441d200f9444a7144791b8d8424d41441d1b8d8424a71984d1bcfe448db1984d1bcfe360db000000000000000144791b8d8424d41441d1b8d8424a71441d200f9424a71441d200f9424a70000000000000001441d1b8d8424a71441d1b8d8424a7198511bcfe448db144791b8d8424d4144791b8d8424d41441d1b8d8444a71441d200f9444a7000000000000000144791b8d8424d41984d1bcfe448db1441d1b8d8424a71441d1b8d8424a7144791b8d8424d41984d208f4448db0f8641b8d84251019880144e83d0ec1984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a7144791b8d8424d4144791b8d8424d4144791b8d8424d41e4511b909448d40000000000000001e4511b909448d41e4511b909448d4074511b909360a71441d200f9444a71441d1b8d8424a71881f14502380e3074511b909360a71984d1bcfe3e4db1441d1b8d8424a71441d200f9424a71441d1b8d8424a71441d1b8f9424a7198511bcfe360db144791b8d8424d41984d1bcfe448db144791b8d8424d41441d1b8d8424a7074511b909360a7 else 0x1441d200f9444a71984d1bcfe448db1441d200f9424a7198511bcfe360db1984d20cfe448db144791b8d8424d418880144e83d08f144791b8d8424d41441d2010c444a71984d1bcfe448db1e4511b909360d4144532010d44cb41984d1bcfe448db144791b8d8424d414479200f928cd41984d1bcfe3e4db1984d1bcfe3e4db00000000000000013479200f9424d40000000000000001e4511b909360d41441d1b8d8424a70000000000000001984d1bcfe448db144791b8d8424d4144791b90c424d4188801450f3d08f1e4511b909448d41e4511b909448d41984d1bcfe448db1441d200d8444a71e4511b909360d4144791b8d8424d40000000000000001441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71984d20cfe448db1984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71441d200f9444a7198511bcfe360e01441d2010c424a71941f218df380f919880144d73d0ec144791b8d8424d41441d1b8d8424a718880144e83d08f144791b8d8424d41441d1b8d8424a71984d1bcfe448db144791b8d8424d41984d20cfe448db144791b8d8424d41441d200f9424a71441d200f9444a7198511bcfe360db1441d1b8d8424a71984d1bcfe448db144791b8d8424d414479200f9444d41441d200f9444a71441d200f9444a7)))) else (if i < 1536 then (if i < 1280 then (if i < 1152 then (if i < 1088 then 0x20066144f43a0ec1441d200f9424a71441d1b8d8424a71984d20ccd448db20062144f435c8f144791b8d8424d41441d1b8d8424a7144791b8d8424d41441d1b90c424a7144791b8d8424d41441d200d8444a71441d1b8d8424a71e4511b909360d4198511bcfe360db1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71441d200f9444a71441d1b8d8424a71441d200f9444a7198511bcfe448db1441d1b8d8424a714479200f9424d4198511bcfe448db144661b8ec3f8b41984d1bcfe448db144791b8d8424d4144791b8d8424d41441d1b8d8424a71984d1bcfe448db1441d200f9424a71441d1b8d8424a71441d1b8d8424a718880144e83d08f18880144e83d08f20066144f435cec2244d1bcfe384db1441d1b8d8424a71e4511b909448d41441d1b8d8424a7144791b8d8424d4198511bcfe448db1441d1b8d8424a71984d1bcfe360db198511bcfe360db1984d1bcfe448db1441d1b8d8248d41441d1b8d8424a7144791b8d8424d4144791b8d8424d41441d1b8d8424a71e44d1b909448d41441d1b8d8424a7144791b8d8424d41441d1b8d8424a71441d1b8d8424a71441d1b8d8424a7084511b909448d4074511b909448a714479200f9424d41441d1b8d8424a71984d20ccd448db1984d20cfe448db1441d1b8d8424a7 else 0x1441d1b8d8424a7000000000000000144791b8d8424d41984d20cfe448db18880144d73d08f000000000000000000000000000000144791b8d8424d4074511b9093e4a71441d200f9444a7144791b8d8424d41441d1b8d8444a718880144d73d08f144791b8d8424d41441d1b8d8424a718880144e83d08f07451201093e4a71441d1b8d8424a71441d1b8d8424a71e4511b909448d41984d1bcfe448db1e4511b909448d4144791b8d8424d41441d1b8d8424a7134791b8d8424d41984d1bcfe448db1984d1bcfe448db18880144e83d08f1e4511b909448d41984d1bcfe448db144791b8d8424d419880144d73d0ec144791b8d8424d41e4511b909360d41441d1b8d8424a7144791b8d8424d4144791b8d8424d41e4511b909360d4144791b8d8424d4198511bc9b360db1441d1b8d8425101441d200f9444a71984d190a9448db1984d20ccd448db1984d1bccd448db1984d218f4380db1441d200f9424a7144791b8d8424d41441d1b8d8424a71441d200d8444a71984d1bcfe3e4db144791b8d8424d41984d20ccd448db144791b8f9424d41441d1b8d8424a71984d20cfe448db1441d200f9444a71441d1b8d8424a7198511bcfe448db1984d20cfe448db1441d1b8d8424a7144791b8d8248d41441d200f9424a7) else (if i < 1216 then 0x7451201093e4a70000000000000001441d200f9424a71441d200f9444a70000000000000001984d1bcfe448db144791b8d8424d40f8641b8d8425101984d1bcfe448db07451201093e4a7144661bcd83f8e01984d210f4448db1984d208f4448db198801450f3d0ec1441d200f9444a72244d1bcfe3e4db18880144e83d08f074511b909360a700000000000000018880144e83d08f19880144d73d0ec0000000000000001441d1b8d8424a719880144e83d0ec1441d1b8d8424a700000000000000019880144e83d0ec1441d200d8444a70000000000000001441d1b8d8424a71441d1b8d8424a7000000000000000134791b8d8424d4198511bcfe360db144791b8d8424d4074511b909360a71441d1b8d8424a7144791b8d8424d41441d1b90c424a70000000000000000000000000000001441d200f9444a70000000000000001441d1b8d8424a7198511bc9b448db098641b8d8425101441d200f9444a7198511bcfe360e014479200f9444d41e4511b892448d4144791b8d8424d41984d1bcfe448db198511bcfe448db1984d20cfe448db1441d200f9424a71441d1b8d8424a71984d210f4448db1441d200f9444a71981f14cdf380ee000000000000000198511bcfe448db144791b8d8424d41441d1b8d8248a71984d218cd380db else 0x1441d200f9444a71441d1b8d8424a70000000000000001441d200f9444a71e4511b909448d41441d200f9444a71441d1b8d8424a70000000000000000000000000000001441d1b8d8424a70000000000000001984d1bcfe360db000000000000000144791b8d8424d41984d20ccd448db144791b8d8424d4144791b8d8248d41441d1b8d8424a7198511bcfe360e018880144e83d08f0000000000000001441d1b8d8424a7198511bcfe448db000000000000000144791b8d8424d4144791b8d8424d40000000000000000000000000000000000000000000001441d200f9424a70000000000000001441d1b8d8424a71441d200f9444a71441d1b8d8424d4000000000000000198511bcfe448db1984d1bcfe448db14479200f9424d41984d1bcfe3b8db1441d1b8d8424a714479200f9444d41984d1bcfe448db14479200f9444d40000000000000000000000000000001441d1b8d8424a7144791b8d84251018880144d73d08f1984d1bcfe448db19880208ff37ca300000000000000018880144e83d08f1984d190cd384db1984d15ccd448db1984d20ccd448db1441d1b8d8424a71441d1b8d8424a71441d1b8d8444a71984d1bcfe448db144791b8d8424d41441d200f9444a71984d20cfe448db1441d1b8d8424a71441d1b8d8424a7)) else (if i < 1408 then (if i < 1344 then 0x1441d200f9444a71441d1b90c424a719880144e83d0ec1441d1b8d8444a71984d1bcfe448db0000000000000000000000000000000000000000000001441d1b8d8424a71441d2010c444a7074511b909448a70000000000000000000000000000000000000000000000000000000000001441d1b8d8424a7144791b8d8424d4144791b8d8424d4144791b8d8248d4144791b8d8424d4074511b9093e4a70000000000000001984d20ccd448db1441d1b8d8424a70000000000000001984d1bcfe448db0000000000000001984d1bcfe448db144791b8d8424d4144791b8d8424d41441d200f928ca71441d200f9424a714479200f9424d414479200f9444d41441d200f9444a7144791b8d8424d41984d190cd384db1441d1b8d8424a7144791b8d8424d41441d1b8d8424a7144791b8d8424d40000000000000001984d1bcfe3e4db0000000000000001441d1b8d8424a71441d200f9424a71886f144e83d08f1984d20cfe448db14479200f9424d41b866208df3fca31441d1b8d8424a71984d220cd448db144791b8d8424d41984d20cfe448db1e4511b909360d4000000000000000144791b8d8424d4144532010d44cb41bc6e14513440f91441d1b8d8444a71441d1b8d8424a714479200f9424d4 else 0x19880144d73d0ec1984d190a9384db1441d200f9424a70000000000000001441d1b8d8424a70000000000000001441d1b8d8424a7144791b8d8424a71441d1b8d8424a7144791b8d8424d40000000000000001441d1b8d8424a71441d200f9424d41441d1b90c424d40000000000000001886320cd34491318880144e83d08f1441d1b8d8424a71441d200f9444a70000000000000001441d1b8d8424a71984d20cfe448db188791bcfe3e513144791b8d8424d418880144d73d08f144791b8d8424d41441d200f9424a7000000000000000144791b8d8424d41984d1bcfe448db144791b8d8424d41984d1bcfe448db1441d200f9444a71441d1b8d8424a7000000000000000198511bcfe448db1441d1b8d8248a71e4511b909448d41984d1bcfe448db1441d200f9444a71984d208f4448db00000000000000020062144f43a08f0000000000000001441d1b8d8424a71984d1bcfe448db13479200f9444d4144791b8d8424d40000000000000001441d1b8d8424a7144791b8d8424d4144791b8d8424d4198511bcfe448db0000000000000001984d1bcfe448db1441d1b8f9424a71984d20cfe448db00000000000000000000000000000014479200d8444d41441d1b8d8424a70000000000000001441d200f9444a7000000000000000) else (if i < 1472 then 0x144791b8d8424d40000000000000001984d1bcfe448db1441a1b8d8424a7074511b909360a7144791b8d8424d4144791b8d8424d41e4511b909448d41984d1bcfe448db1441d200f9444a71984d1bcfe448db1441d1b8d8424a71984d208f4448db1441d1b8d8424a70000000000000001441d1b8d8424a71441d1b8d8424a7144791b8d8424d40000000000000001441d1b8d8424a71884d20cfe448db144791b8d8424d40000000000000000000000000000000000000000000001984d1bcfe448db1441d1b8d8424a70000000000000001441d1b8d8424a7000000000000000074511b909360a700000000000000019880144d73d0ec1984d218f4380db07451201113e4a71984d20ccd448db1441d200f9444a71441d1b8d8424a7198511bc9b360db1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71984d20ccd448db1441d1b8d8424a70000000000000000000000000000001884d20ccd448db19880144d73d0ec1984d1bcfe448db1886320cfe449131441d1b8f9424a71984d20cfe448db1441d1b8d8424a71441d1b8d8424a70000000000000001441d200f9444a71e4511b909360d4144791b8d8424d4144791b8d8424d420066144cd35cec14479200f9424d41e4511b909360d41441d1b8d8424a714479200f9444d4 else 0x1441d200f9444a7144791b8d8424d41984d1bcfe3e4db144791b8d8424d41441d1b8d8424a71984d1bcfe448db1984d20cfe448db1984d1bccd448db144532010d44cb41441d200f9444a71441d1b8d8424d41441d1b8d8424a7198511bcfe448db14479200f9444d41441d200f9444a71984d208f4448db1441d200f9444a7074511b909360a70000000000000001984d190cd384db144791b8d8424d41984d1bcfe448db1984d20cfe448db1441d1b8d8424a71441d1b8d8424a714479200f9444d41e4511b909448d41984d190a9384db1441d200d8424a719880144e83d0ec18880144d73d08f1e451201093e4d41e4511b909360d41441d200f9424a71984d1bcfe448db1441d1b8d8424a7134791b8d8424d41984d20ccd448db1984d1bcfe448db074511b909360a71e4511b909448d41441d200f9424a719880144d73d0ec1e4511b909360d414479200f9444d41fc6e15d0d37ca3144791b8d8424d41984d1bcfe360db18880144d73d08f1984d1bcfe448db1e451201093e4d41441d200f9424a7144791b90c424d41441d1b8d8424a71e4511b909360d41e4511b909360d41441d1b8d8424a7144791b8d8424d41441d1b8d8424a719880144e83d0ec144791b8d8424d41441d1b8d8424a71984d20ccd448db1441d1b8d8424a7))) else (if i < 1792 then (if i < 1664 then (if i < 1600 then 0x1984d1bcfe448db198511bcfe360db198511bcfe448db1441d1b8d8424a71984d20cfe448db1441d200f9424a718880144e83d08f1984d1bcfe3e4db1984d1bcfe448db1441d1b8d8424a71984d190a9384db1984d20ccd448db1e4511b909360d41441d1b8d8424a71884d1bcfe448db14479200f9424d4144791b8d8424d41441d1b8d8248a70000000000000001bc6e14513440f91441d200f9444a7074511b909360a71441d200f9444a71984d1bccd448db1441d1b8d8424a71441d200f9444a71441d1b8d8424a7144791b8d8424d41441d1b8d8424a70000000000000001441d200f9444a71441d200f9444a71441d200f9444a71441d1b8d8424a7144791b8d8424d4144791b8d8424d41984d1bcfe448db1984d190a9384db1441d1b8d8424a71984d20cfe448db1e4511b909360d414479200d8444d41441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71984d1bcfe449131984d20ccd448db1e4511b909448d4188801450f3d08f1984d20cfe448db1441d1b8d8424a7144791b8d8424d414479200f9444d41984d1bcfe448db1441d1b90c424a71441d1b8d8424a71441d200f9424a71441d1b8d8424a70000000000000000000000000000001441d1b8d8424a7144791b8d8424d41441d200f9444a71441d1b8d8424a7 else 0x74511b909360a718c8020d12334ed1441d1b8d8424d41984d208f4448db074511b909360a71441d1b8d8424d41e4511b909360d41441d1b8d8424a71441d1b8d8424a71441d200f9424a71e4511b909360d41441d1b8d8424a71984d208fe448db18880145113d08f1e4511b909448d41441d200f9444a7144791b8d8424d4144791b8d8424d41441d200f9444a71984d20cfe448db1441d1b8f9424a71984d1bcfe448db1e4511b909448d407451201093e4a71984d208f4448db074511b909360a7074511b909360a71441d200f9444a71984d20cfe448db0000000000000001441d200f9424a71441d1b8d8424a71984d1bcfe448db1441d1b8d8424a7144791b8d8424d4074511b892360a71441d1b8d8424a71441d200f9444a71441d1b8d8424a7144791b8d8424d41883a144e83d10e1441d1b8d8424a7198511bcfe360db198511bcfe448db144791b8d8424d41441d1b8d8424a71441d1b8d8424a7144791b8d8424d41441d200f9424a70000000000000001441d200f9444a71441d1b8d8424a7198511bcfe360db1441d200f9444a7134791b8d8424d418880144e83d08f1984d20ccd448db134791b8d8424d41984d1bcfe448db1e4511b909448d4144791b8d8424d418880144e83d08f1984d15cf4448db1441d200f928ca7) else (if i < 1728 then 0x1e4511b909360d41e4511b909360d4198511bcfe360e01441d1b8d8424a7144791b8d8424d41984d1bcfe448db14479200f9444d41984d1bcfe448db198511bcfe360db144791b8d8424d419880144d73d0ec1441d200f9444a70000000000000001e4511b911448d400000000000000000000000000000000000000000000019880144d73d0ec18880144d73d08f1884d1bcfe448db198511bcfe448db000000000000000144791b8d8424d41984d1bcfe3e4db14479200f9444d4198511bcfe360e01441d1b8d8424a71441d1b8d8424a7144791b8d8424d420066144f435cec1984d1bcfe448db144791b8d8448d4144791b8d8424d4134791b8d8424d4198511bcfe448db1984d1bcfe448db144791b8d8424d41441d1b8d8424a71984d1bcfe448db1984d1bcfe448db1441d1b8d8424a7144791b8d8424d41441d200f9444a71441d200f9444a71441d1b8d8424a71984d20cfe448db1441d1b8d8424a71441d1b8d8424a719880144e83d0ec1bc7f144f43a10d18880144e83d08f2244d1bcfe448db14479200f9424d407451201093e4a71441d200f9444a71441d200f9424a7144791b8d8424d41884d218f442d131441d200f9444a71984d1bcfe3e4db1984d1bcfe448db1441d200f9444a7144791b8d8424d4144791b8d8424d4 else 0x1e4511b909360d41441d1b8d8424a7144791b8d8424d41441d1b8d8444a7000000000000000144791b8d8424d40000000000000001441d1b8d8424a71441d200f9444a7144791b8d8424d414479200f9424d41984d1bccd448db1441d1b8d8424a70000000000000000000000000000001984d190cd384db18880144d73d08f1441d1b8d8424a70000000000000001984d220cd3e4db14479200f9444d41984d1bcfe360db1984d1bcfe360db1441d1b8d8424a71441d200f9444a714479200f9444d418880144e83d08f1441d1b8d8424a71441d1b8d8424a707451201093e4a71441d1b8d8424a70000000000000001441d1b8d8424a7000000000000000144791b8d8424d4000000000000000144791b8d8424d41441d1b8d8424a71441d200f9444d41e4511b909448d40000000000000001445320d0d3f8b414479200f9424d42181d200f9445101447d1b8d8424a718880144e83d08f1441d1b8d8424a71441d1b8d8424a71e4511b9093e4d4000000000000000144791b8f9424d41984d1bcfe3e4db074511b909360a700000000000000014479200f9424d41441d1b8d8448a71884d218f442d13144531b8ec340b41e4511b909360d41441d200f9444a71441d1b8d8424a71441d1b8d8424a71441d200f9424a7)) else (if i < 1920 then (if i < 1856 then 0x1984d1bcfe3e4db1441d1b8d8424a71441d1b8d8424a718880144e83d08f1984d1bcfe448db1441d200f9444a7144791b8d8424d41e4511b909360d41441d1b8d8424a71984d1bcfe448db00000000000000007451201113e4a714479200f9424d4144791b8d8424d41984d1bcfe448db144791b8d8424d41e4511b909448d41e4511b909448d414479200f9444d4144791b8d8424d41441d200f9444a70f864200f942510074511b9093e4a720066144f43a0ec1441d1b8d8424a71441d1b8d8424a7198511bcfe360e0144791b8d8424d4144791b8d8424d41441d1b8d8424a71441d1b8d8424a71984d1bcfe360db1984d1bcfe3e4db07451201093e4a71984d1bcfe448db1441d200f9424a7000000000000000000000000000000144791b8d8424d41441d200f9424a7144791b8d8424d4144791b8d8424d40000000000000001441d1b8d8424a71441d2010c444a7000000000000000144791b8d8444d41441d1b8d8424a71984d190a9384db198511bcfe360e01984d208f4448db144791b8d8424d40000000000000001441d200f9424a7000000000000000198511bcfe448db19880144d73d0ec074511b909360a7144791b8d8424d41984d208f4448db1984d190a9384db1984d1bcfe448db1441d1b8d8424a714479200f9444d4 else 0x1441d1b8d8424a7144791b8d8424d414479200f9444d4074511b909360a72181d200f944510074511b909360a718880144e83d08f1984d1bcfe448db1441d1b8d8424a7144791b8d8424d41984d1bcfe360db1441d1b8d8424a718880144d73d08f18880144d73d08f144791b8d8424d41441d200f9424a71887d1bcfe449131441d200f9444a7198511bcfe360e01e451201093e4d40000000000000001984d1bcfe448db14479200f9444d41441d1b8d8424a71e4511b909360d4144791b8d8424d4144791b8d8424d418887144d73d10e1441d1b8d8424a718880144d73d08f1441d1b8d8424a71441d1b8d8424a70000000000000001984d1bcfe448db1984d1bcfe3e4db1e4511b909448d40000000000000001984d1bcfe448db144791b8d8424d41441d200f9444a71441d1b8d8424a71e4511b909448d41984d1bcfe360db1e4511b909448d41984d1bcfe448db18880144e83d08f1984d1bcfe448db1441d200f9424d420062144f435c8f1441d1b8d8424a71984d1bcfe448db1441d200d8444a7198511bcfe448db14479200f9444d41984d1bcfe448db1441d200f9444a71441d1b8d8424d41441d1b8d8424a7198511bcfe448db198511bcfe448db144791b8d8424d41984d1bcfe448db1984d1bcfe448db1441d1b90c424a7) else (if i < 1984 then 0x1fc83144d73d10d18880145103d08f144791b8d8424d41984d1bcfe448db1441d1b8d8424a7144791b90c424d41984d1bcfe448db19880144d73d0ec1441d1b8d8424a70000000000000001984d1bcfe448db1441d200f9444a7074511b909360a7144791b8d8424d4144791b8d8424d4144791b8d8424d41e4511b909448d41984d1bcfe448db1441d1b8d8424a71884d218f442d13144791b8d8424d418887144e83d10e18880144e83d08f1984d1bcfe360db18880144d73d08f1984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71441d200f9444a71441d1b8d8424a71441d1b8d8424a7144791b8d8424d41441d1b8d8424a7000000000000000074511b909360a71441d1b8d8424a7198511bcfe360e020062144f43a08f1441d1b8d8424a714479200f928cd41441d1b8d8424a71441d200f9424a71441d1b8d8424a71e4511b909448d41984d1bcfe448db1984d1bcfe448db1441d200f9444a71441d1b8d8424a71441d200f9444a71e4511b909360d41441d1b8d8424a71441d200f9444a7144791b8d8424d4144791b8d8424d4144791b8d8424d41984d218f4388db144791b8d8424d400000000000000018880144d73d08f200851bcfe449131441d1b8d8424a7074511b909360a71e4511b909448d414479200f9444d4 else 0x1984d1bcfe448db0000000000000000000000000000001441d1b8d8424a70000000000000001441d1b8d8424a720066144f435cec1984d15cfe448db144791b8d8424d41441d1b90c424a71441d1b8d8424a7074511b909360a7000000000000000144791b8d8424d40000000000000001984d1bccd448db1984d15cfe448db1984d1bcfe448db1441a1b8d8424a71441d1b8d8424a71441d1b8d8424a71441d1b8d8424a7144791b8d8424d41441d1b8d8424a71441d1b8f9424a7144791b8d8424d41441d1b8d8424a7144791b8f9424d41e4511b909448d42181d200f9445101441d1b8d8424a7144791b8d8424d40000000000000001441d1b8d8424a7198511bcfe448db18880144e83d08f1441d1b8d8424a7144791b8d8424d4144791b8d8424d41441d200f9444a71441d1b8d8424a71984d1bcfe448db1984d1bcfe448db144791b8d8424d4198511bcfe448db1441d1b8d8444a71e4511b909360d41984d190a9384db14479200f9424d4000000000000000144791b8d8424d4144791b8d8424d41984d1bcfe448db1441d1b8d8424a71984d1bcfe448db074511b909448a7144791b90c424d4144791b8d8424d41986e208ff37ca31441d200f9424a7198511bcfe360db144791b8d8424d41984d1bcfe448db))))) else (if i < 3072 then (if i < 2560 then (if i < 2304 then (if i < 2176 then (if i < 2112 then 0x74511b909360a70000000000000001441d1b8d8424a717c6e15d0d37ca3000000000000000000000000000000144791b8d8424d41441d1b8d8424a70000000000000001984d1bcfe448db0000000000000001984d1bcfe448db1441d1b8d8424a70000000000000001984d1bcfe448db1984d1bcfe448db000000000000000144791b8d8424d41984d1bcfe448db1441d1b90c424a7144791b8d8424d4144791b8d8424d41984d1bcfe448db0000000000000001984d1bcfe448db0000000000000000000000000000001984d1bcfe448db19880144d73d0ec144791b8d8424d41984d1bcfe448db1984d218f4380db1441d1b8d8424a7214801bd123f8ed144791b8d8424d4144791b8d8444d41441d1b8d8424a700000000000000019880144d73d0ec000000000000000074641bd0d3f8e61984d1bccd448db00000000000000018880144e83d08f1441d1b8d8424a71986e190ff37ca31441d1b8d8424a70000000000000001441d1b8d8424a71984d1bcfe448db0000000000000000000000000000001441d1b8d8424a71984d1bcfe448db144791b8d8424d40000000000000001984d1bcfe448db1441d1b8d8424a70000000000000001441d1b8d8424a71441d1b8d8424a7 else 0x1984d1bcfe448db1441d1b8d8424a71984d1bcfe448db0000000000000001441d1b8d8424a71441d200f9424a720062144f435c8f000000000000000144791b8d8424d41441d1b8d8424a71441d1b8d8424a71984d1bcfe448db1441a1b8d8424a71441d1b8d8424a70000000000000001441d1b8d8424a71984d1bcfe448db144531b8ec340b40000000000000001441d1b8d8424a71441d1b8d8424a71984d1bcfe448db000000000000000198511bcfe360db1441d1b8d8424a70000000000000001984d1bcfe448db144532010d44cb41984d1bcfe448db1441d1b8d8424a7198511bcfe360db1984d1bcfe448db0000000000000000000000000000001441d1b8d8424a720066144f435cec1441d1b8d8424a71441d1b8d8424a7144791b8d8424d41441d200f9444a71441d1b8d8424a71984d1bcfe448db1984d1bcfe448db1984d1bcfe448db2244d1bcfe448db1441d1b8d8424a71441d1b90c424a71441d1b8d8424a700000000000000000000000000000018880144d73d08f1984d1bcfe448db1441d1b8d8424a70000000000000001441d1b8d8248a71441d1b8d8424a71441d1b8d8424a70000000000000001441d200f9424a70000000000000001441d1b8d8424a71984d1bcfe448db000000000000000000000000000000) else (if i < 2240 then 0x18880144d73d08f1441d1b8d8424a71981f14cdf380ee1441d1b8d8424a718880144d73d08f1441d1b8d8424a70000000000000001441d1b8d8424a70000000000000001441d1b8d8424a71984d1bcfe448db20066144f435cec0000000000000001984d1bcfe448db1984d1bcfe448db1441d1b8d8424a71441d1b90c424a71441d1b8d8424a71984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71441d1b8d8424a70000000000000001441d200f9424a70000000000000001984d1bcfe448db1984d20cfe448db1984d1bcfe448db0000000000000001984d1bcfe360db1441d1b8d8424a7144791b8d8424d40000000000000001441d200f928ca71441d1b8d8424a7144211b8d8424d41984d1bcfe448db20066144f435cec20062144f435c8f0000000000000001441d1b8d8424a71441d2010c424a71441d1b8d8424a71441d200f9424a70000000000000001984d1bcfe448db20062144f435c8f1441d1b8d8424a71441d1b8d8424a71984d218f442cdb1984d1bcfe448db1441d1b8d8424a71984d1bcfe448db1441d200f9424a71441d1b8d8424a707451201113e4a71441d1b8d8424a70000000000000001441d1b8d8424a71984d1bcfe448db000000000000000000000000000000 else 0x1984d1bcfe448db1441d1b90c424a71441d1b8d8424a71984d1bcfe448db1984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71984d1bcfe448db0000000000000001984d1bcfe448db198511bcfe360db0000000000000000000000000000001984d1bcfe448db18880144e83d08f18880144d73d08f1984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71984d1bc9b448db0000000000000001984d1bcfe448db1984d1bcfe448db1984d1bcfe448db1984d1bcfe448db1441d1b8d8424a71984d1bcfe448db1441d1b8d8424a720062144f435c8f1984d1bcfe448db1984d1bcfe360db1984d1bcfe448db144791b8d8424d41988015d0d37ca31441d1b8d8424a718880144e83d08f1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a720066144f435cec0000000000000001441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71441d1b8d8424a70000000000000001441d1b8d8424a70000000000000001441d1b8d8424a718880144d73d08f1441d1b8d8424a7144531b8ec340b41441d1b8f9424a71441d200f9424a71441d200d8424a71984d1bc9b360db0000000000000001441d1b8d8424a718880144e83d08f1984d1bcfe448db1441d1b8d8424a718880144d73d08f0000000000000001441d1b8d8424a7)) else (if i < 2432 then (if i < 2368 then 0x20062144f435c8f1441d1b8d8424a71441d1b8d8424a700000000000000018880144d73d08f1441d200f9424a71441d200f9424a71441d1b8d8424a71441d1b8d8424a7198511bcfe360db17c6e15d0d37ca31441d1b8d8424a71441d1b8d8424a71984d1bcfe448db1441d1b8d8424a718880144d73d08f1441d1b8d8424a7144791b8d8424d41984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71984d1bcfe448db0000000000000001441d200f9424a71441a1b8d8424a71441d200f9424a71441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71441d200f9424a718880144d73d08f1441d1b8d8424a71441d200f9424a71441d1b8d8424a70000000000000001441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71984d1bcfe448db1441d1b8d8424a7134791b8d8424a71441d1b8d8424a70000000000000001441d1b8d8424a70000000000000001441d1b8d8424a71441d1b8d8424a71441d200f9424a71441d1b8d8424a71441d1b8d8424a71984d1bcfe448db1441d1b8d8424a70000000000000001441d1b8d8444a720066144f435cec1984d1bcfe448db0000000000000001984d20cfe448db2244d1bcfe448db0000000000000000000000000000001984d1bcfe448db1441d1b8d8424a71441d1b8d8424a7 else 0x200851bcfe44913198511bcfe360db1441d200f9424a71441d1b8d8424a71984d1bcfe448db18880144d73d08f144791b8d8424d418880144e83d08f1441d1b8d8424a71984d1bcfe448db1984d1bcfe448db1441d1b8d8424a71441d1b8d8424a70000000000000001984d1bcfe448db18880144d73d08f1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71441d200f9424a71441d1b8d8424a71984d1bcfe448db1984d1bcfe448db0000000000000001441d1b8d8424a71984d1bcfe448db1984d190a9384db1441d200f9444a71441d200f9424a71984d1bcfe448db1984d1bccd448db1441d1b8f928ca71441d1b8d8424a71984d1bcfe448db1441d200f9444a71441d1b8d8424a71441d200f9424a71441d1b8d8424a70000000000000000000000000000000000000000000001441d1b8d8424a7144791b8d8424d4144791b8d8424d41441d1b8d8424a7000000000000000000000000000000144791b8f9424d41441d1b8d8424a71984d1bcfe448db144791b8d8248d41984d1bcfe448db0000000000000001441d1b8d8248a71984d218f4380db1984d1bcfe448db0000000000000001984d1bcfe448db1984d1bcfe448db1441d1b8d8424a70000000000000001441d1b8d8424a71984d1bcfe448db144791b8d8424d4) else (if i < 2496 then 0x1441d1b8d8424a717c6e15d0d37ca3144791b8d8424d41441d1b8d8424a70000000000000001441d1b8d8424a71984d218f4380db1441d1b8d8424a71984d1bcfe448db1984d1bcfe448db198511bcfe360db144791b8d8424d41984d1bcfe448db18880144d73d08f0000000000000001984d1bcfe448db1441d1b8d8424a71441d1b8d8424a717c4d1bcfe448db1441d1b8d8424a71441a1b8d8424a71984d218f4380db1441d200f9424a71984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a7000000000000000000000000000000144791b8d8424d41441d1b8d8424a7198511bcfe448db1441d1b8d8424a71984d1bcfe448db1441a1b8d8424a71441d1b8d8424a71441d1b8d8424a718880144d73d08f1441d1b8d8424a71441d1b8d8424a7144791b8d8424d41441d1b90c424a71441d1b8d8424a71441d1b8d8424a71884d218f4380db1441d1b8d8424a70000000000000001441d1b8d8424a71441d1b8d8424a71984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71984d1bcfe448db1441d1b8d8424a71441d1b8d8424a70000000000000001441d1b8d8424a71441d200f9424a718880144e83d08f1441d1b8d8424a71441d200f9424a71984d1bccd448db000000000000000144791b8d8424d4 else 0x1984d1bcfe448db0000000000000001441a200f9424a718880144e83d08f1984d1bccd448db1441d200f9424a71441d1b8d8424a71441d200f9444a71441d1b8d8424a70000000000000001441d1b8d8424a71441d1b8d8424a720062144f43a08f1441d1b8d8424a71441d1b8d8248a71441d200f9424a71984d1bccd448db1441d1b8d8424a718880144d73d08f1984d1bcfe448db1441d1b8d8424a71441d200f9444a70000000000000001984d1bcfe448db144791b8d8424d418880144e83d08f1441d1b8d8424a71984d15cf4448db1441d200f9424a71984d1bcfe448db1441d1b8d8424a70000000000000001441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71984d1bcfe448db1441d200f9424a707451201113e4a71441a1b8d8424a718880144d73d08f144791b8d8424d40000000000000001441d1b8d8424a71441d1b8d8424a71984d1bcfe448db1441d1b8d8424a70000000000000001984d1bcfe448db1984d1bcfe448db1441d200f9424a71441d1b8d8444a71441d1b8d8424a71441d1b8d8424a71441d1b8d8424a7144791b8d8424d41441d1b8d8424a70000000000000001441d1b8d8424a70000000000000001984d1bcfe3e4db144791b8d8424d40000000000000001441d1b8d8424a71441d1b8d8424a7))) else (if i < 2816 then (if i < 2688 then (if i < 2624 then 0x1441d1b8d8424a71984d1bcfe448db1984d15cfe448db1441d1b8d8424a719880144d73d0ec1984d1bcfe448db1984d1bcfe448db1441d1b8d8424a70000000000000000000000000000001984d1bcfe448db1441d1b8d8424a71441d1b8d8424a70000000000000001441d1b8d8424a71441d1b8d8424a707451201113e4a71441d1b8d8424a7000000000000000000000000000000144791b8d8424d41441d1b8d8424a70000000000000001441d200f9424a71441d1b8d8424a718880144e83d08f07451201113e4a71441d1b8d8424a71984d190a9384db1441d1b8d8424a71441d1b8d8424a707451201113e4a7144791b8d8424d419880144d73d0ec1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71984d1bcfe448db00000000000000000000000000000000000000000000018880144e83d08f1441d1b8d8424a719880144d73d0ec198511bcfe360db1441d1b8d8424a70000000000000001984d218f4380db1984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71984d1bcfe448db18880144d73d08f19880144d73d0ec074511b909360a71441d1b8d8424a720062144f435c8f18880144d73d08f1984d1bcfe448db198511bcfe448db1441d1b8d8424a71441d1b8d8424a71984d1bcfe448db else 0x1441d200f9424a71441d1b8d8424a70000000000000000000000000000000000000000000001441d1b8d8424a70000000000000001441d200f9424a71441d1b8d8424a71441d200f9424a71984d1bcfe448db0000000000000001984d1bcfe448db144791b8d8248d41984d1bcfe448db1441d200f9424a71441d1b8d8424a700000000000000020062144f435c8f1441d1b8d8424a7144791b8d8424d41441d1b8d8424a71441d200f9424a7198511bcfe360db1984d1bcfe448db000000000000000144791b90c424d41984d1bcfe448db1984d1bcfe448db0000000000000001441d1b8d8424a71441d200f9424a71441d1b8d8424a7144791b8d8424d41984d1bcfe448db0000000000000000000000000000001441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71984d1bcfe448db0000000000000000000000000000000000000000000001984d1bcfe448db0000000000000001441d1b8d8424a700000000000000020062144f435c8f1441d1b8d8424a71984d1bcfe448db1441d1b8d8424a700000000000000018880144d73d08f1441d1b8d8424a719880144d73d0ec1441d200f9424a71441d1b8d8424a70000000000000000000000000000001441d1b8d8424a718880144d73d08f1441d1b8d8424a7) else (if i < 2752 then 0x20062144f43a08f144791b8d8424d40000000000000001441d1b8d8424a71441d1b8f9424a71984d1bcfe448db1441d1b8d8424a71441d1b8d8424a70000000000000001984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71441d1b8d8248a7074511b909360a71441d1b8d8444a71441d1b8d8424a70000000000000000000000000000001984d20cfe448db144791b8d8424d41441d1b8d8424a71441d1b8d8424a720062144f43a08f1441d1b8d8424a7144791b8d8424d41441d1b8d8424a71441d200f9424a7144791b8d8424d41441d1b8d8424a71441d1b8f9424a71441d1b8d8424a71984d1bcfe360db0000000000000001441d1b8f9424a71441d1b8d8424a7144791b90c424d4144791b8d8248d41984d1bcfe360db1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a71984d1bcfe360db1441d1b8d8424a70000000000000001984d1bcfe448db0000000000000001984d1bccd448db18880144d73d08f1441d1b8d8424a70000000000000001984d218f4380db1441d1b8d8424a7144791b8d8424d41441d1b8d8424a70000000000000001984d1bcfe448db1984d1bcfe448db0000000000000001441d1b8d8424a7144532010d44cb41441d1b8d8424a70000000000000001441d1b8d8424a71441d1b90c424a7 else 0x1984d190a9384db00000000000000000000000000000018880144d73d08f000000000000000144791b8d8424d40000000000000001984d1bccd448db144791b8d8424d40000000000000000000000000000000000000000000001441d1b8d8424a71441d1b8d8424a71984d218f4380db1441d1b8d8424a707451201113e4a71984d1bcfe448db0000000000000000000000000000001441d1b8d8424a7144791b8d8424d41441d1b8d8424a71984d218f4380db144791b8d8424d41984d20ccd448db1441d1b8d8424a71984d1bcfe448db0000000000000001441d200f9424a7000000000000000000000000000000198511bcfe360db1441d1b8d8424a70000000000000000000000000000001441d1b8d8424a7000000000000000144791b8d8424d420062144f43a08f0000000000000000000000000000000000000000000001441d1b8d8424a7144791b8d8424d40000000000000001441d1b8d8424a70000000000000001441d1b90c424a71984d1bcfe448db1984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71984d1bcfe448db000000000000000000000000000000144791b8d8424d41441d1b8d8424a71441d1b8d8424a71984d1bcfe448db20066144f435cec20062144f43a08f1441d1b8d8248a7144661bcd83f8db)) else (if i < 2944 then (if i < 2880 then 0x1441d1b8d8424a7144791b8d8424d4144531b8ec340b4144791b8d8424d41441d1b8d8424a71984d1bcfe3e4db0000000000000001984d1bcfe448db1441d1b8d8424a71984d1bcfe360db1984d1bcfe448db0000000000000001984d1bcfe448db1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a70000000000000001984d15cf4448db1984d1bcfe448db18880144d73d08f1441d1b8d8424a71441d1b8d8424a71441d1b8d8424a7134791b8d8424d41441d1b8d8248a71984d1bcfe448db1984d218f4380db1441d1b90c424a70000000000000000000000000000001441d1b8d8424a71984d1bcfe448db144791b8d8424d41441d1b8d8424a71441d200f928ca70000000000000001984d1bcfe448db0000000000000000000000000000000000000000000000000000000000001441d1b8d8424a71441d1b8d8424a7144791b8d8424d41984d1bcfe448db1441d1b8d8424a70000000000000001984d1bcfe448db19880144d73d0ec0745120111430a71984d1bcfe448db0000000000000001441d200f9424a7198511bcfe360db else 0x0) else 0))) else 0))
  (tab >>> (60*(i % 64))) &&& 0xfffffffffffffff

def nb517 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 7
  | 5 => 66
  | 6 => 281
  | 7 => 612
  | 8 => 402
  | 9 => 26
  | 10 => 1
  | _ => 0

def ns517 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 12
  | 5 => 126
  | 6 => 585
  | 7 => 1294
  | 8 => 849
  | 9 => 52
  | 10 => 1
  | _ => 0

def bd517 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 11
  | 6 => 77
  | 7 => 358
  | 8 => 970
  | 9 => 1372
  | 10 => 1398
  | _ => 0

def bs517 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 16
  | 6 => 142
  | 7 => 727
  | 8 => 2021
  | 9 => 2870
  | 10 => 2922
  | _ => 0

def states517 (s i : Nat) := unpackWords wire517 10 9 (code517 (bs517 s+i))

def slot517 (s : Nat) (ws : List Nat) : Nat :=
  let h := hashWords ws
  (h / nb517 s + delta517 (bd517 s + h % nb517 s)) % ns517 s

end Live514

namespace Live514
def Z (s : Nat) := safe 138 states517 ns517 slot517 orient (fun s i => six517 (bs517 s+i)) s

theorem u0x0 : span (Z 0) 1 0 = true := by decide +kernel

theorem z0 : span (Z 0) 1 0 = true := u0x0

theorem u1x0 : span (Z 1) 1 0 = true := by decide +kernel

theorem z1 : span (Z 1) 1 0 = true := u1x0

theorem u2x0 : span (Z 2) 1 0 = true := by decide +kernel

theorem z2 : span (Z 2) 1 0 = true := u2x0

theorem u3x0 : span (Z 3) 1 0 = true := by decide +kernel

theorem z3 : span (Z 3) 1 0 = true := u3x0

theorem u4x0 : span (Z 4) 12 0 = true := by decide +kernel

theorem z4 : span (Z 4) 12 0 = true := u4x0

theorem u5x0 : span (Z 5) 40 0 = true := by decide +kernel

theorem u5x1 : span (Z 5) 40 40 = true := by decide +kernel

theorem u5x2 : span (Z 5) 40 80 = true := by decide +kernel

theorem u5x3 : span (Z 5) 6 120 = true := by decide +kernel

theorem z5 : span (Z 5) 126 0 = true := (@span_join (Z 5) 80 0 46 (@span_join (Z 5) 40 0 40 u5x0 u5x1) (@span_join (Z 5) 40 80 6 u5x2 u5x3))

theorem u6x0 : span (Z 6) 40 0 = true := by decide +kernel

theorem u6x1 : span (Z 6) 40 40 = true := by decide +kernel

theorem u6x2 : span (Z 6) 40 80 = true := by decide +kernel

theorem u6x3 : span (Z 6) 40 120 = true := by decide +kernel

theorem u6x4 : span (Z 6) 40 160 = true := by decide +kernel

theorem u6x5 : span (Z 6) 40 200 = true := by decide +kernel

theorem u6x6 : span (Z 6) 40 240 = true := by decide +kernel

theorem u6x7 : span (Z 6) 40 280 = true := by decide +kernel

theorem u6x8 : span (Z 6) 40 320 = true := by decide +kernel

theorem u6x9 : span (Z 6) 40 360 = true := by decide +kernel

theorem u6x10 : span (Z 6) 40 400 = true := by decide +kernel

theorem u6x11 : span (Z 6) 40 440 = true := by decide +kernel

theorem u6x12 : span (Z 6) 40 480 = true := by decide +kernel

theorem u6x13 : span (Z 6) 40 520 = true := by decide +kernel

theorem u6x14 : span (Z 6) 25 560 = true := by decide +kernel

theorem z6 : span (Z 6) 585 0 = true := (@span_join (Z 6) 320 0 265 (@span_join (Z 6) 160 0 160 (@span_join (Z 6) 80 0 80 (@span_join (Z 6) 40 0 40 u6x0 u6x1) (@span_join (Z 6) 40 80 40 u6x2 u6x3)) (@span_join (Z 6) 80 160 80 (@span_join (Z 6) 40 160 40 u6x4 u6x5) (@span_join (Z 6) 40 240 40 u6x6 u6x7))) (@span_join (Z 6) 160 320 105 (@span_join (Z 6) 80 320 80 (@span_join (Z 6) 40 320 40 u6x8 u6x9) (@span_join (Z 6) 40 400 40 u6x10 u6x11)) (@span_join (Z 6) 80 480 25 (@span_join (Z 6) 40 480 40 u6x12 u6x13) u6x14)))

theorem u7x0 : span (Z 7) 40 0 = true := by decide +kernel

theorem u7x1 : span (Z 7) 40 40 = true := by decide +kernel

theorem u7x2 : span (Z 7) 40 80 = true := by decide +kernel

theorem u7x3 : span (Z 7) 40 120 = true := by decide +kernel

theorem u7x4 : span (Z 7) 40 160 = true := by decide +kernel

theorem u7x5 : span (Z 7) 40 200 = true := by decide +kernel

theorem u7x6 : span (Z 7) 40 240 = true := by decide +kernel

theorem u7x7 : span (Z 7) 40 280 = true := by decide +kernel

theorem u7x8 : span (Z 7) 40 320 = true := by decide +kernel

theorem u7x9 : span (Z 7) 40 360 = true := by decide +kernel

theorem u7x10 : span (Z 7) 40 400 = true := by decide +kernel

theorem u7x11 : span (Z 7) 40 440 = true := by decide +kernel

theorem u7x12 : span (Z 7) 40 480 = true := by decide +kernel

theorem u7x13 : span (Z 7) 40 520 = true := by decide +kernel

theorem u7x14 : span (Z 7) 40 560 = true := by decide +kernel

theorem u7x15 : span (Z 7) 40 600 = true := by decide +kernel

theorem u7x16 : span (Z 7) 40 640 = true := by decide +kernel

theorem u7x17 : span (Z 7) 40 680 = true := by decide +kernel

theorem u7x18 : span (Z 7) 40 720 = true := by decide +kernel

theorem u7x19 : span (Z 7) 40 760 = true := by decide +kernel

theorem u7x20 : span (Z 7) 40 800 = true := by decide +kernel

theorem u7x21 : span (Z 7) 40 840 = true := by decide +kernel

theorem u7x22 : span (Z 7) 40 880 = true := by decide +kernel

theorem u7x23 : span (Z 7) 40 920 = true := by decide +kernel

theorem u7x24 : span (Z 7) 40 960 = true := by decide +kernel

theorem u7x25 : span (Z 7) 40 1000 = true := by decide +kernel

theorem u7x26 : span (Z 7) 40 1040 = true := by decide +kernel

theorem u7x27 : span (Z 7) 40 1080 = true := by decide +kernel

theorem u7x28 : span (Z 7) 40 1120 = true := by decide +kernel

theorem u7x29 : span (Z 7) 40 1160 = true := by decide +kernel

theorem u7x30 : span (Z 7) 40 1200 = true := by decide +kernel

theorem u7x31 : span (Z 7) 40 1240 = true := by decide +kernel

theorem u7x32 : span (Z 7) 14 1280 = true := by decide +kernel

theorem z7 : span (Z 7) 1294 0 = true := (@span_join (Z 7) 1280 0 14 (@span_join (Z 7) 640 0 640 (@span_join (Z 7) 320 0 320 (@span_join (Z 7) 160 0 160 (@span_join (Z 7) 80 0 80 (@span_join (Z 7) 40 0 40 u7x0 u7x1) (@span_join (Z 7) 40 80 40 u7x2 u7x3)) (@span_join (Z 7) 80 160 80 (@span_join (Z 7) 40 160 40 u7x4 u7x5) (@span_join (Z 7) 40 240 40 u7x6 u7x7))) (@span_join (Z 7) 160 320 160 (@span_join (Z 7) 80 320 80 (@span_join (Z 7) 40 320 40 u7x8 u7x9) (@span_join (Z 7) 40 400 40 u7x10 u7x11)) (@span_join (Z 7) 80 480 80 (@span_join (Z 7) 40 480 40 u7x12 u7x13) (@span_join (Z 7) 40 560 40 u7x14 u7x15)))) (@span_join (Z 7) 320 640 320 (@span_join (Z 7) 160 640 160 (@span_join (Z 7) 80 640 80 (@span_join (Z 7) 40 640 40 u7x16 u7x17) (@span_join (Z 7) 40 720 40 u7x18 u7x19)) (@span_join (Z 7) 80 800 80 (@span_join (Z 7) 40 800 40 u7x20 u7x21) (@span_join (Z 7) 40 880 40 u7x22 u7x23))) (@span_join (Z 7) 160 960 160 (@span_join (Z 7) 80 960 80 (@span_join (Z 7) 40 960 40 u7x24 u7x25) (@span_join (Z 7) 40 1040 40 u7x26 u7x27)) (@span_join (Z 7) 80 1120 80 (@span_join (Z 7) 40 1120 40 u7x28 u7x29) (@span_join (Z 7) 40 1200 40 u7x30 u7x31))))) u7x32)

theorem u8x0 : span (Z 8) 40 0 = true := by decide +kernel

theorem u8x1 : span (Z 8) 40 40 = true := by decide +kernel

theorem u8x2 : span (Z 8) 40 80 = true := by decide +kernel

theorem u8x3 : span (Z 8) 40 120 = true := by decide +kernel

theorem u8x4 : span (Z 8) 40 160 = true := by decide +kernel

theorem u8x5 : span (Z 8) 40 200 = true := by decide +kernel

theorem u8x6 : span (Z 8) 40 240 = true := by decide +kernel

theorem u8x7 : span (Z 8) 40 280 = true := by decide +kernel

theorem u8x8 : span (Z 8) 40 320 = true := by decide +kernel

theorem u8x9 : span (Z 8) 40 360 = true := by decide +kernel

theorem u8x10 : span (Z 8) 40 400 = true := by decide +kernel

theorem u8x11 : span (Z 8) 40 440 = true := by decide +kernel

theorem u8x12 : span (Z 8) 40 480 = true := by decide +kernel

theorem u8x13 : span (Z 8) 40 520 = true := by decide +kernel

theorem u8x14 : span (Z 8) 40 560 = true := by decide +kernel

theorem u8x15 : span (Z 8) 40 600 = true := by decide +kernel

theorem u8x16 : span (Z 8) 40 640 = true := by decide +kernel

theorem u8x17 : span (Z 8) 40 680 = true := by decide +kernel

theorem u8x18 : span (Z 8) 40 720 = true := by decide +kernel

theorem u8x19 : span (Z 8) 40 760 = true := by decide +kernel

theorem u8x20 : span (Z 8) 40 800 = true := by decide +kernel

theorem u8x21 : span (Z 8) 9 840 = true := by decide +kernel

theorem z8 : span (Z 8) 849 0 = true := (@span_join (Z 8) 640 0 209 (@span_join (Z 8) 320 0 320 (@span_join (Z 8) 160 0 160 (@span_join (Z 8) 80 0 80 (@span_join (Z 8) 40 0 40 u8x0 u8x1) (@span_join (Z 8) 40 80 40 u8x2 u8x3)) (@span_join (Z 8) 80 160 80 (@span_join (Z 8) 40 160 40 u8x4 u8x5) (@span_join (Z 8) 40 240 40 u8x6 u8x7))) (@span_join (Z 8) 160 320 160 (@span_join (Z 8) 80 320 80 (@span_join (Z 8) 40 320 40 u8x8 u8x9) (@span_join (Z 8) 40 400 40 u8x10 u8x11)) (@span_join (Z 8) 80 480 80 (@span_join (Z 8) 40 480 40 u8x12 u8x13) (@span_join (Z 8) 40 560 40 u8x14 u8x15)))) (@span_join (Z 8) 160 640 49 (@span_join (Z 8) 80 640 80 (@span_join (Z 8) 40 640 40 u8x16 u8x17) (@span_join (Z 8) 40 720 40 u8x18 u8x19)) (@span_join (Z 8) 40 800 9 u8x20 u8x21)))

theorem u9x0 : span (Z 9) 40 0 = true := by decide +kernel

theorem u9x1 : span (Z 9) 12 40 = true := by decide +kernel

theorem z9 : span (Z 9) 52 0 = true := (@span_join (Z 9) 40 0 12 u9x0 u9x1)

theorem u10x0 : span (Z 10) 1 0 = true := by decide +kernel

theorem z10 : span (Z 10) 1 0 = true := u10x0

theorem certified (s : Nat) (hs : s ≤ 10) : ∀ i < ns517 s, Z s i = true := by
  interval_cases s

  · exact fun i h => span_ok z0 i (Nat.zero_le i) h

  · exact fun i h => span_ok z1 i (Nat.zero_le i) h

  · exact fun i h => span_ok z2 i (Nat.zero_le i) h

  · exact fun i h => span_ok z3 i (Nat.zero_le i) h

  · exact fun i h => span_ok z4 i (Nat.zero_le i) h

  · exact fun i h => span_ok z5 i (Nat.zero_le i) h

  · exact fun i h => span_ok z6 i (Nat.zero_le i) h

  · exact fun i h => span_ok z7 i (Nat.zero_le i) h

  · exact fun i h => span_ok z8 i (Nat.zero_le i) h

  · exact fun i h => span_ok z9 i (Nat.zero_le i) h

  · exact fun i h => span_ok z10 i (Nat.zero_le i) h

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 138) (goal 138) s xs514) : False := by
  have h10 : NatRun (mask 138) (goal 138) 10 xs514 := extend_run h hs
  have p : xs514.Perm (states517 10 0) := by decide +kernel
  exact noRuns runOrient certified 10 (by decide) 0 (by decide) (Run.perm p h10)
end Live514

theorem PEqualNP.Outside.L_meta_514 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) s → 11 ≤ s := Live514.main514 Live514.noRunFull
