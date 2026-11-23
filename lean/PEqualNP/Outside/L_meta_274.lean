import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- Circuit normalization and live-wire lemmas are adapted from the project helpers and L-meta-611.

namespace PEqualNP.Outside.L_meta_274_aux.H

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

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.Outside.L_meta_274_aux.H

namespace PEqualNP.Outside.L_meta_274_aux.H

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

end PEqualNP.Outside.L_meta_274_aux.H

namespace PEqualNP.Outside.L_meta_274_aux.H

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

abbrev Stat : Type := Bool ⊕ Nat

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

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : Nat) : Stat)) ++ [Sum.inl b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : Nat) : Stat))).length = n := by simp
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
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
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
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_274_aux.H

namespace PEqualNP.Outside.L_meta_274_aux.H
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
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

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => (Sum.inr (i : Nat) : Stat))

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
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
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
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).val
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
        (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
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
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
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
  exact drop_core k pre g post hcl o (Sum.inl c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

end PEqualNP.Outside.L_meta_274_aux.H

namespace PEqualNP.Outside.L_meta_274_aux.H.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_274_aux.H
def Least (m : Nat) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : Nat) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o = f x) ∧
    (∀ (gs' : List Gate) (o' : Nat), CleanL m gs' →
      (∀ x : Fin m → Bool, vl gs' x o' = f x) → gs.length ≤ gs'.length)

theorem Least.hcl {m f gs o} (h : Least m f gs o) : CleanL m gs := h.1
theorem Least.hev {m f gs o} (h : Least m f gs o) : ∀ x : Fin m → Bool, vl gs x o = f x := h.2.1
theorem Least.hmin {m f gs o} (h : Least m f gs o) :
    ∀ (gs' : List Gate) (o' : Nat), CleanL m gs' →
      (∀ x : Fin m → Bool, vl gs' x o' = f x) → gs.length ≤ gs'.length := h.2.2

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

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

section scope6

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

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

end scope6
end PEqualNP.Outside.L_meta_274_aux.H.Readers

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_274_aux.H

namespace PEqualNP.Outside.L_meta_274_aux.R

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

section scope8
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (neg save : Bool)
    (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
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
end scope8

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
  obtain ⟨gs, o, L, hlen⟩ := Readers.exists_least n f s hnc h
  have hev : ∀ x, val gs n o x = f x := L.hev
  have ho : o < n + gs.length := by
    by_contra! hout
    obtain ⟨x, y, hn⟩ := hnc
    exact hn (by rw [← L.hev x, ← L.hev y, Readers.vl_beyond _ _ _ hout, Readers.vl_beyond _ _ _ hout])
  have hnd (p : ℕ) (hp : p < gs.length) : n+p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n+p ∈ g.inputs := by
    by_cases e : n+p = o
    · exact Or.inl e
    · obtain ⟨q, _, hg⟩ := L.live hnc p hp (Ne.symm e)
      exact Or.inr ⟨q, hg⟩
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
    exact run_live n gs o L.hcl ho hnd gs.length 0 (by omega)

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
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
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
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
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
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
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
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

end PEqualNP.Outside.L_meta_274_aux.R

namespace PEqualNP.Outside.L_meta_274_aux.R
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

end PEqualNP.Outside.L_meta_274_aux.R

namespace PEqualNP.Outside.L_meta_274_aux.R

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

end PEqualNP.Outside.L_meta_274_aux.R

namespace PEqualNP.Outside.L_meta_274_aux.R

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

end PEqualNP.Outside.L_meta_274_aux.R

namespace PEqualNP.Outside.L_meta_274_aux.R

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

end PEqualNP.Outside.L_meta_274_aux.R

namespace PEqualNP.Outside.L_meta_274_aux.R

def fG (x : Fin 4 → Bool) : Bool := decide (3 ≤ (List.ofFn x).count true)

def rowsG : List Nat := [3, 3, 5, 5, 6, 6, 9, 9, 10, 10, 12, 12, 7, 11, 7, 13, 7, 14, 11, 13, 11, 14, 13, 14]

def xsG : List Nat := [6156495, 12022579, 15457340, 16691136]

theorem rowsG_len : rowsG.length = 24 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 4) => (fun x : Fin 4 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 12 := by decide +kernel

theorem maskG : mask 12 = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; rfl

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 12 zs &&& lo 12) ≠ lo 12 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 6, ¬ NatRun (mask 12) (goal 12) s xsG) :
    ∀ s ≤ 6, ∀ zs : List Nat, zs.Sublist xsG → NatRun (mask 12) (goal 12) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 6, ¬ NatRun (mask 12) (goal 12) s xsG) :
    ∀ s : Nat, HasCircuitSize 4 fG s → 7 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run fG ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hr : NatRun (mask 12) (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 4 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' (by omega) _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def states : Nat → List (List Nat)
  | 0 => []
  | 1 => []
  | 2 => [[0x157003,0xebd03c,0xfeafc0],
      [0x157003,0xebdc3c,0xfea3c0],
      [0x49d00c,0xb77033,0xfeafc0],
      [0x49d00c,0xb77333,0xfeacc0],
      [0x5ca0c0,0xb77303,0xebdc3c],
      [0x5ca0c0,0xb77333,0xebdc0c],
      [0x5df00f,0xa35030,0xfeafc0],
      [0x5df0cf,0xa35030,0xfeaf00],
      [0x5df0c3,0xb62300,0xebdc3c],
      [0x5df0cf,0xb62300,0xebdc30],
      [0x5df0cc,0xb77333,0xea8c00],
      [0x5df0cf,0xb77330,0xea8c00],
      [0x49d00c,0xb77333,0xfeac00],
      [0x5df0cf,0xa35030,0xfeac00],
      [0x5ca0c0,0xb77333,0xebdc00],
      [0x5df0cf,0xb62300,0xebdc00],
      [0x157003,0xebd03c,0xfea3c0],
      [0x157003,0xebdc3c,0xfea300],
      [0x157003,0xebd030,0xfeafc0],
      [0x157003,0xebdc3c,0xfea0c0],
      [0x157003,0xebd00c,0xfeafc0],
      [0x5df0cf,0xa35030,0xfea300],
      [0x5ca0c0,0xb77300,0xebdc3c],
      [0x5df0cf,0xb77300,0xea8c00],
      [0x49d00c,0xb77033,0xfeacc0],
      [0x49d00c,0xb77030,0xfeafc0],
      [0x49d00c,0xb77333,0xfea0c0],
      [0x49d00c,0xb77003,0xfeafc0],
      [0x5df0cf,0xb62300,0xebd030],
      [0x5df0cf,0xb77030,0xea8c00],
      [0x5ca0c0,0xb77303,0xebdc0c],
      [0x5ca0c0,0xb77333,0xebd00c],
      [0x5ca0c0,0xb77003,0xebdc3c],
      [0x5df0c0,0xb62300,0xebdc3c],
      [0x5df0c0,0xb77333,0xea8c00],
      [0x5df00f,0xa35030,0xfeaf00],
      [0x5df00c,0xa35030,0xfeafc0],
      [0x5df003,0xa35030,0xfeafc0],
      [0x5df00c,0xb77333,0xea8c00],
      [0x5df0c3,0xb62300,0xebdc30],
      [0x5df003,0xb62300,0xebdc3c],
      [0x5df0cc,0xb77330,0xea8c00]]
  | 3 => [[0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x157003,0xebdc3c,0xfeafc0,0xfff3ff],
      [0x5df0cf,0xb77333,0xebd03c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfea3c0],
      [0x49d00c,0xb77333,0xfeafc0,0xfffcff],
      [0x5df0cf,0xb77033,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeacc0],
      [0x5ca0c0,0xb77333,0xebdc3c,0xffffcf],
      [0x5df0cf,0xb77303,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc0c,0xfeafc0],
      [0x5df0cf,0xa35030,0xfeafc0,0xffff3f],
      [0x5df00f,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeaf00],
      [0x5df0cf,0xb62300,0xebdc3c,0xfffff3],
      [0x5df0c3,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc30,0xfeafc0],
      [0x5df0cf,0xb77333,0xea8c00,0xfffffc],
      [0x5df0cc,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77330,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xffffc0],
      [0x49d00c,0xb77333,0xfeafc0,0xfffc3f],
      [0x5df0cf,0xa35030,0xfeafc0,0xfffc3f],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeac00],
      [0x5df0cf,0xb77333,0xfeafc0,0xfffc3c],
      [0x5ca0c0,0xb77333,0xebdc3c,0xffffc3],
      [0x5df0cf,0xb62300,0xebdc3c,0xffffc3],
      [0x5df0cf,0xb77333,0xebdc00,0xfeafc0],
      [0x157003,0xebd03c,0xfeafc0],
      [0x157003,0xebd03c,0xebdc3c,0xfeafc0],
      [0x157003,0xebd03c,0xfeafc0,0xfff3ff],
      [0x157003,0xebdc3c,0xfea3c0],
      [0x157003,0xebdc3c,0xfea3c0,0xfeafc0],
      [0x157003,0xebdc3c,0xfea3c0,0xfff3ff],
      [0x157003,0x5df0cf,0xebd03c,0xfeafc0],
      [0x157003,0x5df0cf,0xebdc3c,0xfea3c0],
      [0x157003,0xb77333,0xebd03c,0xfeafc0],
      [0x157003,0xb77333,0xebdc3c,0xfea3c0],
      [0x157003,0xebdc3c,0xfeafc0,0xfff33f],
      [0x157003,0x49d00c,0xa35030,0xfeafc0],
      [0x157003,0xebdc3c,0xfeafc0,0xfff3f3],
      [0x157003,0x5ca0c0,0xb62300,0xebdc3c],
      [0x157003,0xebdc3c,0xfeafc0,0xfff0ff],
      [0x157003,0xebdc3c,0xfeafc0,0xfff3cf],
      [0x5df0cf,0xb77333,0xebd03c,0xfea3c0],
      [0x5df0cf,0xa35030,0xfeafc0,0xfff33f],
      [0x5df0cf,0xb77333,0xebdc3c,0xfea300],
      [0x5df0cf,0xebdc3c,0xfeafc0,0xfff333],
      [0x5ca0c0,0xb77333,0xebdc3c,0xffffcc],
      [0x5df0cf,0xb77300,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xea8c00,0xffffcc],
      [0x49d00c,0xb77033,0xfeafc0],
      [0x49d00c,0xb77033,0xb77333,0xfeafc0],
      [0x49d00c,0xb77033,0xfeafc0,0xfffcff],
      [0x49d00c,0xb77333,0xfeacc0],
      [0x49d00c,0xb77333,0xfeacc0,0xfeafc0],
      [0x49d00c,0xb77333,0xfeacc0,0xfffcff],
      [0x49d00c,0x5df0cf,0xb77033,0xfeafc0],
      [0x49d00c,0x5df0cf,0xb77333,0xfeacc0],
      [0x49d00c,0xb77033,0xebdc3c,0xfeafc0],
      [0x49d00c,0xb77333,0xebdc3c,0xfeacc0],
      [0x49d00c,0xb77333,0xfeafc0,0xfffcfc],
      [0x49d00c,0x5ca0c0,0xb77333,0xea8c00],
      [0x49d00c,0xb77333,0xfeafc0,0xfff0ff],
      [0x49d00c,0xb77333,0xfeafc0,0xfffccf],
      [0x5df0cf,0xb77033,0xebdc3c,0xfeacc0],
      [0x5df0cf,0xb62300,0xebdc3c,0xfff3f3],
      [0x5df0cf,0xb77333,0xebd030,0xfeafc0],
      [0x5df0cf,0xb77030,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xea8c00,0xfffcfc],
      [0x5ca0c0,0xb77303,0xebdc3c],
      [0x5ca0c0,0xb77303,0xb77333,0xebdc3c],
      [0x5ca0c0,0xb77303,0xebdc3c,0xffffcf],
      [0x5ca0c0,0xb77333,0xebdc0c],
      [0x5ca0c0,0xb77333,0xebdc0c,0xebdc3c],
      [0x5ca0c0,0xb77333,0xebdc0c,0xffffcf],
      [0x5ca0c0,0x5df0cf,0xb77303,0xebdc3c],
      [0x5ca0c0,0x5df0cf,0xb77333,0xebdc0c],
      [0x5ca0c0,0xb77303,0xebdc3c,0xfeafc0],
      [0x5ca0c0,0xb77333,0xebdc0c,0xfeafc0],
      [0x5ca0c0,0xb77333,0xebdc3c,0xfff3cf],
      [0x5ca0c0,0xb77333,0xebdc3c,0xfffccf],
      [0x5df0cf,0xb77303,0xebdc0c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfea0c0],
      [0xb77333,0xebdc3c,0xfeafc0,0xfff0cf],
      [0x5df0c0,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb62300,0xebdc3c,0xfffff0],
      [0x5df0cf,0xb77333,0xea8c00,0xfffff0],
      [0x5df00f,0xa35030,0xfeafc0],
      [0x5df00f,0x5df0cf,0xa35030,0xfeafc0],
      [0x5df00f,0xa35030,0xfeafc0,0xffff3f],
      [0x5df0cf,0xa35030,0xfeaf00],
      [0x5df0cf,0xa35030,0xfeaf00,0xfeafc0],
      [0x5df0cf,0xa35030,0xfeaf00,0xffff3f],
      [0x5df00f,0xa35030,0xb77333,0xfeafc0],
      [0x5df0cf,0xa35030,0xb77333,0xfeaf00],
      [0x5df00f,0xa35030,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xa35030,0xebdc3c,0xfeaf00],
      [0x5df0cf,0xa35030,0xfeafc0,0xffff3c],
      [0x5df0cf,0xa35030,0xb62300,0xea8c00],
      [0x5df0cf,0xa35030,0xfeafc0,0xffff33],
      [0x5df00f,0xb77333,0xebdc3c,0xfeaf00],
      [0x5df0cf,0xb77333,0xebd00c,0xfeafc0],
      [0x5df00c,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xea8c00,0xffff3c],
      [0x5df0c3,0xb62300,0xebdc3c],
      [0x5df0c3,0x5df0cf,0xb62300,0xebdc3c],
      [0x5df0c3,0xb62300,0xebdc3c,0xfffff3],
      [0x5df0cf,0xb62300,0xebdc30],
      [0x5df0cf,0xb62300,0xebdc30,0xebdc3c],
      [0x5df0cf,0xb62300,0xebdc30,0xfffff3],
      [0x5df0c3,0xb62300,0xb77333,0xebdc3c],
      [0x5df0cf,0xb62300,0xb77333,0xebdc30],
      [0x5df0c3,0xb62300,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb62300,0xebdc30,0xfeafc0],
      [0x5df0cf,0xb62300,0xebdc3c,0xffff33],
      [0x5df0c3,0xb77333,0xebdc30,0xfeafc0],
      [0x5df0cf,0xb77003,0xebdc3c,0xfeafc0],
      [0x5df003,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cc,0xb77333,0xea8c00],
      [0x5df0cc,0x5df0cf,0xb77333,0xea8c00],
      [0x5df0cc,0xb77333,0xea8c00,0xfffffc],
      [0x5df0cf,0xb77330,0xea8c00],
      [0x5df0cf,0xb77330,0xb77333,0xea8c00],
      [0x5df0cf,0xb77330,0xea8c00,0xfffffc],
      [0x5df0cc,0xb77333,0xea8c00,0xebdc3c],
      [0x5df0cf,0xb77330,0xea8c00,0xebdc3c],
      [0x5df0cc,0xb77333,0xea8c00,0xfeafc0],
      [0x5df0cf,0xb77330,0xea8c00,0xfeafc0],
      [0x5df0cc,0xb77330,0xebdc3c,0xfeafc0]]
  | 4 => [[0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0xa20f30,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xa20f30,0xb77333,0xebdc3c,0xfeafc0],
      [0x157003,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfff3ff],
      [0x49d00c,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffcff],
      [0x5ca0c0,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xffffcf],
      [0x5df0cf,0xb77333,0xb77333,0xebdc3c,0xfeafc0],
      [0x488ccc,0x5df0cf,0xebdc3c,0xfeafc0],
      [0x488ccc,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xa35030,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xffff3f],
      [0x5df0cf,0xb62300,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffff3],
      [0x5df0cf,0xb77333,0xebdc3c,0xebdc3c,0xfeafc0],
      [0x1423c3,0x5df0cf,0xb77333,0xfeafc0],
      [0x1423c3,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xea8c00,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffffc],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfeafc0],
      [0x1503f,0x5df0cf,0xb77333,0xebdc3c],
      [0x1503f,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x488ccc,0xa20f30,0xebdc3c,0xfeafc0],
      [0x1423c3,0xa20f30,0xb77333,0xfeafc0],
      [0x1503f,0xa20f30,0xb77333,0xebdc3c],
      [0x0,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xffffff],
      [0x5df0cf,0xa20330,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xb77f33,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xa20c30,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xebdf3c,0xfeafc0],
      [0x5df0cf,0xa20f00,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfeaff0],
      [0x5df0cf,0xb77333,0xea8ffc,0xebdc3c,0xfeafc0],
      [0x15000,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffc3f],
      [0x142000,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xffffc3],
      [0x157003,0xebdc3c,0xfeafc0,0xfff3ff],
      [0x157003,0x5df0cf,0xebdc3c,0xfeafc0,0xfff3ff],
      [0x157003,0xb77333,0xebdc3c,0xfeafc0,0xfff3ff],
      [0x157003,0x49d00c,0xb77333,0xebdc3c,0xfeafc0],
      [0x157003,0x5ca0c0,0xb77333,0xebdc3c,0xfeafc0],
      [0x157003,0x5df0cf,0xa35030,0xebdc3c,0xfeafc0],
      [0x157003,0x5df0cf,0xb62300,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebd03c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebd03c,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebd03c,0xfeafc0,0xfff3ff],
      [0x5df0cf,0xb77333,0xebdc3c,0xfea3c0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfea3c0,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfea3c0,0xfff3ff],
      [0xc00,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb62ff3,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfff33f],
      [0x488000,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xffffcc],
      [0x49d00c,0xb77333,0xfeafc0,0xfffcff],
      [0x49d00c,0x5df0cf,0xb77333,0xfeafc0,0xfffcff],
      [0x49d00c,0xb77333,0xebdc3c,0xfeafc0,0xfffcff],
      [0x49d00c,0x5ca0c0,0xb77333,0xebdc3c,0xfeafc0],
      [0x49d00c,0x5df0cf,0xa35030,0xb77333,0xfeafc0],
      [0x49d00c,0x5df0cf,0xb77333,0xea8c00,0xfeafc0],
      [0x5df0cf,0xb77033,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77033,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77033,0xebdc3c,0xfeafc0,0xfffcff],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeacc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeacc0,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeacc0,0xfffcff],
      [0x300,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xa35f3f,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfff3f3],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffcfc],
      [0x5ca0c0,0xb77333,0xebdc3c,0xffffcf],
      [0x5ca0c0,0x5df0cf,0xb77333,0xebdc3c,0xffffcf],
      [0x5ca0c0,0xb77333,0xebdc3c,0xfeafc0,0xffffcf],
      [0x5ca0c0,0x5df0cf,0xb62300,0xb77333,0xebdc3c],
      [0x5ca0c0,0x5df0cf,0xb77333,0xea8c00,0xebdc3c],
      [0x5df0cf,0xb77303,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77303,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77303,0xebdc3c,0xfeafc0,0xffffcf],
      [0x5df0cf,0xb77333,0xebdc0c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc0c,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc0c,0xfeafc0,0xffffcf],
      [0x30,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x1423c3,0x488ccc,0x5df0cf,0xfeafc0],
      [0x1503f,0x488ccc,0x5df0cf,0xebdc3c],
      [0x4880cc,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0x5dfccf,0xb77333,0xebdc3c,0xfeafc0],
      [0x488c0c,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xebdcfc,0xfeafc0],
      [0x488cc0,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfeafcc],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfff0ff],
      [0x5cafcf,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xa20000,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffff0],
      [0x5df0cf,0xa35030,0xfeafc0,0xffff3f],
      [0x5df0cf,0xa35030,0xb77333,0xfeafc0,0xffff3f],
      [0x5df0cf,0xa35030,0xebdc3c,0xfeafc0,0xffff3f],
      [0x5df0cf,0xa35030,0xb62300,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xa35030,0xb77333,0xea8c00,0xfeafc0],
      [0x5df00f,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df00f,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df00f,0xb77333,0xebdc3c,0xfeafc0,0xffff3f],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeaf00],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeaf00,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeaf00,0xffff3f],
      [0xc0,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfff3cf],
      [0x49dcff,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xffff3c],
      [0x5df0cf,0xb62300,0xebdc3c,0xfffff3],
      [0x5df0cf,0xb62300,0xb77333,0xebdc3c,0xfffff3],
      [0x5df0cf,0xb62300,0xebdc3c,0xfeafc0,0xfffff3],
      [0x5df0cf,0xb62300,0xb77333,0xea8c00,0xebdc3c],
      [0x5df0c3,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0c3,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0c3,0xb77333,0xebdc3c,0xfeafc0,0xfffff3],
      [0x5df0cf,0xb77333,0xebdc30,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc30,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc30,0xfeafc0,0xfffff3],
      [0xc,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x1503f,0x1423c3,0x5df0cf,0xb77333],
      [0x1420c3,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0x5df3cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x142303,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xb773f3,0xebdc3c,0xfeafc0],
      [0x1423c0,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfeafc3],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffccf],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xffff33],
      [0x1573ff,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xea8c00,0xfffffc],
      [0x5df0cf,0xb77333,0xea8c00,0xebdc3c,0xfffffc],
      [0x5df0cf,0xb77333,0xea8c00,0xfeafc0,0xfffffc],
      [0x5df0cc,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cc,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cc,0xb77333,0xebdc3c,0xfeafc0,0xfffffc],
      [0x5df0cf,0xb77330,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77330,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77330,0xebdc3c,0xfeafc0,0xfffffc],
      [0x3,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x1500f,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0x5df0ff,0xb77333,0xebdc3c,0xfeafc0],
      [0x15033,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xb7733f,0xebdc3c,0xfeafc0],
      [0x1503c,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xebdc3f,0xfeafc0]]
  | 5 => [[0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0xa20f30,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xa20f30,0xb77333,0xebdc3c,0xfeafc0],
      [0x157003,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfff3ff],
      [0x49d00c,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffcff],
      [0x5ca0c0,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xffffcf],
      [0x5df0cf,0xb77333,0xb77333,0xebdc3c,0xfeafc0],
      [0x488ccc,0x5df0cf,0xebdc3c,0xfeafc0],
      [0x488ccc,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xa35030,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xffff3f],
      [0x5df0cf,0xb62300,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffff3],
      [0x5df0cf,0xb77333,0xebdc3c,0xebdc3c,0xfeafc0],
      [0x1423c3,0x5df0cf,0xb77333,0xfeafc0],
      [0x1423c3,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xea8c00,0xebdc3c,0xfeafc0],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfffffc],
      [0x5df0cf,0xb77333,0xebdc3c,0xfeafc0,0xfeafc0],
      [0x1503f,0x5df0cf,0xb77333,0xebdc3c],
      [0x1503f,0x5df0cf,0xb77333,0xebdc3c,0xfeafc0]]
  | 6 => [[0x5df0cf,0xb77333,0xebdc3c,0xfeafc0]]
  | _ => []

def N (s : Nat) : Nat := (states s).length
def S (s i : Nat) : List Nat := (states s).getD i []
def found (s : Nat) (zs : List Nat) : Bool := (states s).any fun ys => zs.isPerm ys

theorem found_sound {s zs} (h : found s zs = true) :
    ∃ i < N s, zs.Perm (S s i) := by
  obtain ⟨ys, hym, hp⟩ := List.any_eq_true.1 h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hym
  obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.1 hi
  refine ⟨i, hb, ?_⟩
  have e : S s i = ys := by
    rw [S, List.getD_eq_getElem _ _ hb, he]
  rw [e]
  exact List.isPerm_iff.1 hp

def bar : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal 12])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask 12) (s + 2 - ws.length) ws fun _ zs =>
        covers 12 s zs && !(found s zs))

set_option maxRecDepth 10000 in
theorem bar_all (hc : ∀ s ≤ 6, ∀ i < N s, bar s i = true) :
    ∀ s ≤ 6, ∀ i < N s, ¬ NatRun (mask 12) (goal 12) s (S s i) := by
  intro s
  induction s with
  | zero =>
    intro hs i hi h
    have hb := hc 0 hs i hi
    simp [bar, zero_done h rfl] at hb
  | succ s ih =>
    intro hs i hi h
    have hb := hc (s+1) hs i hi
    let F (_ : Nat) (zs : List Nat) := covers 12 s zs && !(found s zs)
    have hF (tag : Nat) (zs) (hz : NatRun (mask 12) (goal 12) s zs) : F tag zs = true := by
      have hn : found s zs = false := by
        cases he : found s zs with
        | false => rfl
        | true =>
          obtain ⟨j, hj, hp⟩ := found_sound he
          exact False.elim (ih (by omega) j hj (Run.perm hp hz))
      simp only [F, covers_ok hz, hn, Bool.not_false, Bool.and_self]
    have hn := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hn] at hb
    contradiction

theorem checked_0 : ∀ i < N 0, bar 0 i = true := by
  intro i hi
  simp [N, states] at hi

theorem checked_1 : ∀ i < N 1, bar 1 i = true := by
  intro i hi
  simp [N, states] at hi

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_0 : bar 2 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_1 : bar 2 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_2 : bar 2 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_3 : bar 2 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_4 : bar 2 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_5 : bar 2 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_6 : bar 2 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_7 : bar 2 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_8 : bar 2 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_9 : bar 2 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_10 : bar 2 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_11 : bar 2 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_12 : bar 2 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_13 : bar 2 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_14 : bar 2 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_15 : bar 2 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_16 : bar 2 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_17 : bar 2 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_18 : bar 2 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_19 : bar 2 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_20 : bar 2 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_21 : bar 2 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_22 : bar 2 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_23 : bar 2 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_24 : bar 2 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_25 : bar 2 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_26 : bar 2 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_27 : bar 2 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_28 : bar 2 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_29 : bar 2 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_30 : bar 2 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_31 : bar 2 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_32 : bar 2 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_33 : bar 2 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_34 : bar 2 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_35 : bar 2 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_36 : bar 2 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_37 : bar 2 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_38 : bar 2 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_39 : bar 2 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_40 : bar 2 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_2_41 : bar 2 41 = true := by decide +kernel

theorem checked_2 : ∀ i < N 2, bar 2 i = true := by
  intro i hi
  have hi' : i < 42 := by simpa only [N, states, List.length_cons, List.length_nil] using hi
  interval_cases i
  · exact check_2_0
  · exact check_2_1
  · exact check_2_2
  · exact check_2_3
  · exact check_2_4
  · exact check_2_5
  · exact check_2_6
  · exact check_2_7
  · exact check_2_8
  · exact check_2_9
  · exact check_2_10
  · exact check_2_11
  · exact check_2_12
  · exact check_2_13
  · exact check_2_14
  · exact check_2_15
  · exact check_2_16
  · exact check_2_17
  · exact check_2_18
  · exact check_2_19
  · exact check_2_20
  · exact check_2_21
  · exact check_2_22
  · exact check_2_23
  · exact check_2_24
  · exact check_2_25
  · exact check_2_26
  · exact check_2_27
  · exact check_2_28
  · exact check_2_29
  · exact check_2_30
  · exact check_2_31
  · exact check_2_32
  · exact check_2_33
  · exact check_2_34
  · exact check_2_35
  · exact check_2_36
  · exact check_2_37
  · exact check_2_38
  · exact check_2_39
  · exact check_2_40
  · exact check_2_41

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_0 : bar 3 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_1 : bar 3 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_2 : bar 3 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_3 : bar 3 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_4 : bar 3 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_5 : bar 3 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_6 : bar 3 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_7 : bar 3 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_8 : bar 3 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_9 : bar 3 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_10 : bar 3 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_11 : bar 3 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_12 : bar 3 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_13 : bar 3 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_14 : bar 3 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_15 : bar 3 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_16 : bar 3 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_17 : bar 3 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_18 : bar 3 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_19 : bar 3 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_20 : bar 3 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_21 : bar 3 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_22 : bar 3 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_23 : bar 3 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_24 : bar 3 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_25 : bar 3 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_26 : bar 3 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_27 : bar 3 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_28 : bar 3 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_29 : bar 3 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_30 : bar 3 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_31 : bar 3 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_32 : bar 3 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_33 : bar 3 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_34 : bar 3 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_35 : bar 3 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_36 : bar 3 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_37 : bar 3 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_38 : bar 3 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_39 : bar 3 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_40 : bar 3 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_41 : bar 3 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_42 : bar 3 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_43 : bar 3 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_44 : bar 3 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_45 : bar 3 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_46 : bar 3 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_47 : bar 3 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_48 : bar 3 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_49 : bar 3 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_50 : bar 3 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_51 : bar 3 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_52 : bar 3 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_53 : bar 3 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_54 : bar 3 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_55 : bar 3 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_56 : bar 3 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_57 : bar 3 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_58 : bar 3 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_59 : bar 3 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_60 : bar 3 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_61 : bar 3 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_62 : bar 3 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_63 : bar 3 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_64 : bar 3 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_65 : bar 3 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_66 : bar 3 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_67 : bar 3 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_68 : bar 3 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_69 : bar 3 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_70 : bar 3 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_71 : bar 3 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_72 : bar 3 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_73 : bar 3 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_74 : bar 3 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_75 : bar 3 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_76 : bar 3 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_77 : bar 3 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_78 : bar 3 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_79 : bar 3 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_80 : bar 3 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_81 : bar 3 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_82 : bar 3 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_83 : bar 3 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_84 : bar 3 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_85 : bar 3 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_86 : bar 3 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_87 : bar 3 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_88 : bar 3 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_89 : bar 3 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_90 : bar 3 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_91 : bar 3 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_92 : bar 3 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_93 : bar 3 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_94 : bar 3 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_95 : bar 3 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_96 : bar 3 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_97 : bar 3 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_98 : bar 3 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_99 : bar 3 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_100 : bar 3 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_101 : bar 3 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_102 : bar 3 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_103 : bar 3 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_104 : bar 3 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_105 : bar 3 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_106 : bar 3 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_107 : bar 3 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_108 : bar 3 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_109 : bar 3 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_110 : bar 3 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_111 : bar 3 111 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_112 : bar 3 112 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_113 : bar 3 113 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_114 : bar 3 114 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_115 : bar 3 115 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_116 : bar 3 116 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_117 : bar 3 117 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_118 : bar 3 118 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_119 : bar 3 119 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_120 : bar 3 120 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_121 : bar 3 121 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_122 : bar 3 122 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_123 : bar 3 123 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_124 : bar 3 124 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_125 : bar 3 125 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_126 : bar 3 126 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_127 : bar 3 127 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_3_128 : bar 3 128 = true := by decide +kernel

theorem checked_3 : ∀ i < N 3, bar 3 i = true := by
  intro i hi
  have hi' : i < 129 := by simpa only [N, states, List.length_cons, List.length_nil] using hi
  interval_cases i
  · exact check_3_0
  · exact check_3_1
  · exact check_3_2
  · exact check_3_3
  · exact check_3_4
  · exact check_3_5
  · exact check_3_6
  · exact check_3_7
  · exact check_3_8
  · exact check_3_9
  · exact check_3_10
  · exact check_3_11
  · exact check_3_12
  · exact check_3_13
  · exact check_3_14
  · exact check_3_15
  · exact check_3_16
  · exact check_3_17
  · exact check_3_18
  · exact check_3_19
  · exact check_3_20
  · exact check_3_21
  · exact check_3_22
  · exact check_3_23
  · exact check_3_24
  · exact check_3_25
  · exact check_3_26
  · exact check_3_27
  · exact check_3_28
  · exact check_3_29
  · exact check_3_30
  · exact check_3_31
  · exact check_3_32
  · exact check_3_33
  · exact check_3_34
  · exact check_3_35
  · exact check_3_36
  · exact check_3_37
  · exact check_3_38
  · exact check_3_39
  · exact check_3_40
  · exact check_3_41
  · exact check_3_42
  · exact check_3_43
  · exact check_3_44
  · exact check_3_45
  · exact check_3_46
  · exact check_3_47
  · exact check_3_48
  · exact check_3_49
  · exact check_3_50
  · exact check_3_51
  · exact check_3_52
  · exact check_3_53
  · exact check_3_54
  · exact check_3_55
  · exact check_3_56
  · exact check_3_57
  · exact check_3_58
  · exact check_3_59
  · exact check_3_60
  · exact check_3_61
  · exact check_3_62
  · exact check_3_63
  · exact check_3_64
  · exact check_3_65
  · exact check_3_66
  · exact check_3_67
  · exact check_3_68
  · exact check_3_69
  · exact check_3_70
  · exact check_3_71
  · exact check_3_72
  · exact check_3_73
  · exact check_3_74
  · exact check_3_75
  · exact check_3_76
  · exact check_3_77
  · exact check_3_78
  · exact check_3_79
  · exact check_3_80
  · exact check_3_81
  · exact check_3_82
  · exact check_3_83
  · exact check_3_84
  · exact check_3_85
  · exact check_3_86
  · exact check_3_87
  · exact check_3_88
  · exact check_3_89
  · exact check_3_90
  · exact check_3_91
  · exact check_3_92
  · exact check_3_93
  · exact check_3_94
  · exact check_3_95
  · exact check_3_96
  · exact check_3_97
  · exact check_3_98
  · exact check_3_99
  · exact check_3_100
  · exact check_3_101
  · exact check_3_102
  · exact check_3_103
  · exact check_3_104
  · exact check_3_105
  · exact check_3_106
  · exact check_3_107
  · exact check_3_108
  · exact check_3_109
  · exact check_3_110
  · exact check_3_111
  · exact check_3_112
  · exact check_3_113
  · exact check_3_114
  · exact check_3_115
  · exact check_3_116
  · exact check_3_117
  · exact check_3_118
  · exact check_3_119
  · exact check_3_120
  · exact check_3_121
  · exact check_3_122
  · exact check_3_123
  · exact check_3_124
  · exact check_3_125
  · exact check_3_126
  · exact check_3_127
  · exact check_3_128

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_0 : bar 4 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_1 : bar 4 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_2 : bar 4 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_3 : bar 4 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_4 : bar 4 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_5 : bar 4 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_6 : bar 4 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_7 : bar 4 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_8 : bar 4 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_9 : bar 4 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_10 : bar 4 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_11 : bar 4 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_12 : bar 4 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_13 : bar 4 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_14 : bar 4 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_15 : bar 4 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_16 : bar 4 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_17 : bar 4 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_18 : bar 4 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_19 : bar 4 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_20 : bar 4 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_21 : bar 4 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_22 : bar 4 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_23 : bar 4 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_24 : bar 4 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_25 : bar 4 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_26 : bar 4 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_27 : bar 4 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_28 : bar 4 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_29 : bar 4 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_30 : bar 4 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_31 : bar 4 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_32 : bar 4 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_33 : bar 4 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_34 : bar 4 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_35 : bar 4 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_36 : bar 4 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_37 : bar 4 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_38 : bar 4 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_39 : bar 4 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_40 : bar 4 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_41 : bar 4 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_42 : bar 4 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_43 : bar 4 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_44 : bar 4 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_45 : bar 4 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_46 : bar 4 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_47 : bar 4 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_48 : bar 4 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_49 : bar 4 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_50 : bar 4 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_51 : bar 4 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_52 : bar 4 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_53 : bar 4 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_54 : bar 4 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_55 : bar 4 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_56 : bar 4 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_57 : bar 4 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_58 : bar 4 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_59 : bar 4 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_60 : bar 4 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_61 : bar 4 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_62 : bar 4 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_63 : bar 4 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_64 : bar 4 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_65 : bar 4 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_66 : bar 4 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_67 : bar 4 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_68 : bar 4 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_69 : bar 4 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_70 : bar 4 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_71 : bar 4 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_72 : bar 4 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_73 : bar 4 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_74 : bar 4 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_75 : bar 4 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_76 : bar 4 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_77 : bar 4 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_78 : bar 4 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_79 : bar 4 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_80 : bar 4 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_81 : bar 4 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_82 : bar 4 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_83 : bar 4 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_84 : bar 4 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_85 : bar 4 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_86 : bar 4 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_87 : bar 4 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_88 : bar 4 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_89 : bar 4 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_90 : bar 4 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_91 : bar 4 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_92 : bar 4 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_93 : bar 4 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_94 : bar 4 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_95 : bar 4 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_96 : bar 4 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_97 : bar 4 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_98 : bar 4 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_99 : bar 4 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_100 : bar 4 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_101 : bar 4 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_102 : bar 4 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_103 : bar 4 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_104 : bar 4 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_105 : bar 4 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_106 : bar 4 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_107 : bar 4 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_108 : bar 4 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_109 : bar 4 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_110 : bar 4 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_111 : bar 4 111 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_112 : bar 4 112 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_113 : bar 4 113 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_114 : bar 4 114 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_115 : bar 4 115 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_116 : bar 4 116 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_117 : bar 4 117 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_118 : bar 4 118 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_119 : bar 4 119 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_120 : bar 4 120 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_121 : bar 4 121 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_122 : bar 4 122 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_123 : bar 4 123 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_124 : bar 4 124 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_125 : bar 4 125 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_126 : bar 4 126 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_127 : bar 4 127 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_128 : bar 4 128 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_129 : bar 4 129 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_130 : bar 4 130 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_131 : bar 4 131 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_132 : bar 4 132 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_133 : bar 4 133 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_134 : bar 4 134 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_135 : bar 4 135 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_136 : bar 4 136 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_137 : bar 4 137 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_138 : bar 4 138 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_139 : bar 4 139 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_140 : bar 4 140 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_141 : bar 4 141 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_142 : bar 4 142 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_143 : bar 4 143 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_144 : bar 4 144 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_145 : bar 4 145 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_146 : bar 4 146 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_147 : bar 4 147 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_148 : bar 4 148 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_149 : bar 4 149 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_4_150 : bar 4 150 = true := by decide +kernel

theorem checked_4 : ∀ i < N 4, bar 4 i = true := by
  intro i hi
  have hi' : i < 151 := by simpa only [N, states, List.length_cons, List.length_nil] using hi
  interval_cases i
  · exact check_4_0
  · exact check_4_1
  · exact check_4_2
  · exact check_4_3
  · exact check_4_4
  · exact check_4_5
  · exact check_4_6
  · exact check_4_7
  · exact check_4_8
  · exact check_4_9
  · exact check_4_10
  · exact check_4_11
  · exact check_4_12
  · exact check_4_13
  · exact check_4_14
  · exact check_4_15
  · exact check_4_16
  · exact check_4_17
  · exact check_4_18
  · exact check_4_19
  · exact check_4_20
  · exact check_4_21
  · exact check_4_22
  · exact check_4_23
  · exact check_4_24
  · exact check_4_25
  · exact check_4_26
  · exact check_4_27
  · exact check_4_28
  · exact check_4_29
  · exact check_4_30
  · exact check_4_31
  · exact check_4_32
  · exact check_4_33
  · exact check_4_34
  · exact check_4_35
  · exact check_4_36
  · exact check_4_37
  · exact check_4_38
  · exact check_4_39
  · exact check_4_40
  · exact check_4_41
  · exact check_4_42
  · exact check_4_43
  · exact check_4_44
  · exact check_4_45
  · exact check_4_46
  · exact check_4_47
  · exact check_4_48
  · exact check_4_49
  · exact check_4_50
  · exact check_4_51
  · exact check_4_52
  · exact check_4_53
  · exact check_4_54
  · exact check_4_55
  · exact check_4_56
  · exact check_4_57
  · exact check_4_58
  · exact check_4_59
  · exact check_4_60
  · exact check_4_61
  · exact check_4_62
  · exact check_4_63
  · exact check_4_64
  · exact check_4_65
  · exact check_4_66
  · exact check_4_67
  · exact check_4_68
  · exact check_4_69
  · exact check_4_70
  · exact check_4_71
  · exact check_4_72
  · exact check_4_73
  · exact check_4_74
  · exact check_4_75
  · exact check_4_76
  · exact check_4_77
  · exact check_4_78
  · exact check_4_79
  · exact check_4_80
  · exact check_4_81
  · exact check_4_82
  · exact check_4_83
  · exact check_4_84
  · exact check_4_85
  · exact check_4_86
  · exact check_4_87
  · exact check_4_88
  · exact check_4_89
  · exact check_4_90
  · exact check_4_91
  · exact check_4_92
  · exact check_4_93
  · exact check_4_94
  · exact check_4_95
  · exact check_4_96
  · exact check_4_97
  · exact check_4_98
  · exact check_4_99
  · exact check_4_100
  · exact check_4_101
  · exact check_4_102
  · exact check_4_103
  · exact check_4_104
  · exact check_4_105
  · exact check_4_106
  · exact check_4_107
  · exact check_4_108
  · exact check_4_109
  · exact check_4_110
  · exact check_4_111
  · exact check_4_112
  · exact check_4_113
  · exact check_4_114
  · exact check_4_115
  · exact check_4_116
  · exact check_4_117
  · exact check_4_118
  · exact check_4_119
  · exact check_4_120
  · exact check_4_121
  · exact check_4_122
  · exact check_4_123
  · exact check_4_124
  · exact check_4_125
  · exact check_4_126
  · exact check_4_127
  · exact check_4_128
  · exact check_4_129
  · exact check_4_130
  · exact check_4_131
  · exact check_4_132
  · exact check_4_133
  · exact check_4_134
  · exact check_4_135
  · exact check_4_136
  · exact check_4_137
  · exact check_4_138
  · exact check_4_139
  · exact check_4_140
  · exact check_4_141
  · exact check_4_142
  · exact check_4_143
  · exact check_4_144
  · exact check_4_145
  · exact check_4_146
  · exact check_4_147
  · exact check_4_148
  · exact check_4_149
  · exact check_4_150

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_0 : bar 5 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_1 : bar 5 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_2 : bar 5 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_3 : bar 5 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_4 : bar 5 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_5 : bar 5 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_6 : bar 5 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_7 : bar 5 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_8 : bar 5 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_9 : bar 5 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_10 : bar 5 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_11 : bar 5 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_12 : bar 5 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_13 : bar 5 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_14 : bar 5 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_15 : bar 5 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_16 : bar 5 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_17 : bar 5 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_18 : bar 5 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_19 : bar 5 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_20 : bar 5 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_21 : bar 5 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_22 : bar 5 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_23 : bar 5 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_5_24 : bar 5 24 = true := by decide +kernel

theorem checked_5 : ∀ i < N 5, bar 5 i = true := by
  intro i hi
  have hi' : i < 25 := by simpa only [N, states, List.length_cons, List.length_nil] using hi
  interval_cases i
  · exact check_5_0
  · exact check_5_1
  · exact check_5_2
  · exact check_5_3
  · exact check_5_4
  · exact check_5_5
  · exact check_5_6
  · exact check_5_7
  · exact check_5_8
  · exact check_5_9
  · exact check_5_10
  · exact check_5_11
  · exact check_5_12
  · exact check_5_13
  · exact check_5_14
  · exact check_5_15
  · exact check_5_16
  · exact check_5_17
  · exact check_5_18
  · exact check_5_19
  · exact check_5_20
  · exact check_5_21
  · exact check_5_22
  · exact check_5_23
  · exact check_5_24

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_6_0 : bar 6 0 = true := by decide +kernel

theorem checked_6 : ∀ i < N 6, bar 6 i = true := by
  intro i hi
  have hi' : i < 1 := by simpa only [N, states, List.length_cons, List.length_nil] using hi
  interval_cases i
  · exact check_6_0

theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < N s, bar s i = true := by
  interval_cases s
  · exact checked_0
  · exact checked_1
  · exact checked_2
  · exact checked_3
  · exact checked_4
  · exact checked_5
  · exact checked_6

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : NatRun (mask 12) (goal 12) s xsG) : False := by
  have h6 : NatRun (mask 12) (goal 12) 6 xsG := extend_run h hs
  have p : xsG.Perm (S 6 0) := by decide +kernel
  exact bar_all checked 6 (by decide) 0 (by decide) (Run.perm p h6)

end PEqualNP.Outside.L_meta_274_aux.R

theorem PEqualNP.Outside.L_meta_274 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ (∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true)) := by
  rintro ⟨C, hok, hsize, hev⟩
  have hc : PEqualNP.MetaComplexity.HasCircuitSize 4 PEqualNP.Outside.L_meta_274_aux.R.fG 6 := by
    refine ⟨C, hok, hsize, ?_⟩
    intro x
    apply Bool.eq_iff_iff.mpr
    simpa [PEqualNP.Outside.L_meta_274_aux.R.fG] using hev x
  have h := PEqualNP.Outside.L_meta_274_aux.R.mainG PEqualNP.Outside.L_meta_274_aux.R.noRunFull 6 hc
  omega
