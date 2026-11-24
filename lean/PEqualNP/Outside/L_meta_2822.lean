import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2822_aux.Helpers
open PEqualNP.MetaComplexity

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

end PEqualNP.Outside.L_meta_2822_aux.Helpers

namespace PEqualNP.Outside.L_meta_2822_aux.Helpers
open PEqualNP.MetaComplexity

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

end PEqualNP.Outside.L_meta_2822_aux.Helpers

namespace PEqualNP.Outside.L_meta_2822_aux.Helpers
open PEqualNP.MetaComplexity

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

end PEqualNP.Outside.L_meta_2822_aux.Helpers

namespace PEqualNP.Outside.L_meta_2822_aux.Perm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2822_aux.Helpers

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
end PEqualNP.Outside.L_meta_2822_aux.Perm

namespace PEqualNP.Outside.L_meta_2822_aux.M168

namespace L_meta_168_helpers

open PEqualNP.CircuitLowerBounds

private theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ)
    (h : j ≠ L.length) : (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

private theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ)
    (h : L.length = k) : (L ++ [S]).getD k d = S := by
  subst h; simp

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
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

private theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

private theorem getD_wiresFrom_input (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length →
      (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    have h' : i < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp; omega
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i h'
    exact this.trans (List.getD_append _ _ _ _ h)

private theorem mem_take_one {α : Type} {a : α} (l : List α) :
    a ∈ l.take 1 ↔ l.head? = some a := by
  rw [List.take_one]
  cases l <;> simp [eq_comm]

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

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

private theorem mem_normGate_inputs_iff (n : ℕ) (g : Gate) :
    n ∈ (normGate g).inputs ↔
      (g.op = GateOp.not ∧ g.inputs.head? = some n) ∨
      (g.op ≠ GateOp.not ∧ n ∈ g.inputs) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not =>
    simp only [normGate]
    rw [mem_take_one inputs]
    simp
  | and => simp [normGate]
  | or => simp [normGate]
  | mod m => simp [normGate]
  | maj => simp [normGate]

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

private theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
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

private def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

private def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

private theorem elim_len_add_count_le (n k : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) → k < acc.1.length →
      (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3]
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    have hk' : k < (elimStep n acc g).1.length := by simp [elimStep]; omega
    have hc' : ∃ c, (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl c := by
      obtain ⟨c, hc⟩ := hc
      refine ⟨c, ?_⟩
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hc
    have hih := ih (elimStep n acc g) hok' hk' hc'
    by_cases hkg : k ∈ g.inputs
    · have hcnt : (g :: gs).countP (fun g => decide (k ∈ g.inputs))
          = gs.countP (fun g => decide (k ∈ g.inputs)) + 1 := by
        rw [List.countP_cons]
        simp [hkg]
      have hsim : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact (hok g List.mem_cons_self).1.1
        · simpa using (hok g List.mem_cons_self).1.2
        · intro h; simpa using (hok g List.mem_cons_self).2 h
        · obtain ⟨c, hc⟩ := hc
          exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, List.length_append]
        rw [hsim]; simp
      rw [hcnt, List.length_cons]
      omega
    · have hcnt : (g :: gs).countP (fun g => decide (k ∈ g.inputs))
          = gs.countP (fun g => decide (k ∈ g.inputs)) := by
        rw [List.countP_cons]
        simp [hkg]
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [hcnt, List.length_cons]
      omega

private theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

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

private def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

private theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
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

private theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

private theorem wiresFrom_agree_off {n : ℕ} (gs : List Gate)
    (hno : ∀ g ∈ gs, n ∉ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, i ≠ n → w.getD i false = w'.getD i false) →
      ∀ j, j ≠ n → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil =>
    intro w w' _ hagree j hj
    exact hagree j hj
  | cons g gs ih =>
    intro w w' hlen hagree j hj
    have hno' : ∀ g' ∈ gs, n ∉ g'.inputs :=
      fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')
    have hgn : n ∉ g.inputs := hno g List.mem_cons_self
    have hlen1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).length := by
      simp [hlen]
    have hagree1 : ∀ i, i ≠ n →
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).getD i false := by
      intro i hi
      by_cases hlt : i < w.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w.length
        · subst heq
          rw [getD_snoc_len w _ _ w.length rfl, getD_snoc_len w' _ _ w.length hlen.symm]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact hagree a (fun e => hgn (e ▸ ha))
        · have hwl : i ≠ w'.length := by omega
          rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ hwl]
          exact hagree i hi
    exact ih hno'
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      hlen1 hagree1 j hj

private theorem two_le_countP_of_two_getElem {α : Type} (p : α → Bool) (l : List α)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i ≠ j)
    (hpi : p l[i] = true) (hpj : p l[j] = true) : 2 ≤ l.countP p := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, j + 1 =>
      have ha : p a = true := by simpa using hpi
      have hj' : j < l.length := by simpa using hj
      have hpj' : p l[j] = true := by simpa using hpj
      rw [List.countP_cons, if_pos ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[j], List.getElem_mem hj', hpj'⟩
      omega
    | i + 1, 0 =>
      have ha : p a = true := by simpa using hpj
      have hi' : i < l.length := by simpa using hi
      have hpi' : p l[i] = true := by simpa using hpi
      rw [List.countP_cons, if_pos ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[i], List.getElem_mem hi', hpi'⟩
      omega
    | i + 1, j + 1 =>
      have hi' : i < l.length := by simpa using hi
      have hj' : j < l.length := by simpa using hj
      have hij' : i ≠ j := by omega
      have hpi' : p l[i] = true := by simpa using hpi
      have hpj' : p l[j] = true := by simpa using hpj
      have hrec := ih i j hi' hj' hij' hpi' hpj'
      rw [List.countP_cons]
      have hle : l.countP p ≤ l.countP p + (if p a then 1 else 0) := Nat.le_add_right _ _
      omega

end L_meta_168_helpers

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open L_meta_168_helpers

theorem L_meta_168 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' false)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false)) s → C.size ≤ s + 1) → ∃ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) ∧ ∀ j' : Fin C.gates.length, ((C.gates.get j').op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j').inputs.head? = some n ∨ (C.gates.get j').op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j').inputs) → j' = j := by
  intro n C hmin hdep hnc hsize
  obtain ⟨hCok, _⟩ := hmin
  set gs : List Gate := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hCok g0 hg0)
  have hout : C.output ≠ n := by
    intro houtn
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have hv : ∀ z : Fin n → Bool, circuitFun (n + 1) C (Fin.snoc z false) = false := by
      intro z
      show (wiresFrom C.gates (List.ofFn (Fin.snoc z false))).getD C.output false = false
      rw [houtn]
      rw [getD_wiresFrom_input C.gates _ n (by
        rw [List.length_ofFn]; exact Nat.lt_succ_self n)]
      rw [ofFn_snoc]
      rw [getD_snoc_len _ _ _ n (by simp [List.length_ofFn])]
    rw [hv y, hv y']
  have hex : ∃ j : Fin C.gates.length, n ∈ (normGate (C.gates.get j)).inputs := by
    by_contra hnone
    push_neg at hnone
    have hno : ∀ g ∈ gs, n ∉ g.inputs := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      obtain ⟨i, hi⟩ := List.mem_iff_get.1 hg0
      rw [← hi]
      exact hnone i
    obtain ⟨y, hne⟩ := hdep
    have hlen : (List.ofFn (Fin.snoc y false)).length
        = (List.ofFn (Fin.snoc y true)).length := by simp
    have hagree : ∀ i, i ≠ n →
        (List.ofFn (Fin.snoc y false)).getD i false
          = (List.ofFn (Fin.snoc y true)).getD i false := by
      intro i hi
      rw [ofFn_snoc, ofFn_snoc]
      by_cases hlt : i < n
      · rw [List.getD_append _ _ _ _ (by simpa [List.length_ofFn] using hlt),
            List.getD_append _ _ _ _ (by simpa [List.length_ofFn] using hlt)]
      · have hli : i ≠ (List.ofFn y).length := by simp [List.length_ofFn]; omega
        rw [getD_snoc_ne _ _ _ _ hli, getD_snoc_ne _ _ _ _ hli]
    have hEq := wiresFrom_agree_off (n := n) gs hno _ _ hlen hagree C.output hout
    apply hne
    show (wiresFrom C.gates (List.ofFn (Fin.snoc y false))).getD C.output false
        = (wiresFrom C.gates (List.ofFn (Fin.snoc y true))).getD C.output false
    simpa [hgs, wiresFrom_norm] using hEq
  set acc : List Stat × List Gate := elim n gs (initStats n false, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y false))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n (List.ofFn y) (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n false y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = circuitFun (n + 1) C (Fin.snoc y false) := by
    intro y
    rw [((hinv y).2 C.output).2]
    rw [hgs, wiresFrom_norm]
    rfl
  have hcs : HasCircuitSize n
      (fun y : Fin n → Bool => circuitFun (n + 1) C (Fin.snoc y false)) acc.2.length := by
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      exfalso
      obtain ⟨y, y', hne⟩ := hnc
      apply hne
      rw [← hval y, ← hval y', hst]
      rfl
    | inr j =>
      refine ⟨⟨acc.2, j⟩, ?_, le_rfl, ?_⟩
      · intro g hg
        exact elim_ok n gs (initStats n false, []) (by simp) g hg
      · intro y
        change (⟨acc.2, j⟩ : Circuit).eval (List.ofFn y)
          = circuitFun (n + 1) C (Fin.snoc y false)
        rw [← hval y, hst]
        rfl
  have hsize' : C.size ≤ acc.2.length + 1 := hsize acc.2.length hcs
  have hcount_bound : acc.2.length + gs.countP (fun g => decide (n ∈ g.inputs)) ≤ C.size := by
    have h := elim_len_add_count_le n n gs (initStats n false, []) hnok
      (by simp [initStats]) ⟨false, getD_snoc_len _ _ _ _ (by simp)⟩
    simpa [acc, hgs, Circuit.size, List.length_nil, Nat.zero_add] using h
  have hcount_le : gs.countP (fun g => decide (n ∈ g.inputs)) ≤ 1 := by omega
  obtain ⟨j0, hj0⟩ := hex
  refine ⟨j0, (mem_normGate_inputs_iff n (C.gates.get j0)).1 hj0, ?_⟩
  intro j' hj'
  by_contra hne
  have hdec0 : (fun g => decide (n ∈ (normGate g).inputs)) (C.gates.get j0) = true := by
    simpa using hj0
  have hdecj : (fun g => decide (n ∈ (normGate g).inputs)) (C.gates.get j') = true := by
    simpa using (mem_normGate_inputs_iff n (C.gates.get j')).2 hj'
  have hij : j0.val ≠ j'.val := by
    intro h
    exact (Ne.symm hne) (Fin.ext h)
  have h2' := two_le_countP_of_two_getElem (fun g => decide (n ∈ (normGate g).inputs))
    C.gates j0.val j'.val j0.isLt j'.isLt hij hdec0 hdecj
  have h2 : 2 ≤ gs.countP (fun g => decide (n ∈ g.inputs)) := by
    rw [hgs, List.countP_map]
    exact h2'
  omega

end PEqualNP.Outside.L_meta_2822_aux.M168

namespace PEqualNP.Outside.L_meta_2822_aux.Meta169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

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

private def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

private theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
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

private theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

private theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

private theorem normGate_of_ne_not (g : Gate) (h : g.op ≠ GateOp.not) : normGate g = g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [normGate]

private theorem normGate_read (g : Gate) (n : ℕ)
    (h : g.op = GateOp.not ∧ g.inputs.head? = some n ∨
      g.op ≠ GateOp.not ∧ n ∈ g.inputs) : n ∈ (normGate g).inputs := by
  rcases h with ⟨hop, hhead⟩ | ⟨hop, hmem⟩
  · have htake : g.inputs.take 1 = [n] := by
      rcases h : g.inputs with _ | ⟨a, ins⟩ <;> simp_all
    simp [normGate, hop, htake]
  · simpa only [normGate_of_ne_not g hop] using hmem

private theorem elim_stat_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem elim_read_const (n k : ℕ) (acc : List Stat × List Gate) (g : Gate)
    (hg : NOk g) (hread : k ∈ g.inputs) (b : Bool)
    (hfix : acc.1.getD k (Sum.inl false) = Sum.inl b) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none :=
    simplify_count _ _ _ hg.1.1 (by simpa using hg.1.2)
      (fun h => by simpa using hg.2 h) ⟨b, List.mem_map.mpr ⟨k, hread, hfix⟩⟩
  change (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]
  simp

private theorem bad_reader_constant (n m : ℕ) (stats : List Stat) (g : Gate)
    (hg : NOk g) (hread : n ∈ g.inputs) (hfix : stats.getD n (Sum.inl false) = Sum.inl false)
    (hbad : ¬(g.op = GateOp.or ∧ g.inputs.length = 2 ∧
      ∃ w ∈ g.inputs, w ≠ n ∧ w < stats.length)) :
    ∃ b, (simplify g.op m (g.inputs.map fun i => stats.getD i (Sum.inl false))).2 =
      Sum.inl b := by
  obtain ⟨op, ins⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := hg.1.1
  have hlen : ins.length ≤ 2 := hg.1.2
  simp only [List.getD_eq_getElem?_getD] at hfix
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨false, by simp [simplify, simpAnd, hfix]⟩
    · have hmem : n = a ∨ n = b := by simpa using hread
      rcases hmem with ha | hb
      · subst a
        refine ⟨false, ?_⟩
        cases hb : stats[b]?.getD (Sum.inl false) <;> simp [simplify, simpAnd, hfix, hb]
      · subst b
        refine ⟨false, ?_⟩
        cases ha : stats[a]?.getD (Sum.inl false) <;> simp [simplify, simpAnd, hfix, ha]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨false, by simp [simplify, simpOr, hfix]⟩
    · have hout (w : ℕ) (hw : w ∈ [a, b]) :
          stats[w]?.getD (Sum.inl false) = Sum.inl false := by
        by_cases hn : w = n
        · simpa only [hn] using hfix
        · have hnlt : ¬w < stats.length := fun hlt => hbad ⟨rfl, rfl, w, hw, hn, hlt⟩
          exact List.getD_eq_default _ _ (Nat.le_of_not_gt hnlt)
      exact ⟨false, by simp [simplify, simpOr, hout a (by simp), hout b (by simp)]⟩
    · simp at hlen
  · have hone : ins.length ≤ 1 := hg.2 rfl
    rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hread
    · have ha : n = a := by simpa using hread
      subst a
      exact ⟨true, by simp [simplify, simpNot, hfix]⟩
    · simp at hone

private theorem wires_agree (gs : List Gate) (bad : ℕ → Prop) (w w' : List Bool)
    (hlen : w.length = w'.length)
    (hw : ∀ i, ¬bad i → w.getD i false = w'.getD i false)
    (hgs : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬bad i) :
    ∀ i, ¬bad i → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs generalizing w w' with
  | nil => exact hw
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    let v' := g.op.eval (g.inputs.map fun i => w'.getD i false)
    have hv : v = v' := by
      dsimp only [v, v']
      congr 1
      exact List.map_congr_left (fun i hi => hw i (hgs g List.mem_cons_self i hi))
    change ∀ i, ¬bad i → (wiresFrom gs (w ++ [v])).getD i false =
      (wiresFrom gs (w' ++ [v'])).getD i false
    apply ih _ _ (by simp [hlen]) _ (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    intro i hi
    by_cases heq : i = w.length
    · rw [getD_snoc_len _ _ _ _ heq.symm, getD_snoc_len _ _ _ _ (hlen.symm.trans heq.symm), hv]
    · rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ (by omega)]
      exact hw i hi

end PEqualNP.Outside.L_meta_2822_aux.Meta169

namespace PEqualNP.Outside.L_meta_2822_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2822_aux.Meta169

theorem L_meta_169_thm : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' false)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false)) s → C.size ≤ s + 1) → ∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧ n ∈ (C.gates.get j).inputs ∧ ∃ w ∈ (C.gates.get j).inputs, w ≠ n ∧ w < n + 1 + j.val := by
  classical
  intro n C hmin hdep hnonconst htight j hreads
  by_contra hshape
  let gs := C.gates.map normGate
  let pre := gs.take j.val
  let g := normGate (C.gates.get j)
  let post := gs.drop (j.val + 1)
  let m := n + 1 + j.val
  let start : List Stat × List Gate := (initStats n false, [])
  let before := elim n pre start
  let after := elimStep n before g
  let final := elim n post after
  have hj : j.val < gs.length := by simp [gs]
  have hsplit : gs = pre ++ g :: post := by
    have hs := List.take_append_drop j.val gs
    rw [List.drop_eq_getElem_cons hj] at hs
    simpa [pre, g, post, gs, List.get_eq_getElem] using hs.symm
  have hPreLen : pre.length = j.val := by
    simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hSize : C.size = pre.length + 1 + post.length := by
    have hs := congrArg List.length hsplit
    have hg : gs.length = C.size := by simp [gs, Circuit.size]
    simp only [List.length_append, List.length_cons] at hs
    omega
  have hok : ∀ k ∈ gs, NOk k := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact normGate_nok _ (hmin.1 _ hk')
  have hg : NOk g := hok g (by rw [hsplit]; simp)
  have hpre : ∀ k ∈ pre, NOk k := fun k hk =>
    hok k (by rw [hsplit]; exact List.mem_append_left _ hk)
  have hpost : ∀ k ∈ post, NOk k := fun k hk =>
    hok k (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hk))
  have hread : n ∈ g.inputs := normGate_read _ _ hreads
  have hm : before.1.length = m := by
    rw [elim_stat_length]
    simp [start, initStats, m, hPreLen]
  have hbad : ¬(g.op = GateOp.or ∧ g.inputs.length = 2 ∧
      ∃ w ∈ g.inputs, w ≠ n ∧ w < before.1.length) := by
    intro ⟨hop, hlen, w, hw, hne, hlt⟩
    have hop' : (C.gates.get j).op = GateOp.or := (normGate_op _).symm.trans hop
    have hgn : g = C.gates.get j := normGate_of_ne_not _ (by rw [hop']; simp)
    rw [hgn] at hlen hw
    exact hshape ⟨hop', hlen, by simpa only [hgn] using hread, w, hw, hne, by simpa [hm, m] using hlt⟩
  have hstart : n < start.1.length := by simp [start, initStats]
  have hfix : start.1.getD n (Sum.inl false) = Sum.inl false := by
    simp [start, initStats]
  have hbefore : before.1.getD n (Sum.inl false) = Sum.inl false := by
    exact (elim_getD n n _ pre start hstart).trans hfix

  obtain ⟨b, hconst⟩ := bad_reader_constant n (n + before.2.length) before.1 g hg hread hbefore hbad
  have hSaved : after.2.length = before.2.length := elim_read_const n n before g hg hread false hbefore
  have hAfterLen : after.1.length = m + 1 := by simp [after, elimStep, hm]
  have hAfterN : after.1.getD n (Sum.inl false) = Sum.inl false := by
    change (before.1 ++ [_]).getD n (Sum.inl false) = Sum.inl false
    rw [getD_snoc_ne _ _ _ _ (by rw [hm]; dsimp [m]; omega), hbefore]
  have hAfterM : after.1.getD m (Sum.inl false) = Sum.inl b := by
    change (before.1 ++ [_]).getD m (Sum.inl false) = Sum.inl b
    rw [getD_snoc_len _ _ _ _ hm, hconst]
  have hFinal : elim n gs start = final := by
    rw [hsplit]
    simp only [elim, List.foldl_append]
    rfl
  have heval (y : Fin n → Bool) :
      (final.1.getD C.output (Sum.inl false)).val (wiresFrom final.2 (List.ofFn y)) =
        circuitFun (n + 1) C (Fin.snoc y false) := by
    have hv := (inv_elim n (List.ofFn y) (by simp) gs _ start
      (fun k hk => (hok k hk).1) (inv_init n false y)).2 C.output
    rw [hFinal] at hv
    simp only [circuitFun, Circuit.eval, ofFn_snoc]
    change _ = (wiresFrom C.gates (List.ofFn y ++ [false])).getD C.output false
    rw [← wiresFrom_norm C.gates]
    exact hv.2
  obtain ⟨out, hout⟩ : ∃ out, final.1.getD C.output (Sum.inl false) = Sum.inr out := by
    cases h : final.1.getD C.output (Sum.inl false) with
    | inr out => exact ⟨out, rfl⟩
    | inl c =>
      obtain ⟨y, y', hne⟩ := hnonconst
      exfalso
      apply hne
      rw [← heval y, ← heval y', h]
      rfl
  have hOutN : C.output ≠ n := by
    intro h
    rw [h, elim_getD n n _ post after (by rw [hAfterLen]; dsimp [m]; omega), hAfterN] at hout
    cases hout
  have hOutM : C.output ≠ m := by
    intro h
    rw [h, elim_getD n m _ post after (by omega), hAfterM] at hout
    cases hout
  have hLower : C.size ≤ final.2.length + 1 := by
    apply htight final.2.length
    refine ⟨⟨final.2, out⟩, ?_, le_rfl, ?_⟩
    · have ho := elim_ok n gs start (by simp [start])
      rwa [hFinal] at ho
    · intro y
      have he := heval y
      rw [hout] at he
      exact he
  have hBeforeLen : before.2.length ≤ pre.length := by
    simpa [before, start] using elim_len n pre start
  have hFinalLen : final.2.length ≤ after.2.length + post.length :=
    elim_len n post after

  have noPre (k : Gate) (hk : k ∈ pre) : n ∉ k.inputs := by
    intro hr
    have h := elim_len_lt n n pre start hpre hstart ⟨false, hfix⟩ ⟨k, hk, hr⟩
    change before.2.length + 1 ≤ 0 + pre.length at h
    omega
  have noPost (k : Gate) (hk : k ∈ post) (i : ℕ) (hi : i ∈ k.inputs) :
      ¬(i = n ∨ i = m) := by
    intro hbadIndex
    rcases hbadIndex with hN | hM
    · subst i
      have h := elim_len_lt n n post after hpost
        (by rw [hAfterLen]; dsimp [m]; omega) ⟨false, hAfterN⟩ ⟨k, hk, hi⟩
      change final.2.length + 1 ≤ after.2.length + post.length at h
      omega
    · subst i
      have h := elim_len_lt n m post after hpost
        (by omega) ⟨b, hAfterM⟩ ⟨k, hk, hi⟩
      change final.2.length + 1 ≤ after.2.length + post.length at h
      omega

  obtain ⟨y, hne⟩ := hdep
  apply hne
  let input (b : Bool) := List.ofFn y ++ [b]
  have hInputLen (b : Bool) : (input b).length = n + 1 := by simp [input]
  let w (b : Bool) := wiresFrom pre (input b)
  have hwLen (b : Bool) : (w b).length = m := by
    simp [w, length_wiresFrom, hInputLen, hPreLen, m]
  have hw : ∀ i, i ≠ n → (w false).getD i false = (w true).getD i false := by
    apply wires_agree pre (fun i => i = n) _ _ (by simp [hInputLen]) _
      (fun k hk i hi he => noPre k hk (he ▸ hi))
    intro i hi
    change (List.ofFn y ++ [false]).getD i false = (List.ofFn y ++ [true]).getD i false
    have hin : i ≠ (List.ofFn y).length := by simpa using hi
    rw [getD_snoc_ne _ _ _ _ hin, getD_snoc_ne _ _ _ _ hin]
  let extended (b : Bool) := w b ++ [g.op.eval (g.inputs.map fun i => (w b).getD i false)]
  have ha : ∀ i, ¬(i = n ∨ i = m) →
      (extended false).getD i false = (extended true).getD i false := by
    intro i hi
    have hin : i ≠ n := fun he => hi (Or.inl he)
    have him : i ≠ m := fun he => hi (Or.inr he)
    dsimp only [extended]
    rw [getD_snoc_ne _ _ _ _ (by simpa [hwLen] using him),
      getD_snoc_ne _ _ _ _ (by simpa [hwLen] using him)]
    exact hw i hin
  have hv := wires_agree post (fun i => i = n ∨ i = m) (extended false) (extended true)
    (by simp [extended, hwLen]) ha noPost C.output (by simp [hOutN, hOutM])
  simp only [circuitFun, Circuit.eval, ofFn_snoc]
  change (wiresFrom C.gates (input false)).getD C.output false =
    (wiresFrom C.gates (input true)).getD C.output false
  have hs : C.gates.map normGate = pre ++ g :: post := hsplit
  simp only [← wiresFrom_norm C.gates, hs, wiresFrom_append]
  exact hv

end PEqualNP.Outside.L_meta_2822_aux

namespace PEqualNP.Outside.L_meta_2822_aux.Proof
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2822_aux.Helpers PEqualNP.Outside.L_meta_2822_aux.Perm
theorem relabel_perm_fanInTwo {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (h : FanInTwo C) : FanInTwo (relabel n n σ C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  exact ⟨(h g0 hg0).1, by simpa [relGate] using (h g0 hg0).2⟩

theorem relabel_perm_size {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (relabel n n σ C).size = C.size := by
  simp [relabel, Circuit.size]

theorem relabel_perm_circuitFun {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (x : Fin n → Bool) :
    circuitFun n (relabel n n σ C) x = circuitFun n C (x ∘ σ) := by
  exact (rel_fold n n σ C.gates _ _ (rel_init n n σ x)).2.2 C.output

theorem relabel_perm_minimal {n : ℕ} (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (h : IsMinimalCircuit n C) : IsMinimalCircuit n (relabel n n σ C) := by
  refine ⟨relabel_perm_fanInTwo σ C h.1, ?_⟩
  intro D hDfit hDcf
  let D' := relabel n n σ.symm D
  have hD'cf : circuitFun n D' = circuitFun n C := by
    funext x
    rw [relabel_perm_circuitFun, hDcf, relabel_perm_circuitFun]
    congr 1
    funext i
    simp
  have hle := h.2 D' (relabel_perm_fanInTwo σ.symm D hDfit) hD'cf
  simpa [D', relabel_perm_size] using hle

theorem wmap_perm_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) :
    wmap n n σ w = if h : w < n then (σ ⟨w, h⟩ : ℕ) else w := by
  unfold wmap
  split
  · rfl
  · omega

theorem wmap_perm_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (j w : ℕ) :
    wmap n n σ w < n + j ↔ w < n + j := by
  rw [wmap_perm_eq]
  split
  · rename_i h
    have h2 := (σ ⟨w, h⟩).isLt
    omega
  · rfl


end PEqualNP.Outside.L_meta_2822_aux.Proof


namespace PEqualNP.Outside.L_meta_2822_aux.Proof
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2822_aux.Helpers PEqualNP.Outside.L_meta_2822_aux.Perm


def moveFun (i : Fin 9) (j : Fin 9) : Fin 9 :=
  if h : j.val < 8 then i.succAbove ⟨j.val,h⟩ else i

lemma move_bij (i : Fin 9) : Function.Bijective (moveFun i) := by
  have h : ∀ i : Fin 9, Function.Bijective (moveFun i) := by decide +kernel
  exact h i

noncomputable def move (i : Fin 9) : Equiv.Perm (Fin 9) := Equiv.ofBijective (moveFun i) (move_bij i)

lemma move_cast (i : Fin 9) (j : Fin 8) : move i j.castSucc = i.succAbove j := by
  simp [move,moveFun,j.isLt]
lemma move_last (i : Fin 9) : move i (Fin.last 8) = i := by simp [move,moveFun]

lemma input_eq (i : Fin 9) (b : Bool) (y : Fin 8 → Bool) :
    (Fin.snoc y b) ∘ (move i).symm = Fin.insertNth i b y := by
  funext k
  change (Fin.snoc y b : Fin 9 → Bool) ((move i).symm k) = _
  by_cases hk : k = i
  · have hi : (move i).symm i = Fin.last 8 := by
      apply (move i).injective
      simpa only [Equiv.apply_symm_apply] using (move_last i).symm
    simp only [hk, hi, Fin.insertNth_apply_same, Fin.snoc_last]
  · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hk
    have hi : (move i).symm k = j.castSucc := by
      apply (move i).injective
      simpa [move_cast] using hj.symm
    rw [hi, ← hj]
    simp
lemma insert_list (i : Fin 9) (b : Bool) (y : Fin 8 → Bool) :
    List.ofFn (Fin.insertNth i b y) = (List.ofFn y).insertIdx i.val b := by
  fin_cases i <;> simp [List.ofFn_succ,Fin.insertNth, Fin.succAboveCases]
  all_goals and_intros <;> rfl


def readsEff (C : Circuit) (w : ℕ) (j : Fin C.gates.length) : Prop :=
  ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some w) ∨
  ((C.gates.get j).op ≠ GateOp.not ∧ w ∈ (C.gates.get j).inputs)

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

lemma unique_or (C : Circuit) (i : Fin 9) (hmin : IsMinimalCircuit 9 C)
    (hdep : ∃ y : Fin 8 → Bool, C.eval ((List.ofFn y).insertIdx i.val false) ≠ C.eval ((List.ofFn y).insertIdx i.val true))
    (hnc : ∃ y z : Fin 8 → Bool, C.eval ((List.ofFn y).insertIdx i.val false) ≠ C.eval ((List.ofFn z).insertIdx i.val false))
    (htight : ∀ s, HasCircuitSize 8 (fun y => C.eval ((List.ofFn y).insertIdx i.val false)) s → C.size ≤ s+1) :
    ∃ (p : Fin C.gates.length) (w : ℕ),
      readsEff C i.val p ∧ (∀ j, readsEff C i.val j → j = p) ∧
      (gateAt C p.val).op = GateOp.or ∧
      ((gateAt C p.val).inputs = [i.val,w] ∨ (gateAt C p.val).inputs = [w,i.val]) ∧
      w ≠ i.val ∧ w < 9 + p.val := by
  classical
  let σ := (move i).symm
  let Cσ := relabel 9 9 σ C
  have hCσmin : IsMinimalCircuit 9 Cσ := relabel_perm_minimal σ C hmin
  have heval (y : Fin 8 → Bool) (b : Bool) :
      circuitFun 9 Cσ (Fin.snoc y b) = C.eval ((List.ofFn y).insertIdx i.val b) := by
    rw [relabel_perm_circuitFun]
    change C.eval (List.ofFn ((Fin.snoc y b) ∘ (move i).symm)) = _
    rw [input_eq, insert_list]
  have hdepσ : ∃ y, circuitFun 9 Cσ (Fin.snoc y false) ≠ circuitFun 9 Cσ (Fin.snoc y true) := by
    simpa only [heval] using hdep
  have hncσ : ∃ y z, circuitFun 9 Cσ (Fin.snoc y false) ≠ circuitFun 9 Cσ (Fin.snoc z false) := by
    simpa only [heval] using hnc
  have hbσ : ∀ s, HasCircuitSize 8 (fun y => circuitFun 9 Cσ (Fin.snoc y false)) s → Cσ.size ≤ s+1 := by
    intro s hs
    have heq : (fun y => circuitFun 9 Cσ (Fin.snoc y false)) = (fun y => C.eval ((List.ofFn y).insertIdx i.val false)) := funext (fun y => heval y false)
    rw [heq] at hs
    simpa [Cσ, relabel_perm_size] using htight s hs
  obtain ⟨pσ,hpσ_read,hpσ_uniq⟩ := M168.L_meta_168 8 Cσ hCσmin hdepσ hncσ hbσ
  have hpσ_or := L_meta_169_thm 8 Cσ hCσmin hdepσ hncσ hbσ pσ hpσ_read
  have hlen : Cσ.gates.length = C.gates.length := by simp [Cσ, relabel]
  have hσi : σ i = Fin.last 8 := by
    change (move i).symm i = Fin.last 8
    apply (move i).injective
    simpa only [Equiv.apply_symm_apply] using (move_last i).symm
  have hwmap_eq_n : ∀ u, wmap 9 9 σ u = 8 ↔ u = i.val := by
    intro u
    rw [wmap_perm_eq]
    split
    · rename_i hu
      constructor
      · intro h
        have hv : σ ⟨u,hu⟩ = Fin.last 8 := Fin.ext h
        have he : (⟨u,hu⟩ : Fin 9) = i := σ.injective (hv.trans hσi.symm)
        exact congrArg Fin.val he
      · intro h
        have he : (⟨u,hu⟩ : Fin 9) = i := Fin.ext h
        simpa [he] using congrArg Fin.val hσi
    · have hi := i.isLt
      constructor <;> intro h <;> omega
  have hget : ∀ (j : Fin C.gates.length),
      Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩ = relGate (9) (9) σ (C.gates.get j) := by
    intro j; simp [Cσ, relabel]
  have hreads_iff : ∀ (j : Fin C.gates.length),
      readsEff C i.val j ↔
        ((Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩).op = GateOp.not ∧
          (Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩).inputs.head? = some 8 ∨
         (Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩).op ≠ GateOp.not ∧
          8 ∈ (Cσ.gates.get ⟨j.val, hlen.symm ▸ j.isLt⟩).inputs) := by
    intro j
    rw [hget j]
    simp only [readsEff, relGate, List.head?_map, List.mem_map]
    constructor
    · rintro (⟨hop, hhd⟩ | ⟨hop, hmem⟩)
      · left; refine ⟨hop, ?_⟩
        rw [hhd]; simp [(hwmap_eq_n i.val).2 rfl]
      · right; exact ⟨hop, i.val, hmem, (hwmap_eq_n i.val).2 rfl⟩
    · rintro (⟨hop, hhd⟩ | ⟨hop, u, hu, hwu⟩)
      · left; refine ⟨hop, ?_⟩
        cases h : (C.gates.get j).inputs with
        | nil => rw [h] at hhd; simp at hhd
        | cons u tl =>
          rw [h] at hhd
          simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
          simp [(hwmap_eq_n u).1 hhd]
      · right; rw [(hwmap_eq_n u).1 hwu] at hu; exact ⟨hop, hu⟩
  let p : Fin C.gates.length := ⟨pσ.val, hlen ▸ pσ.isLt⟩
  have hp_get : Cσ.gates.get pσ = relGate (9) (9) σ (C.gates.get p) := hget p
  obtain ⟨hop, hinlen, _, wσ, hwσ_mem, hwσ_ne, hwσ_lt⟩ := hpσ_or
  rw [hp_get] at hop hinlen hwσ_mem
  simp only [relGate, List.length_map, List.mem_map] at hop hinlen hwσ_mem
  obtain ⟨w, hw_mem, rfl⟩ := hwσ_mem
  have hw_ne : w ≠ i.val := fun h => hwσ_ne ((hwmap_eq_n w).2 h)
  have hw_lt : w < 9 + p.val := (wmap_perm_lt_iff σ p.val w).1 hwσ_lt
  have hp_read : readsEff C i.val p := (hreads_iff p).2 hpσ_read
  have hp_uniq : ∀ j : Fin C.gates.length, readsEff C i.val j → j = p := by
    intro j hj
    have hjσ := (hreads_iff j).1 hj
    have heq := hpσ_uniq ⟨j.val, hlen.symm ▸ j.isLt⟩ hjσ
    have hval : j.val = pσ.val := congrArg Fin.val heq
    exact Fin.ext hval
  have hga : gateAt C p.val = C.gates.get p := gateAt_eq_getElem p.isLt
  have ha_mem : i.val ∈ (C.gates.get p).inputs := by
    rcases hp_read with ⟨hnot, _⟩ | ⟨_, hmem⟩
    · rw [hop] at hnot; cases hnot
    · exact hmem
  have hins : (C.gates.get p).inputs = [i.val, w] ∨ (C.gates.get p).inputs = [w, i.val] := by
    rcases hlist : (C.gates.get p).inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
    · rw [hlist] at hinlen; simp at hinlen
    · rw [hlist] at hinlen; simp at hinlen
    · rw [hlist] at ha_mem hw_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_mem hw_mem
      rcases ha_mem with rfl | rfl <;> rcases hw_mem with rfl | rfl
      · exact (hw_ne rfl).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (hw_ne rfl).elim
    · rw [hlist] at hinlen; simp at hinlen
  exact ⟨p, w, hp_read, hp_uniq, hga ▸ hop, hga ▸ hins, hw_ne, hw_lt⟩


lemma norm_read_eff (g : Gate) (w : ℕ) (hg : Ok g) :
    w ∈ (normGate g).inputs ↔
    (g.op = GateOp.not ∧ g.inputs.head? = some w) ∨ (g.op ≠ GateOp.not ∧ w ∈ g.inputs) := by
  have hgop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hg.1
  rcases hgop with h | h | h
  · simp [normGate, h]
  · simp [normGate, h]
  · cases hi : g.inputs with
    | nil => simp [normGate, h, hi]
    | cons a l => simp [normGate, h, hi, eq_comm]

lemma rb_norm (g : Gate) (w : ℕ) (hg : Ok g) :
    (if g.op.eval [false,false] = true then g.inputs.take 1 else g.inputs).contains w = true ↔
      w ∈ (normGate g).inputs := by
  have hgop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hg.1
  rcases hgop with h | h | h <;> simp [normGate, h, GateOp.eval]

lemma fold_block (gs : List Gate) (i w : ℕ)
    (hok : ∀ g ∈ gs, Ok g)
    (hshape : ∀ g ∈ gs, i ∈ (normGate g).inputs →
      g.op = GateOp.or ∧ (g.inputs = [i,w] ∨ g.inputs = [w,i])) :
    ∀ a b : List Bool, a.length = b.length → i < a.length → w < a.length →
      a.getD w false = true → b.getD w false = true →
      (∀ j, j ≠ i → a.getD j false = b.getD j false) →
      ∀ j, j ≠ i → (wiresFrom gs a).getD j false = (wiresFrom gs b).getD j false := by
  induction gs with
  | nil => intro a b hl hi hw haw hbw hab j hj; exact hab j hj
  | cons g gs ih =>
    intro a b hl hi hw haw hbw hab j hj
    have hv : g.op.eval (g.inputs.map fun k => a.getD k false) =
        g.op.eval (g.inputs.map fun k => b.getD k false) := by
      by_cases hr : i ∈ (normGate g).inputs
      · obtain ⟨hop,hin⟩ := hshape g List.mem_cons_self hr
        rcases hin with hin | hin <;> simp only [hop,hin,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq, haw,hbw,Bool.or_true,Bool.true_or,Bool.or_false]
      · rw [← normGate_eval g, ← normGate_eval g]
        congr 1
        apply List.map_congr_left
        intro k hk
        exact hab k (fun he => hr (he ▸ hk))
    change (wiresFrom gs (a ++ [g.op.eval (g.inputs.map fun k => a.getD k false)])).getD j false =
      (wiresFrom gs (b ++ [g.op.eval (g.inputs.map fun k => b.getD k false)])).getD j false
    rw [hv]
    apply ih (fun g hg => hok g (List.mem_cons_of_mem _ hg))
      (fun g hg => hshape g (List.mem_cons_of_mem _ hg)) _ _ (by simp [hl])
      (by simp; omega) (by simp; omega)
    · rw [List.getD_append _ _ _ _ hw]; exact haw
    · rw [List.getD_append _ _ _ _ (by omega)]; exact hbw
    · intro k hk
      by_cases he : k = a.length
      · subst k
        rw [getD_snoc_eq, hl, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ he, getD_snoc_ne _ _ _ _ (by omega)]
        exact hab k hk
    · exact hj

lemma input_get (x : Fin 9 → Bool) (j : Fin 9) :
    (List.ofFn x).getD j.val false = x j := by
  rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getElem_ofFn]

lemma insert_off (i : Fin 9) (y : Fin 8 → Bool) (j : ℕ) (hji : j ≠ i.val) :
    ((List.ofFn y).insertIdx i.val false).getD j false =
      ((List.ofFn y).insertIdx i.val true).getD j false := by
  rw [← insert_list, ← insert_list]
  by_cases hj : j < 9
  · rw [input_get _ ⟨j,hj⟩, input_get _ ⟨j,hj⟩]
    have hne : (⟨j,hj⟩ : Fin 9) ≠ i := fun e => hji (congrArg Fin.val e)
    obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hne
    rw [← hk]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]



lemma solve : have x1 : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) => (if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs).contains ↑x1; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x2 →     have x5 : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (x5 : Bool) (x6 : Fin (8 : ℕ) → Bool) => x2.eval ((List.ofFn x6).insertIdx (↑x3) x5);     (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x5 Bool.false x6 ≠ x5 Bool.false x7) → (∀ (x7 : Fin (9 : ℕ)), x7 ≠ x3 → ∃ (x9 : Fin (8 : ℕ) → Bool), x5 Bool.false x9 ≠ x5 Bool.true x9 ∧ ((List.ofFn x9).insertIdx (↑x3) Bool.false).getD (↑x7) Bool.false = Bool.true) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (2 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x8 = x5 Bool.false) ∨ ∃ (x8 : Fin x2.size) (x9 : ℕ), (9 : ℕ) ≤ x9 ∧ x9 < (9 : ℕ) + ↑x8 ∧ (x2.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x2.gates.get x8).inputs = [↑x3, x9] ∨ (x2.gates.get x8).inputs = [x9, ↑x3]) ∧ ∀ (x10 : Fin x2.size), x1 x3 (x2.gates.get x10) = Bool.true → x10 = x8 := by
  classical
  dsimp only
  intro C i hmin hnc hsens
  by_cases hsave : ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
      circuitFun 8 D = (fun y => C.eval ((List.ofFn y).insertIdx i.val false))
  · exact Or.inl hsave
  right
  have hchoose : ∀ i : Fin 9, ∃ p : Fin 9, p ≠ i := by decide +kernel
  obtain ⟨k,hki⟩ := hchoose i
  obtain ⟨y,hy,_⟩ := hsens k hki
  have hdep : ∃ y : Fin 8 → Bool, C.eval ((List.ofFn y).insertIdx i.val false) ≠ C.eval ((List.ofFn y).insertIdx i.val true) := ⟨y,hy⟩
  have htight : ∀ s, HasCircuitSize 8 (fun y => C.eval ((List.ofFn y).insertIdx i.val false)) s → C.size ≤ s+1 := by
    intro s hs
    obtain ⟨D,hD,hDs,hDf⟩ := hs
    by_contra hn
    apply hsave
    exact ⟨D,hD,by omega,funext hDf⟩
  obtain ⟨p,w,hp,huniq,hop,hins,hne,hlt⟩ := unique_or C i hmin hdep hnc htight
  have hgate : gateAt C p.val = C.gates.get p := gateAt_eq_getElem p.isLt
  have hge : 9 ≤ w := by
    by_contra hn
    have hw : w < 9 := by omega
    let k : Fin 9 := ⟨w,hw⟩
    have hki : k ≠ i := fun e => hne (congrArg Fin.val e)
    obtain ⟨y,hy,hwy⟩ := hsens k hki
    have hshape : ∀ g ∈ C.gates, i.val ∈ (normGate g).inputs →
        g.op = GateOp.or ∧ (g.inputs = [i.val,w] ∨ g.inputs = [w,i.val]) := by
      intro g hg hr
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
      rw [← hj] at hr ⊢
      have hr' : readsEff C i.val j := (norm_read_eff _ _ (hmin.1 _ (List.get_mem _ _))).mp hr
      have hjp := huniq j hr'
      subst j
      simpa only [hgate] using And.intro hop hins
    have ho : C.output ≠ i.val := by
      intro he
      have hc (z : Fin 8 → Bool) : C.eval ((List.ofFn z).insertIdx i.val false) = false := by
        rw [← insert_list]
        change (wiresFrom C.gates (List.ofFn (Fin.insertNth i false z))).getD C.output false = false
        rw [he, getD_wiresFrom _ _ _ (by simp [i.isLt]), input_get]
        simp
      obtain ⟨z,z',hz⟩ := hnc
      exact hz ((hc z).trans (hc z').symm)
    let a := (List.ofFn y).insertIdx i.val false
    let b := (List.ofFn y).insertIdx i.val true
    have ha : a.length = 9 := by dsimp [a]; rw [← insert_list]; simp
    have hb : b.length = 9 := by dsimp [b]; rw [← insert_list]; simp
    have haw : a.getD w false = true := hwy
    have hbw : b.getD w false = true := (insert_off i y w hne).symm.trans haw
    have hf := fold_block C.gates i.val w hmin.1 hshape a b (ha.trans hb.symm)
      (by rw [ha]; exact i.isLt) (by rw [ha]; exact hw) haw hbw
      (insert_off i y) C.output ho
    exact hy hf
  refine ⟨p,w,hge,hlt,?_,?_,?_⟩
  · simpa only [hgate] using hop
  · simpa only [hgate] using hins
  · intro j hj
    apply huniq
    apply (norm_read_eff _ _ (hmin.1 _ (List.get_mem _ _))).mp
    exact (rb_norm _ _ (hmin.1 _ (List.get_mem _ _))).mp hj

end PEqualNP.Outside.L_meta_2822_aux.Proof

theorem PEqualNP.Outside.L_meta_2822 : have x1 : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) => (if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs).contains ↑x1; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x2 →     have x5 : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (x5 : Bool) (x6 : Fin (8 : ℕ) → Bool) => x2.eval ((List.ofFn x6).insertIdx (↑x3) x5);     (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x5 Bool.false x6 ≠ x5 Bool.false x7) → (∀ (x7 : Fin (9 : ℕ)), x7 ≠ x3 → ∃ (x9 : Fin (8 : ℕ) → Bool), x5 Bool.false x9 ≠ x5 Bool.true x9 ∧ ((List.ofFn x9).insertIdx (↑x3) Bool.false).getD (↑x7) Bool.false = Bool.true) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (2 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x8 = x5 Bool.false) ∨ ∃ (x8 : Fin x2.size) (x9 : ℕ), (9 : ℕ) ≤ x9 ∧ x9 < (9 : ℕ) + ↑x8 ∧ (x2.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x2.gates.get x8).inputs = [↑x3, x9] ∨ (x2.gates.get x8).inputs = [x9, ↑x3]) ∧ ∀ (x10 : Fin x2.size), x1 x3 (x2.gates.get x10) = Bool.true → x10 = x8 := by
  exact PEqualNP.Outside.L_meta_2822_aux.Proof.solve
