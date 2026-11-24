import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4053

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def isOr (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem isOr_iff (g : Gate) : isOr g = true ↔ g.op = GateOp.or := by
  unfold isOr
  cases h : g.op <;> simp

abbrev En := List (Finset ℕ × Finset ℕ)

def cj (w : List Bool) (s : Finset ℕ) : Bool := decide (∀ x9 ∈ s, w.getD x9 false = true)

def erun (E : En) (x : List Bool) : List Bool :=
  E.foldl (fun (x7 : List Bool) (x8 : Finset ℕ × Finset ℕ) =>
    x7 ++ [decide (∀ x9 ∈ x8.1, x7.getD x9 false = true) ||
      decide (∀ x9 ∈ x8.2, x7.getD x9 false = true)]) x

theorem erun_snoc (E : En) (e : Finset ℕ × Finset ℕ) (x : List Bool) :
    erun (E ++ [e]) x = erun E x ++ [cj (erun E x) e.1 || cj (erun E x) e.2] := by
  simp [erun, cj, List.foldl_append]

theorem erun_length (E : En) (x : List Bool) : (erun E x).length = x.length + E.length := by
  induction E using List.reverseRecOn with
  | nil => simp [erun]
  | append_singleton E e ih => rw [erun_snoc]; simp [ih]; omega

theorem erun_keep (E : En) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (erun E x).getD i false = x.getD i false := by
  induction E using List.reverseRecOn with
  | nil => rfl
  | append_singleton E e ih => rw [erun_snoc, getD_snoc, erun_length, if_neg (by omega), ih]

theorem cj_snoc (w : List Bool) (b : Bool) (s : Finset ℕ) (h : ∀ i ∈ s, i < w.length) :
    cj (w ++ [b]) s = cj w s := by
  unfold cj
  refine decide_eq_decide.2 (forall₂_congr fun i hi => ?_)
  have := h i hi
  rw [getD_snoc, if_neg (by omega)]

theorem cj_one (w : List Bool) (i : ℕ) : cj w {i} = w.getD i false := by
  unfold cj
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · exact fun h => h i (Finset.mem_singleton_self i)
  · intro h k hk
    rw [Finset.mem_singleton.1 hk]; exact h

def inx {n : ℕ} (x : Fin n → Bool) : List Bool := List.ofFn x ++ [false]

theorem inx_len {n : ℕ} (x : Fin n → Bool) : (inx x).length = n + 1 := by simp [inx]

theorem inx_n {n : ℕ} (E : En) (x : Fin n → Bool) : cj (erun E (inx x)) {n} = false := by
  rw [cj_one, erun_keep _ _ _ (by rw [inx_len]; omega)]
  unfold inx
  rw [getD_snoc, if_pos (by simp)]

theorem build (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (E : En) (s : ℕ → Finset ℕ), E.length = gs.countP isOr ∧
      (∀ (k : ℕ) (hk : k < E.length), ∀ i ∈ E[k].1 ∪ E[k].2, i < n + 1 + k) ∧
      (∀ w, ∀ i ∈ s w, i < n + 1 + E.length) ∧
      ∀ (x : Fin n → Bool) (w : ℕ), (run gs (List.ofFn x)).getD w false =
        cj (erun E (inx x)) (s w) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], fun w => if w < n then {w} else {n}, by simp, fun k hk => by simp at hk, ?_, ?_⟩
    · intro w i hi
      dsimp only at hi
      split_ifs at hi with h
      · rw [Finset.mem_singleton.1 hi]; simp; omega
      · rw [Finset.mem_singleton.1 hi]; simp
    · intro x w
      beta_reduce
      split_ifs with h
      · rw [cj_one]
        change (List.ofFn x).getD w false = (inx x).getD w false
        unfold inx
        rw [getD_snoc, if_neg (by simp; omega)]
      · rw [inx_n]
        exact List.getD_eq_default _ _ (by change (List.ofFn x).length ≤ w; rw [List.length_ofFn]; omega)
  | append_singleton gs g ih =>
    obtain ⟨E, s, h1, h2, h3, h4⟩ := ih fun g' h => hg g' (by simp [h])
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    have hval : ∀ (x : Fin n → Bool) (w : ℕ), (run (gs ++ [g]) (List.ofFn x)).getD w false =
        if w = n + gs.length then g.op.eval (g.inputs.map fun i => cj (erun E (inx x)) (s i))
        else cj (erun E (inx x)) (s w) := by
      intro x w
      rw [run_snoc, getD_snoc, run_length, List.length_ofFn]
      split_ifs
      · congr 1
        exact List.map_congr_left fun i _ => h4 x i
      · exact h4 x w
    rcases hop with ho | ho
    · refine ⟨E, fun w => if w = n + gs.length then g.inputs.toFinset.biUnion s else s w, ?_, h2,
        ?_, ?_⟩
      · have e : isOr g = false := by simp [isOr, ho]
        rw [List.countP_append, List.countP_singleton, h1, e]
        simp
      · intro w i hi
        dsimp only at hi
        split_ifs at hi
        · obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 hi
          exact h3 a i ha
        · exact h3 w i hi
      · intro x w
        rw [hval]
        dsimp only
        split_ifs
        · rw [ho, Bool.eq_iff_iff]
          simp only [GateOp.eval, cj, decide_eq_true_eq, List.all_map, List.all_eq_true,
            Function.comp_apply, id_eq, Finset.mem_biUnion, List.mem_toFinset]
          constructor
          · rintro h i ⟨a, ha, hi⟩
            exact h a ha i hi
          · intro h a ha i hi
            exact h i ⟨a, ha, hi⟩
        · rfl
    · have fin : ∀ A B : Finset ℕ, (∀ i ∈ A ∪ B, i < n + 1 + E.length) →
          (∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun i => cj (erun E (inx x)) (s i)) =
            (cj (erun E (inx x)) A || cj (erun E (inx x)) B)) →
          ∃ (E : En) (s : ℕ → Finset ℕ),
            E.length = (gs ++ [g]).countP isOr ∧
            (∀ (k : ℕ) (hk : k < E.length), ∀ i ∈ E[k].1 ∪ E[k].2, i < n + 1 + k) ∧
            (∀ w, ∀ i ∈ s w, i < n + 1 + E.length) ∧
            ∀ (x : Fin n → Bool) (w : ℕ), (run (gs ++ [g]) (List.ofFn x)).getD w false =
              cj (erun E (inx x)) (s w) := by
        intro A B hAB hv
        refine ⟨E ++ [(A, B)], fun w => if w = n + gs.length then {n + 1 + E.length} else s w,
          ?_, ?_, ?_, ?_⟩
        · rw [List.countP_append, List.countP_singleton, List.length_append, h1, (isOr_iff g).2 ho]
          simp
        · intro k hk i hi
          rcases Nat.lt_or_ge k E.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact h2 k h i hi
          · have hkk : k = E.length := by simp at hk; omega
            subst hkk
            simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero] at hi
            exact hAB i hi
        · intro w i hi
          dsimp only at hi
          rw [List.length_append, List.length_singleton]
          split_ifs at hi
          · rw [Finset.mem_singleton.1 hi]; omega
          · have := h3 w i hi; omega
        · intro x w
          rw [hval]
          dsimp only
          split_ifs
          · rw [cj_one, erun_snoc, getD_snoc, erun_length, inx_len, if_pos rfl]
            exact hv x
          · rw [erun_snoc, cj_snoc _ _ _ (by
              intro i hi; rw [erun_length, inx_len]; exact h3 w i hi)]
      obtain ⟨o, I⟩ := g
      simp only at ho hlen hval fin ⊢
      subst ho
      match I, hlen with
      | [], _ =>
        refine fin {n} {n} (fun i hi => ?_) fun x => ?_
        · rw [Finset.union_self] at hi; rw [Finset.mem_singleton.1 hi]; omega
        · rw [inx_n]; rfl
      | [a], _ =>
        refine fin (s a) {n} (fun i hi => ?_) fun x => ?_
        · rcases Finset.mem_union.1 hi with h | h
          · exact h3 a i h
          · rw [Finset.mem_singleton.1 h]; omega
        · rw [inx_n]; simp [GateOp.eval]
      | [a, b], _ =>
        refine fin (s a) (s b) (fun i hi => ?_) fun x => ?_
        · rcases Finset.mem_union.1 hi with h | h
          · exact h3 a i h
          · exact h3 b i h
        · simp [GateOp.eval]

theorem card_count (l : List Gate) (p : Gate → Prop) [DecidablePred p] :
    Fintype.card { i : Fin l.length // p (l.get i) } = l.countP (fun g => decide (p g)) := by
  rw [Fintype.card_subtype, Finset.card_filter]
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [List.countP_cons, ← ih]
    change (∑ i : Fin (l.length + 1), if p ((g :: l).get i) then 1 else 0) = _
    rw [Fin.sum_univ_succ, Nat.add_comm]
    congr 1
    by_cases h : p g <;> simp [h]

end PEqualNP.Outside.L_meta_4053

theorem PEqualNP.Outside.L_meta_4053 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     ∃ (x4 : List (Finset ℕ × Finset ℕ)) (x5 : Finset ℕ),       x4.length = {x6 : Fin x2.gates.length | (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧         (∀ (x6 : ℕ) (x7 : x6 < x4.length), ∀ x8 ∈ x4[x6].1 ∪ x4[x6].2, x8 < x1 + (1 : ℕ) + x6) ∧           (∀ x6 ∈ x5, x6 < x1 + (1 : ℕ) + x4.length) ∧             ∀ (x6 : Fin x1 → Bool),               x2.eval (List.ofFn x6) =                 have x7 : List Bool := List.foldl (fun (x7 : List Bool) (x8 : Finset ℕ × Finset ℕ) => x7 ++ [Decidable.decide (∀ x9 ∈ x8.1, x7.getD x9 Bool.false = Bool.true) || Decidable.decide (∀ x9 ∈ x8.2, x7.getD x9 Bool.false = Bool.true)]) (List.ofFn x6 ++ [Bool.false]) x4;                 Decidable.decide (∀ x8 ∈ x5, x7.getD x8 Bool.false = Bool.true) := by
  intro n C hm
  obtain ⟨E, s, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_meta_4053.build n C.gates (fun g hg => by
    obtain ⟨a, b⟩ := hm g hg
    exact ⟨by simpa using a, b⟩)
  refine ⟨E, s C.output, ?_, h2, h3 C.output, fun x => h4 x C.output⟩
  have hset : {x6 : Fin C.gates.length | (C.gates.get x6).op =
      PEqualNP.CircuitLowerBounds.GateOp.or} = {x6 : Fin C.gates.length |
      PEqualNP.Outside.L_meta_4053.isOr (C.gates.get x6) = true} := by
    ext i
    exact (PEqualNP.Outside.L_meta_4053.isOr_iff _).symm
  have hc := PEqualNP.Outside.L_meta_4053.card_count C.gates fun g => PEqualNP.Outside.L_meta_4053.isOr g = true
  rw [hset, h1, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  refine Eq.trans ?_ (hc.symm.trans ?_)
  · congr 1
  · exact Fintype.card_congr (Equiv.refl _)
