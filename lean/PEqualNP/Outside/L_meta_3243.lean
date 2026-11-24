import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3243_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One gate appended to the wire values.
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  have h' : i < (List.ofFn f).length := by simpa using h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h', Option.getD_some, List.getElem_ofFn]

theorem getD_ofFn_ge {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : n ≤ i) :
    (List.ofFn f).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
  rfl

theorem length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

theorem prefix_fold (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    unfold stepW
    rw [getD_snoc, if_pos hi]

theorem last_step (w : List Bool) (g : Gate) :
    (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold stepW
  rw [getD_snoc, if_neg (lt_irrefl _), if_pos rfl]


theorem prefix_step (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepW w g).getD i false = w.getD i false := by
  unfold stepW
  rw [getD_snoc, if_pos hi]
theorem any_congr' {α : Type} (l : List α) (f g : α → Bool) (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.any_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

-- The OR gate number `i` of a block.
def orGate (B v1 : ℕ) (rest : List ℕ) (i : ℕ) : Gate :=
  ⟨GateOp.or, [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩

theorem acc_succ (B v1 K k : ℕ) (hk : k < K) :
    (v1 :: (List.range K).map (fun j => B + j)).getD (k + 1) 0 = B + k := by
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_range, hk]

theorem chain (B v1 : ℕ) (rest : List ℕ) (w : List Bool) (hB : w.length = B)
    (hv1 : v1 < B) (hr : ∀ r ∈ rest, r < B) :
    ∀ k, k ≤ rest.length →
      (((List.range k).map (orGate B v1 rest)).foldl stepW w).length = B + k ∧
      (((List.range k).map (orGate B v1 rest)).foldl stepW w).getD
        ((v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0) false =
        (v1 :: rest.take k).any (fun v => w.getD v false) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [hB]
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    constructor
    · simp [stepW, ih1]
      omega
    · rw [acc_succ B v1 rest.length k (by omega)]
      have hk' : k < rest.length := by omega
      rw [← ih1, last_step]
      simp only [orGate, List.map_cons, List.map_nil]
      rw [ih2, List.getD_eq_getElem _ _ hk',
        prefix_fold _ _ _ (by rw [hB]; exact hr _ (List.getElem_mem hk'))]
      rw [List.take_succ, List.getElem?_eq_getElem hk']
      simp only [Option.toList_some, GateOp.eval, List.any_cons, List.any_nil, List.any_append,
        Bool.or_false, id, Bool.or_assoc]

theorem blockGates_eq (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    blockGates B a t v1 rest lead = (List.range rest.length).map (orGate B v1 rest) ++
      ⟨GateOp.and, [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩ ::
      (if lead then [] else [⟨GateOp.or, [a, B + rest.length]⟩]) := rfl

theorem block_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  rw [blockGates_eq]
  cases lead <;> simp

theorem block_val (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (w : List Bool) (hB : w.length = B)
    (ha : lead = false → a < B) (ht : t < B) (hv1 : v1 < B) (hr : ∀ r ∈ rest, r < B) :
    ((blockGates B a t v1 rest lead).foldl stepW w).getD
        (B + (blockGates B a t v1 rest lead).length - 1) false =
      ((!lead && w.getD a false) ||
        (w.getD t false && (v1 :: rest).any (fun v => w.getD v false))) := by
  obtain ⟨c1, c2⟩ := chain B v1 rest w hB hv1 hr rest.length le_rfl
  rw [List.take_length] at c2
  rw [block_len, blockGates_eq, List.foldl_append]
  have hand : (stepW (((List.range rest.length).map (orGate B v1 rest)).foldl stepW w)
      ⟨GateOp.and, [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩).getD
        (B + rest.length) false =
      (w.getD t false && (v1 :: rest).any (fun v => w.getD v false)) := by
    rw [← c1, last_step]
    simp only [List.map_cons, List.map_nil]
    rw [c2, prefix_fold _ _ _ (by rw [hB]; exact ht)]
    simp [GateOp.eval]
  cases lead with
  | true =>
    simp only [if_true, List.foldl_cons, List.foldl_nil]
    rw [show B + (rest.length + 1 + 0) - 1 = B + rest.length by omega, hand]
    simp
  | false =>
    simp only [List.foldl_cons, List.foldl_nil, Bool.false_eq_true, if_false]
    have hlenA : (stepW (((List.range rest.length).map (orGate B v1 rest)).foldl stepW w)
      ⟨GateOp.and, [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩).length =
        B + rest.length + 1 := by
      simp [stepW, c1]
    rw [show B + (rest.length + 1 + 1) - 1 = B + rest.length + 1 by omega, ← hlenA, last_step]
    simp only [List.map_cons, List.map_nil]
    have haB : a < B := ha rfl
    rw [hand, prefix_step _ _ _ (by rw [c1]; omega),
      prefix_fold _ _ _ (by rw [hB]; exact haB)]
    simp [GateOp.eval]

theorem cover_len (own : List (ℕ × List ℕ)) (hne : ∀ e ∈ own, e.2 ≠ []) :
    ∀ (B : ℕ) (lead : Bool) (a : ℕ),
      (coverGatesB B lead a own).length + (if lead = true ∧ own ≠ [] then 1 else 0) =
        (own.map (fun e => e.2.length)).sum + own.length := by
  induction own with
  | nil => intro B lead a; simp [coverGatesB]
  | cons e os ih =>
    intro B lead a
    obtain ⟨t, l⟩ := e
    cases l with
    | nil => exact absurd rfl (hne (t, []) (by simp))
    | cons v1 rest =>
      have ih' := ih (fun e he => hne e (by simp [he]))
      simp only [coverGatesB, List.length_append]
      have h2 := ih' (B + (blockGates B a t v1 rest lead).length) false
        (B + (blockGates B a t v1 rest lead).length - 1)
      simp only [Bool.false_eq_true, false_and, if_false, Nat.add_zero] at h2
      rw [h2, block_len]
      cases lead <;> simp <;> omega

theorem len_le_sum (own : List (ℕ × List ℕ)) (hne : ∀ e ∈ own, e.2 ≠ []) :
    own.length ≤ (own.map (fun e => e.2.length)).sum := by
  induction own with
  | nil => simp
  | cons e os ih =>
    have h1 : e.2 ≠ [] := hne e (by simp)
    have h2 := ih (fun e he => hne e (by simp [he]))
    have h3 : 0 < e.2.length := List.length_pos_iff.mpr h1
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem cover_val (own : List (ℕ × List ℕ)) (hne : ∀ e ∈ own, e.2 ≠ []) :
    ∀ (B : ℕ) (lead : Bool) (a : ℕ) (w : List Bool), w.length = B → (lead = false → a < B) →
      (∀ e ∈ own, e.1 < B ∧ ∀ v ∈ e.2, v < B) → own ≠ [] →
      ((coverGatesB B lead a own).foldl stepW w).getD
          (B + (coverGatesB B lead a own).length - 1) false =
        ((!lead && w.getD a false) ||
          own.any (fun e => w.getD e.1 false && e.2.any (fun v => w.getD v false))) := by
  induction own with
  | nil => intro B lead a w _ _ _ h; exact absurd rfl h
  | cons e os ih =>
    intro B lead a w hB ha hb _
    obtain ⟨t, l⟩ := e
    cases l with
    | nil => exact absurd rfl (hne (t, []) (by simp))
    | cons v1 rest =>
      have hne' : ∀ e ∈ os, e.2 ≠ [] := fun e he => hne e (by simp [he])
      have hb' : ∀ e ∈ os, e.1 < B ∧ ∀ v ∈ e.2, v < B := fun e he => hb e (by simp [he])
      have ht : t < B := (hb (t, v1 :: rest) (by simp)).1
      have hv1 : v1 < B := (hb (t, v1 :: rest) (by simp)).2 v1 (by simp)
      have hr : ∀ r ∈ rest, r < B := fun r hr => (hb (t, v1 :: rest) (by simp)).2 r (by simp [hr])
      have hbv := block_val B a t v1 rest lead w hB ha ht hv1 hr
      simp only [coverGatesB, List.length_append, List.foldl_append]
      by_cases hos : os = []
      · subst hos
        simp only [coverGatesB, List.length_nil, Nat.add_zero, List.foldl_nil]
        rw [hbv]
        simp
      · have hG : 1 ≤ (blockGates B a t v1 rest lead).length := by
          rw [block_len]
          omega
        have hlenW1 : ((blockGates B a t v1 rest lead).foldl stepW w).length =
            B + (blockGates B a t v1 rest lead).length := by
          rw [length_fold, hB]
        have hpre : ∀ i < B, ((blockGates B a t v1 rest lead).foldl stepW w).getD i false =
            w.getD i false := fun i hi => prefix_fold _ _ _ (by omega)
        have hb'' : ∀ e ∈ os, e.1 < B + (blockGates B a t v1 rest lead).length ∧
            ∀ v ∈ e.2, v < B + (blockGates B a t v1 rest lead).length := by
          intro e he
          obtain ⟨h1, h2⟩ := hb' e he
          exact ⟨by omega, fun v hv => by have := h2 v hv; omega⟩
        have := ih hne' (B + (blockGates B a t v1 rest lead).length) false
          (B + (blockGates B a t v1 rest lead).length - 1)
          ((blockGates B a t v1 rest lead).foldl stepW w) hlenW1 (fun _ => by omega) hb'' hos
        rw [show B + ((blockGates B a t v1 rest lead).length +
            (coverGatesB (B + (blockGates B a t v1 rest lead).length) false
              (B + (blockGates B a t v1 rest lead).length - 1) os).length) - 1 =
            B + (blockGates B a t v1 rest lead).length +
            (coverGatesB (B + (blockGates B a t v1 rest lead).length) false
              (B + (blockGates B a t v1 rest lead).length - 1) os).length - 1 by omega]
        rw [this, hbv]
        have hany : os.any (fun e => ((blockGates B a t v1 rest lead).foldl stepW w).getD e.1 false &&
            e.2.any (fun v => ((blockGates B a t v1 rest lead).foldl stepW w).getD v false)) =
            os.any (fun e => w.getD e.1 false && e.2.any (fun v => w.getD v false)) := by
          apply any_congr'
          intro e he
          obtain ⟨h1, h2⟩ := hb' e he
          rw [hpre _ h1, any_congr' _ _ _ (fun v hv => hpre v (h2 v hv))]
        rw [hany]
        simp [Bool.or_assoc]

theorem main_aux : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) := by
  intro x1 x2 x3 x4 x5 n hown hchar C
  have hn : n = x1 + x2 := rfl
  have hne : ∀ e ∈ x5, e.2 ≠ [] := fun e he => (hown e he).1
  have hb : ∀ e ∈ x5, e.1 < n ∧ ∀ v ∈ e.2, v < n := by
    intro e he
    rcases (hown e he).2 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨by omega, fun v hv => (h2 v hv).2⟩
    · exact ⟨h2, fun v hv => by have := h3 v hv; omega⟩
  have hlen := cover_len x5 hne n true 0
  by_cases h5 : x5 = []
  · subst h5
    have hnone : ∀ (a : Fin x1) (b : Fin x2), ¬ x3 a b := fun a b h => by
      simpa using (hchar a b).mp h
    refine ⟨?_, ?_⟩
    · simp [C, coverCircuitB, coverGatesB, Circuit.size]
    · intro x
      have hl : PEqualNP.MetaComplexity.circuitFun n C x = false := by
        show (C.wires (List.ofFn x)).getD C.output false = false
        simp only [C, coverCircuitB, coverGatesB, if_true]
        exact getD_ofFn_ge x n le_rfl
      rw [hl]
      symm
      rw [decide_eq_false_iff_not]
      rintro ⟨a, b, h, _⟩
      exact hnone a b h
  · have hsum := len_le_sum x5 hne
    have hpos : 0 < x5.length := List.length_pos_iff.mpr h5
    simp only [h5, ne_eq, not_false_eq_true, and_self, if_true] at hlen
    have hG : coverGatesB n true 0 x5 ≠ [] := by
      intro h
      rw [h] at hlen
      simp only [List.length_nil] at hlen
      omega
    have hCe : C = ⟨coverGatesB n true 0 x5, n + (coverGatesB n true 0 x5).length - 1⟩ := by
      show coverCircuitB n x5 = _
      unfold coverCircuitB
      rw [if_neg hG]
    refine ⟨?_, ?_⟩
    · rw [hCe]
      show (coverGatesB n true 0 x5).length = _
      omega
    · intro x
      have hl : PEqualNP.MetaComplexity.circuitFun n C x =
          ((coverGatesB n true 0 x5).foldl stepW (List.ofFn x)).getD
            (n + (coverGatesB n true 0 x5).length - 1) false := by
        show (C.wires (List.ofFn x)).getD C.output false = _
        rw [hCe]
        rfl
      rw [hl, cover_val x5 hne n true 0 (List.ofFn x) (by simp) (fun h => absurd h (by simp)) hb h5]
      have hV : ∀ i (hi : i < n), (List.ofFn x).getD i false = x ⟨i, hi⟩ :=
        fun i hi => getD_ofFn x i hi
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_iff]
      simp only [Bool.not_true, Bool.false_and, Bool.false_or, List.any_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨e, he, het, v, hv, hvt⟩
        obtain ⟨h1, h2⟩ := hb e he
        have hvn := h2 v hv
        rcases (hown e he).2 with ⟨k1, k2⟩ | ⟨k1, k2, k3⟩
        · have kv := k2 v hv
          refine ⟨⟨e.1, k1⟩, ⟨v - x1, by omega⟩, (hchar _ _).mpr ⟨e, he, Or.inl ⟨rfl, ?_⟩⟩, ?_, ?_⟩
          · show x1 + (v - x1) ∈ e.2
            rw [show x1 + (v - x1) = v by omega]
            exact hv
          · rw [hV _ h1] at het
            exact het
          · rw [hV _ hvn] at hvt
            rw [← hvt]
            congr 1
            ext
            simp
            omega
        · have kv := k3 v hv
          refine ⟨⟨v, kv⟩, ⟨e.1 - x1, by omega⟩, (hchar _ _).mpr ⟨e, he, Or.inr ⟨?_, hv⟩⟩, ?_, ?_⟩
          · show e.1 = x1 + (e.1 - x1)
            omega
          · rw [hV _ hvn] at hvt
            exact hvt
          · rw [hV _ h1] at het
            rw [← het]
            congr 1
            ext
            simp
            omega
      · rintro ⟨a, b, hab, ha, hbt⟩
        obtain ⟨e, he, hcase⟩ := (hchar a b).mp hab
        have ha' : (List.ofFn x).getD a.val false = true := by
          rw [hV _ (by omega)]
          exact ha
        have hb' : (List.ofFn x).getD (x1 + b.val) false = true := by
          rw [hV _ (by omega)]
          exact hbt
        rcases hcase with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · exact ⟨e, he, by rw [k1]; exact ha', x1 + b.val, k2, hb'⟩
        · exact ⟨e, he, by rw [k1]; exact hb', a.val, k2, ha'⟩

end PEqualNP.Outside.L_meta_3243_aux

theorem PEqualNP.Outside.L_meta_3243 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) := by
  exact PEqualNP.Outside.L_meta_3243_aux.main_aux
