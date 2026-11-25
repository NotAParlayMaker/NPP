import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8784_aux

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gL {V l : List Bool} {i : ℕ} (h : i < V.length) :
    (V ++ l).getD i false = V.getD i false := List.getD_append _ _ _ _ h

theorem fold_pre (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl stp w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (stp w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      simp only [List.foldl_cons]; rw [ht]; simp [stp]⟩

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stp w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons]; rw [ih]; simp [stp]; omega

theorem fconst (W : List Bool) (gs : List Gate) (h : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < W.length) :
    ∀ p, gs.foldl stp (W ++ p) =
      W ++ p ++ gs.map (fun g => g.op.eval (g.inputs.map fun i => W.getD i false)) := by
  induction gs with
  | nil => intro p; simp
  | cons g gs ih =>
    intro p
    have e : g.inputs.map (fun i => (W ++ p).getD i false) = g.inputs.map (fun i => W.getD i false) :=
      List.map_congr_left (fun i hi => gL (h g (by simp) i hi))
    simp only [List.foldl_cons, stp, e, List.append_assoc]
    rw [ih (fun g hg => h g (by simp [hg])) (p ++ _)]
    simp

def rho (x1 x2 k : ℕ) : ℕ := if k < x1 then k else if k < x1 + x1 then k + x2 else k + 2 * x2

def re (x1 x2 : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho x1 x2)⟩

theorem frel (x1 x2 : ℕ) (gs : List Gate) : ∀ (W w : List Bool), W.length = w.length + 2 * x2 →
    x1 + x1 + x2 ≤ w.length → (∀ k, W[rho x1 x2 k]? = w[k]?) →
    (∀ k, ((gs.map (re x1 x2)).foldl stp W)[rho x1 x2 k]? = (gs.foldl stp w)[k]?) := by
  induction gs with
  | nil => intro W w _ _ h; simpa using h
  | cons g gs ih =>
    intro W w hl hn h
    simp only [List.map_cons, List.foldl_cons]
    have e : (re x1 x2 g).inputs.map (fun i => W.getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      simp only [re, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, List.getD_eq_getElem?_getD, h]
    apply ih
    · simp only [stp, List.length_append, List.length_singleton]; omega
    · simp only [stp, List.length_append, List.length_singleton]; omega
    · intro k
      simp only [stp, e]
      have hop : (re x1 x2 g).op = g.op := rfl
      rw [hop]
      rcases lt_trichotomy k w.length with hk | hk | hk
      · have : rho x1 x2 k < W.length := by unfold rho; split_ifs <;> omega
        rw [List.getElem?_append_left this, List.getElem?_append_left hk, h]
      · subst hk
        have : rho x1 x2 w.length = W.length := by unfold rho; split_ifs <;> omega
        rw [this]; simp
      · have : W.length < rho x1 x2 k := by unfold rho; split_ifs <;> omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

def accW (B a : ℕ) : ℕ → ℕ
  | 0 => a
  | i + 1 => B + 3 * i + 2

def blk (B a : ℕ) (p q r : ℕ → ℕ) (i : ℕ) : List Gate :=
  [⟨GateOp.or, [p i, q i]⟩, ⟨GateOp.and, [r i, B + 3 * i]⟩, ⟨GateOp.or, [accW B a i, B + 3 * i + 1]⟩]

def T (B a : ℕ) (p q r : ℕ → ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => T B a p q r k ++ blk B a p q r k

theorem T_len (B a : ℕ) (p q r : ℕ → ℕ) (k : ℕ) : (T B a p q r k).length = 3 * k := by
  induction k with
  | zero => simp [T]
  | succ k ih => simp [T, blk, ih]; omega

theorem T_ok (B a : ℕ) (p q r : ℕ → ℕ) (k : ℕ) :
    ∀ g ∈ T B a p q r k, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction k with
  | zero => simp [T]
  | succ k ih =>
    intro g hg
    simp only [T, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · simp [blk] at hg
      rcases hg with rfl | rfl | rfl <;> simp

def RB (n : ℕ) (gs : List Gate) : Prop := ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j

theorem rb_app {n : ℕ} {a b : List Gate} (ha : RB n a) (hb : RB (n + a.length) b) : RB n (a ++ b) := by
  intro j hj i hi
  by_cases h : j < a.length
  · rw [List.getElem_append_left h] at hi; exact ha j h i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have := hb (j - a.length) (by simp at hj; omega) i hi
    omega

theorem rb_iff (n : ℕ) (C : Circuit) : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ↔ RB n C.gates := by
  constructor
  · intro h j hj i hi
    have := h j hj i
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at this
    rw [List.getD_eq_getElem _ _ hj] at this
    exact this hi
  · intro h j hj i hi
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    exact h j hj i hi

theorem accW_lt (B a k : ℕ) (ha : a < B) : accW B a k < B + 3 * k := by
  cases k <;> simp [accW] <;> omega

theorem T_rb (B a : ℕ) (p q r : ℕ → ℕ) (ha : a < B) : ∀ k, (∀ i < k, p i < B ∧ q i < B ∧ r i < B) →
    RB B (T B a p q r k) := by
  intro k
  induction k with
  | zero => intro _ j hj; simp [T] at hj
  | succ k ih =>
    intro hp
    apply rb_app (ih (fun i hi => hp i (by omega)))
    rw [T_len]
    obtain ⟨h1, h2, h3⟩ := hp k (by omega)
    have hacc := accW_lt B a k ha
    intro j hj i hi
    simp [blk] at hj
    interval_cases j <;> simp [blk] at hi <;> omega

theorem chain (W : List Bool) (B a : ℕ) (p q r : ℕ → ℕ) (hW : W.length = B) (ha : a < B) :
    ∀ k, (∀ i < k, p i < B ∧ q i < B ∧ r i < B) →
    ((T B a p q r k).foldl stp W).getD (accW B a k) false = (W.getD a false ||
      (List.range k).any fun i => W.getD (r i) false && (W.getD (p i) false || W.getD (q i) false)) := by
  intro k
  induction k with
  | zero => intro _; simp [T, accW]
  | succ k ih =>
    intro hp
    have hv := ih (fun i hi => hp i (by omega))
    obtain ⟨h1, h2, h3⟩ := hp k (by omega)
    have hacc := accW_lt B a k ha
    have hVl : ((T B a p q r k).foldl stp W).length = B + 3 * k := by rw [fold_len, T_len]; omega
    obtain ⟨t, ht⟩ := fold_pre (T B a p q r k) W
    have hpre : ∀ i < B, ((T B a p q r k).foldl stp W).getD i false = W.getD i false := by
      intro i hi; rw [ht]; exact gL (by omega)
    rw [show T B a p q r (k + 1) = T B a p q r k ++ blk B a p q r k from rfl, List.foldl_append]
    generalize (T B a p q r k).foldl stp W = V at hv hVl hpre
    have e1 := hpre (p k) h1
    have e2 := hpre (q k) h2
    have e3 := hpre (r k) h3
    rw [show accW B a (k + 1) = B + 3 * k + 2 from rfl]
    simp only [blk, List.foldl_cons, List.foldl_nil, stp, List.map_cons, List.map_nil]
    rw [List.range_succ, List.any_append, ← Bool.or_assoc, ← hv, List.any_cons, List.any_nil,
      Bool.or_false, ← e1, ← e2, ← e3]
    generalize accW B a k = c at hacc
    rw [show B + 3 * k = V.length by omega] at hacc ⊢
    have h1' : p k < V.length := by omega
    have h2' : q k < V.length := by omega
    have h3' : r k < V.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hacc, h1', h2', h3',
      GateOp.eval]

end PEqualNP.Outside.L_meta_8784_aux

open PEqualNP.Outside.L_meta_8784_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8784 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x2 → Fin x1) (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1 + x2) x5 → x5.output < x1 + x1 + x2 + x5.size → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2 + (x1 + x2)) x8 ∧ x8.size ≤ x5.size + (4 : ℕ) * x2 ∧ ∀ (x9 x10 : Fin (x1 + x2) → Bool), x8.eval (List.ofFn x9 ++ List.ofFn x10) = (x5.eval (((List.ofFn fun (x11 : Fin x1) => x9 (Fin.castAdd x2 x11)) ++ List.ofFn fun (x11 : Fin x1) => x10 (Fin.castAdd x2 x11)) ++ List.ofFn fun (x11 : Fin x2) => x10 (Fin.castAdd x2 (x3 x11)) || x10 (Fin.castAdd x2 (x4 x11))) || (List.finRange x2).any fun (x11 : Fin x2) => x9 (Fin.natAdd x1 x11) && (x10 (Fin.castAdd x2 (x3 x11)) || x10 (Fin.castAdd x2 (x4 x11)) || x10 (Fin.natAdd x1 x11))) := by
  intro x1 x2 x3 x4 x5 hAO hout
  obtain ⟨hand, hrb, h2⟩ := hAO
  rw [rb_iff] at hrb
  have hs : x5.size = x5.gates.length := rfl
  let a := rho x1 x2 x5.output
  let B := x1 + x2 + (x1 + x2) + x2 + x5.size
  let H : List Gate := List.ofFn (fun i : Fin x2 =>
    (⟨GateOp.or, [x1 + x2 + (x3 i).val, x1 + x2 + (x4 i).val]⟩ : Gate))
  let O := x5.gates.map (re x1 x2)
  let TT := T B a (fun i => x1 + x2 + (x1 + x2) + i) (fun i => x1 + x2 + x1 + i) (fun i => x1 + i) x2
  have ha : a < B := by simp only [a, B, rho]; split_ifs <;> omega
  have hpq : ∀ i < x2, x1 + x2 + (x1 + x2) + i < B ∧ x1 + x2 + x1 + i < B ∧ x1 + i < B := by
    intro i hi; simp only [B]; omega
  have hTT := T_rb B a _ _ _ ha x2 hpq
  have hHl : H.length = x2 := by simp [H]
  have hOl : O.length = x5.size := by simp [O, hs]
  refine ⟨⟨H ++ O ++ TT, accW B a x2⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · simp [H] at hg; obtain ⟨i, rfl⟩ := hg; simp
    · simp only [O, List.mem_map] at hg; obtain ⟨g0, hg0, rfl⟩ := hg; exact hand g0 hg0
    · exact (T_ok _ _ _ _ _ _ g hg).1
  · rw [rb_iff]
    apply rb_app (rb_app ?_ ?_)
    · simp only [List.length_append, hHl, hOl]
      convert hTT using 1
      simp only [B]; omega
    · intro j hj i hi
      simp [H] at hj hi
      have := (x3 ⟨j, hj⟩).isLt
      have := (x4 ⟨j, hj⟩).isLt
      rcases hi with rfl | rfl <;> omega
    · intro j hj i hi
      rw [hHl]
      have hj' : j < x5.gates.length := by simpa [O] using hj
      simp only [O, List.getElem_map, re, List.mem_map] at hi
      obtain ⟨b, hb, rfl⟩ := hi
      have := hrb j hj' b hb
      unfold rho; split_ifs <;> omega
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · simp [H] at hg; obtain ⟨i, rfl⟩ := hg; simp
    · simp only [O, List.mem_map] at hg; obtain ⟨g0, hg0, rfl⟩ := hg; simpa [re] using h2 g0 hg0
    · exact (T_ok _ _ _ _ _ _ g hg).2
  · simp only [Circuit.size, List.length_append, hHl, hOl, TT, T_len]; omega
  · intro x9 x10
    have hw : ∀ (C : Circuit) (x : List Bool), C.wires x = C.gates.foldl stp x := fun _ _ => rfl
    unfold Circuit.eval
    rw [hw, hw]
    dsimp only
    rw [List.foldl_append, List.foldl_append]
    have hLl : (List.ofFn x9 ++ List.ofFn x10).length = x1 + x2 + (x1 + x2) := by simp
    have hLv : ∀ j, (List.ofFn x9 ++ List.ofFn x10).getD j false = if h : j < x1 + x2 then x9 ⟨j, h⟩
        else if h2 : j < x1 + x2 + (x1 + x2) then x10 ⟨j - (x1 + x2), by omega⟩ else false := by
      intro j
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_ofFn]
      split_ifs <;> simp_all <;> omega
    let hv := List.ofFn (fun i : Fin x2 => x10 (Fin.castAdd x2 (x3 i)) || x10 (Fin.castAdd x2 (x4 i)))
    have hH0 : H.foldl stp (List.ofFn x9 ++ List.ofFn x10) = (List.ofFn x9 ++ List.ofFn x10) ++ hv := by
      have := fconst (List.ofFn x9 ++ List.ofFn x10) H (by
        intro g hg i hi
        simp [H] at hg
        obtain ⟨j, rfl⟩ := hg
        have := (x3 j).isLt
        have := (x4 j).isLt
        simp at hi
        rcases hi with rfl | rfl <;> omega) []
      simp only [List.append_nil] at this
      rw [this]
      congr 1
      simp only [H, hv, List.map_ofFn]
      congr 1
      funext i
      have := (x3 i).isLt
      have := (x4 i).isLt
      simp only [Function.comp, GateOp.eval, hLv]
      simp [show x1 + x2 + (x3 i).val < x1 + x2 + (x1 + x2) by omega, show x1 + x2 + (x4 i).val < x1 + x2 + (x1 + x2) by omega, Fin.castAdd]
      rfl
    rw [hH0]
    have hrel0 : ∀ k, ((List.ofFn x9 ++ List.ofFn x10) ++ hv)[rho x1 x2 k]? =
        (((List.ofFn fun (x11 : Fin x1) => x9 (Fin.castAdd x2 x11)) ++ List.ofFn fun (x11 : Fin x1) => x10 (Fin.castAdd x2 x11)) ++ List.ofFn fun (x11 : Fin x2) => x10 (Fin.castAdd x2 (x3 x11)) || x10 (Fin.castAdd x2 (x4 x11)))[k]? := by
      intro k
      simp only [hv, rho]
      simp [List.getElem?_append, List.getElem?_ofFn]
      repeat' split
      all_goals (try omega)
      all_goals (try simp only [Option.some.injEq])
      all_goals first | rfl | (congr 1; ext; simp; omega) | (congr 1 <;> congr 3 <;> ext <;> simp <;> omega)
    have hrel := frel x1 x2 x5.gates _ _ (by simp [hv]; omega) (by simp; omega) hrel0
    obtain ⟨t, ht⟩ := fold_pre O ((List.ofFn x9 ++ List.ofFn x10) ++ hv)
    have hW1l : (O.foldl stp ((List.ofFn x9 ++ List.ofFn x10) ++ hv)).length = B := by
      rw [fold_len]; simp [hv, hOl, B]; omega
    rw [chain _ B a _ _ _ hW1l ha x2 hpq]
    congr 1
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      exact congrArg (fun o => Option.getD o false) (hrel x5.output)
    · have pt : ∀ i (hi : i < x2),
          ((O.foldl stp ((List.ofFn x9 ++ List.ofFn x10) ++ hv)).getD (x1 + i) false &&
            ((O.foldl stp ((List.ofFn x9 ++ List.ofFn x10) ++ hv)).getD (x1 + x2 + (x1 + x2) + i) false ||
              (O.foldl stp ((List.ofFn x9 ++ List.ofFn x10) ++ hv)).getD (x1 + x2 + x1 + i) false)) =
          (x9 (Fin.natAdd x1 ⟨i, hi⟩) && (x10 (Fin.castAdd x2 (x3 ⟨i, hi⟩)) ||
            x10 (Fin.castAdd x2 (x4 ⟨i, hi⟩)) || x10 (Fin.natAdd x1 ⟨i, hi⟩))) := by
        intro i hi
        rw [ht]
        have hl0 : (List.ofFn x9 ++ List.ofFn x10 ++ hv).length = x1 + x2 + (x1 + x2) + x2 := by
          simp [hv]; omega
        have v1 : (List.ofFn x9 ++ List.ofFn x10 ++ hv ++ t).getD (x1 + i) false = x9 (Fin.natAdd x1 ⟨i, hi⟩) := by
          rw [gL (by omega), gL (by simp; omega), hLv]
          simp [show x1 + i < x1 + x2 by omega, Fin.natAdd]
        have v2 : (List.ofFn x9 ++ List.ofFn x10 ++ hv ++ t).getD (x1 + x2 + (x1 + x2) + i) false =
            (x10 (Fin.castAdd x2 (x3 ⟨i, hi⟩)) || x10 (Fin.castAdd x2 (x4 ⟨i, hi⟩))) := by
          rw [gL (by omega), List.getD_append_right _ _ _ _ (by simp)]
          simp [hv, hi]
        have v3 : (List.ofFn x9 ++ List.ofFn x10 ++ hv ++ t).getD (x1 + x2 + x1 + i) false = x10 (Fin.natAdd x1 ⟨i, hi⟩) := by
          rw [gL (by omega), gL (by simp; omega), hLv]
          simp [show ¬ x1 + x2 + x1 + i < x1 + x2 by omega,
            show x1 + x2 + x1 + i < x1 + x2 + (x1 + x2) by omega, Fin.natAdd]
          congr 1; ext; simp; omega
        rw [v1, v2, v3]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, List.mem_range, List.mem_finRange, true_and]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨⟨i, hi⟩, by rw [← pt i hi]; exact h⟩
      · rintro ⟨⟨i, hi⟩, h⟩
        exact ⟨i, hi, by rw [pt i hi]; exact h⟩
