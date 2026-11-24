import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3517_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (x1 : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map x1⟩

def r (k : ℕ) : ℕ := if k < 4 then k else if k < 9 then k + 1 else if k = 9 then 12 else k + 4

lemma r_inj : Function.Injective r := by
  intro a b h
  unfold r at h
  split_ifs at h <;> omega

lemma r_lt (i j : ℕ) (h : i < 10 + j) : r i < 14 + j := by
  unfold r
  split_ifs <;> omega

lemma r_ge (k : ℕ) (h : 10 ≤ k) : r k = k + 4 := by
  unfold r
  split_ifs <;> omega

lemma fold_len (gs : List Gate) : ∀ (W : List Bool), (gs.foldl stepW W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma fold_pre (gs : List Gate) : ∀ (W : List Bool) (k : ℕ), k < W.length →
    (gs.foldl stepW W).getD k false = W.getD k false := by
  induction gs with
  | nil => intro W k _; rfl
  | cons g gs ih =>
    intro W k hk
    rw [List.foldl_cons, ih _ k (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hk

lemma step_inv (W Y : List Bool) (g : Gate) (hl : W.length = Y.length + 4)
    (hn : 10 ≤ Y.length)
    (hv : ∀ k, W.getD (r k) false = Y.getD k false) :
    ∀ k, (stepW W (reGate r g)).getD (r k) false = (stepW Y g).getD k false := by
  intro k
  have hm : (g.inputs.map r).map (fun i => W.getD i false)
      = g.inputs.map (fun i => Y.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hv i)
  show (W ++ [g.op.eval ((g.inputs.map r).map fun i => W.getD i false)]).getD (r k) false
    = (Y ++ [g.op.eval (g.inputs.map fun i => Y.getD i false)]).getD k false
  rw [hm]
  by_cases hk : k < Y.length
  · have hs : r k < W.length := by
      have := r_lt k (Y.length - 10) (by omega)
      omega
    rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ hk, hv k]
  · have hs : r k = k + 4 := r_ge k (by omega)
    rw [hs, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    congr 1
    omega

lemma fold_inv (gs : List Gate) :
    ∀ (W Y : List Bool), W.length = Y.length + 4 → 10 ≤ Y.length →
    (∀ k, W.getD (r k) false = Y.getD k false) →
    ∀ k, ((gs.map (reGate r)).foldl stepW W).getD (r k) false = (gs.foldl stepW Y).getD k false := by
  induction gs with
  | nil => intro W Y _ _ hv; exact hv
  | cons g gs ih =>
    intro W Y hl hn hv
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_ ?_ (step_inv W Y g hl hn hv)
    · simp [stepW, hl]
    · simp [stepW]; omega

lemma base (x5 : Fin 14 → Bool) (k : ℕ) :
    (List.ofFn x5).getD (r k) false = (List.ofFn fun (x6 : Fin 10) => x5 ([(0 : Fin 14), 1, 2, 3, 5, 6, 7, 8, 9, 12].getD ↑x6 0)).getD k false := by
  by_cases hk : k < 10
  · interval_cases k <;> simp [r, List.getD_eq_getElem?_getD]
  · rw [r_ge k (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def tailG (L p : ℕ) : List Gate :=
  [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [L, 5]⟩, ⟨GateOp.and, [L + 1, 10]⟩,
   ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [L + 3, 6]⟩, ⟨GateOp.and, [L + 4, 11]⟩,
   ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [L + 6, 4]⟩, ⟨GateOp.and, [L + 7, 13]⟩,
   ⟨GateOp.or, [L + 2, L + 5]⟩, ⟨GateOp.or, [L + 9, L + 8]⟩, ⟨GateOp.or, [p, L + 10]⟩]

def E (W : List Bool) : Bool :=
  ((W.getD 0 false || W.getD 4 false || W.getD 5 false) && W.getD 10 false)
  || ((W.getD 3 false || W.getD 4 false || W.getD 6 false) && W.getD 11 false)
  || ((W.getD 1 false || W.getD 2 false || W.getD 4 false) && W.getD 13 false)

lemma tail_ops (L p : ℕ) : ∀ g ∈ tailG L p, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  simp only [tailG, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma tail_nodup (L p : ℕ) (hL : 14 ≤ L) (hp : p ≠ L + 10) : ∀ g ∈ tailG L p, g.inputs.Nodup := by
  intro g hg
  simp only [tailG, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

lemma step0 (W : List Bool) (op : GateOp) (a b : ℕ) :
    stepW W ⟨op, [a, b]⟩ = W ++ [op.eval [W.getD a false, W.getD b false]] := rfl

lemma step_app (W vs : List Bool) (op : GateOp) (a b : ℕ) :
    stepW (W ++ vs) ⟨op, [a, b]⟩ = W ++ (vs ++ [op.eval [(W ++ vs).getD a false, (W ++ vs).getD b false]]) := by
  simp [stepW]

lemma get_lo (W vs : List Bool) (i : ℕ) (h : i < W.length) : (W ++ vs).getD i false = W.getD i false :=
  List.getD_append _ _ _ _ h

lemma get_hi (W vs : List Bool) (i : ℕ) : (W ++ vs).getD (W.length + i) false = vs.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

lemma get_hi0 (W vs : List Bool) : (W ++ vs).getD W.length false = vs.getD 0 false := get_hi W vs 0

lemma tail_eval (W : List Bool) (L p : ℕ) (hWL : W.length = L) (hL : 14 ≤ L) (hp : p < L ∨ p = L + 9) :
    ((tailG L p).foldl stepW W).getD (L + 11) false
      = ((if p < L then W.getD p false else false) || E W) := by
  subst hWL
  unfold tailG
  rw [List.foldl_cons, step0]
  rcases hp with hp | hp
  · rw [ite_eq_left hp]
    simp (disch := omega) only [List.foldl_cons, List.foldl_nil, step_app, get_hi, get_hi0, get_lo, List.nil_append, List.cons_append, List.getD_cons_succ, List.getD_cons_zero]
    simp [GateOp.eval, E, Bool.or_assoc]
  · subst hp
    rw [ite_eq_right (by omega)]
    simp (disch := omega) only [List.foldl_cons, List.foldl_nil, step_app, get_hi, get_hi0, get_lo, List.nil_append, List.cons_append, List.getD_cons_succ, List.getD_cons_zero]
    rw [Bool.eq_iff_iff]
    simp [GateOp.eval, E]

lemma E_congr (W V : List Bool) (h : ∀ i < 14, W.getD i false = V.getD i false) : E W = E V := by
  unfold E
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega), h 10 (by omega), h 11 (by omega), h 13 (by omega)]

lemma getD_fin (x5 : Fin 14 → Bool) (i : Fin 14) : (List.ofFn x5).getD ↑i false = x5 i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma mk (x5 : Fin 14 → Bool) (l : List (ℕ × ℕ)) (a b : ℕ) (ha : a < 14) (hb : b < 14) (hm : (a, b) ∈ l)
    (h1 : (List.ofFn x5).getD a false = true) (h2 : (List.ofFn x5).getD b false = true) :
    ∃ (x6 : Fin 14) (x7 : Fin 14), ((↑x6 : ℕ), (↑x7 : ℕ)) ∈ l ∧ x5 x6 = true ∧ x5 x7 = true :=
  ⟨⟨a, ha⟩, ⟨b, hb⟩, hm, (getD_fin x5 ⟨a, ha⟩).symm.trans h1, (getD_fin x5 ⟨b, hb⟩).symm.trans h2⟩

lemma edge (x5 : Fin 14 → Bool) :
    decide (∃ (x6 : Fin 14) (x7 : Fin 14), ((↑x6 : ℕ), (↑x7 : ℕ)) ∈ [((0 : ℕ), (10 : ℕ)), (1, 13), (2, 13), (3, 11), (4, 10), (4, 11), (4, 13), (5, 10), (6, 11)] ∧ x5 x6 = true ∧ x5 x7 = true)
      = E (List.ofFn x5) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, E, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨x6, x7, hmem, h1, h2⟩
    replace h1 := (getD_fin x5 x6).trans h1
    replace h2 := (getD_fin x5 x7).trans h2
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      (rw [ha] at h1; rw [hb] at h2; simp at h1 h2 ⊢; simp [h1, h2])
  · rintro ((⟨((h | h) | h), h2⟩ | ⟨((h | h) | h), h2⟩) | ⟨((h | h) | h), h2⟩)
    · exact mk x5 _ 0 10 (by omega) (by omega) (by simp) h h2
    · exact mk x5 _ 4 10 (by omega) (by omega) (by simp) h h2
    · exact mk x5 _ 5 10 (by omega) (by omega) (by simp) h h2
    · exact mk x5 _ 3 11 (by omega) (by omega) (by simp) h h2
    · exact mk x5 _ 4 11 (by omega) (by omega) (by simp) h h2
    · exact mk x5 _ 6 11 (by omega) (by omega) (by simp) h h2
    · exact mk x5 _ 1 13 (by omega) (by omega) (by simp) h h2
    · exact mk x5 _ 2 13 (by omega) (by omega) (by simp) h h2
    · exact mk x5 _ 4 13 (by omega) (by omega) (by simp) h h2

lemma main (x1 : Circuit) (h1 : IsAO2 10 x1) (hn : ∀ x3 ∈ x1.gates, x3.inputs.Nodup) :
    ∃ (x4 : Circuit), IsAO2 14 x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ 2 ≤ x4.size ∧ x4.size ≤ x1.size + 12 ∧
    ∀ (x5 : Fin 14 → Bool), x4.eval (List.ofFn x5) = (x1.eval (List.ofFn fun (x6 : Fin 10) => x5 ([(0 : Fin 14), 1, 2, 3, 5, 6, 7, 8, 9, 12].getD ↑x6 0)) || E (List.ofFn x5)) := by
  obtain ⟨hao, hrb, h2⟩ := h1
  have hW1 : ∀ x5 : Fin 14 → Bool, ((x1.gates.map (reGate r)).foldl stepW (List.ofFn x5)).length = 14 + x1.gates.length := by
    intro x5
    rw [fold_len]
    simp
  obtain ⟨p, hp, hpv⟩ : ∃ p, (p < 14 + x1.gates.length ∨ p = 14 + x1.gates.length + 9) ∧
      ∀ x5 : Fin 14 → Bool, (if p < 14 + x1.gates.length then ((x1.gates.map (reGate r)).foldl stepW (List.ofFn x5)).getD p false else false)
        = (x1.gates.foldl stepW (List.ofFn fun (x6 : Fin 10) => x5 ([(0 : Fin 14), 1, 2, 3, 5, 6, 7, 8, 9, 12].getD ↑x6 0))).getD x1.output false := by
    by_cases ho : x1.output < 10 + x1.gates.length
    · refine ⟨r x1.output, Or.inl (r_lt _ _ ho), ?_⟩
      intro x5
      rw [ite_eq_left (r_lt _ _ ho)]
      exact fold_inv x1.gates _ _ (by simp) (by simp) (base x5) x1.output
    · refine ⟨14 + x1.gates.length + 9, Or.inr rfl, ?_⟩
      intro x5
      rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by rw [fold_len]; simp; omega)]
  refine ⟨⟨x1.gates.map (reGate r) ++ tailG (14 + x1.gates.length) p, 14 + x1.gates.length + 11⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      exact hao g0 hg0
    · exact (tail_ops _ _ g h).1
  · intro j hj i hi
    unfold gateAt at hi
    simp only [List.length_append, List.length_map] at hj
    by_cases hjs : j < x1.gates.length
    · rw [List.getD_append _ _ _ _ (by simpa using hjs), List.getD_eq_getElem _ _ (by simpa using hjs), List.getElem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
      refine r_lt _ _ (hrb j hjs i0 ?_)
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hjs]
      exact hi0
    · obtain ⟨t, rfl⟩ : ∃ t, j = x1.gates.length + t := ⟨j - x1.gates.length, by omega⟩
      have ht : t < 12 := by
        simp [tailG] at hj
        omega
      rw [List.getD_append_right _ _ _ _ (by simp)] at hi
      simp only [List.length_map, Nat.add_sub_cancel_left] at hi
      interval_cases t <;> simp [tailG] at hi <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      simpa [reGate] using h2 g0 hg0
    · exact (tail_ops _ _ g h).2
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      exact (hn g0 hg0).map r_inj
    · exact tail_nodup _ _ (by omega) (by omega) g h
  · simp [Circuit.size, tailG]
  · simp [Circuit.size, tailG]
  · intro x5
    show ((x1.gates.map (reGate r) ++ tailG (14 + x1.gates.length) p).foldl stepW (List.ofFn x5)).getD (14 + x1.gates.length + 11) false = _
    rw [List.foldl_append, tail_eval _ _ p (hW1 x5) (by omega) hp, hpv x5]
    congr 1
    exact E_congr _ _ (fun i hi => fold_pre _ _ i (by simp; omega))

end PEqualNP.Outside.L_meta_3517_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3517_aux in
theorem PEqualNP.Outside.L_meta_3517 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (2 : ℕ) ≤ x4.size ∧ x4.size ≤ x1.size + (12 : ℕ) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = (x1.eval (List.ofFn fun (x6 : Fin (10 : ℕ)) => x5 ([(0 : Fin (14 : ℕ)), (1 : Fin (14 : ℕ)), (2 : Fin (14 : ℕ)), (3 : Fin (14 : ℕ)), (5 : Fin (14 : ℕ)), (6 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ)), (8 : Fin (14 : ℕ)), (9 : Fin (14 : ℕ)), (12 : Fin (14 : ℕ))].getD ↑x6 (0 : Fin (14 : ℕ)))) || Decidable.decide (∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true)) := by
  intro x1 h1 hn
  obtain ⟨x4, a, b, c, d, e⟩ := main x1 h1 hn
  refine ⟨x4, a, b, c, d, ?_⟩
  intro x5
  rw [e x5, edge x5]
