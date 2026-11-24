import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace PEqualNP.Outside.L_meta_4439

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeFun : (Fin 9 → Bool) → Bool :=
  fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))

def maskList : List ℕ :=
  [0, 1, 4, 16, 128, 80, 3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144, 81, 84, 208]

def maskVal (m : ℕ) (x : Fin 9 → Bool) : Bool :=
  decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true)

def sig (s : Fin 4) : List ℕ :=
  match s.val with
  | 0 => [0, 1, 2, 3, 4, 5, 6, 7, 8]
  | 1 => [1, 0, 5, 8, 6, 2, 4, 7, 3]
  | 2 => [3, 8, 5, 0, 4, 2, 6, 7, 1]
  | _ => [8, 3, 2, 1, 6, 5, 4, 7, 0]

def sigFin (s : Fin 4) (i : Fin 9) : Fin 9 :=
  match s.val with
  | 0 => ![0, 1, 2, 3, 4, 5, 6, 7, 8] i
  | 1 => ![1, 0, 5, 8, 6, 2, 4, 7, 3] i
  | 2 => ![3, 8, 5, 0, 4, 2, 6, 7, 1] i
  | _ => ![8, 3, 2, 1, 6, 5, 4, 7, 0] i

lemma sig_edge (s : Fin 4) (x : Fin 9 → Bool) :
    edgeFun (fun i => x (sigFin s i)) = edgeFun x := by
  revert x s
  decide

lemma sig_46 (s : Fin 4) (x : Fin 9 → Bool) :
    (x (sigFin s 4) || x (sigFin s 6)) = (x 4 || x 6) := by
  revert x s
  decide

lemma sig_lt (s : Fin 4) (j : ℕ) (hj : j < 9) : (sig s).getD j j < 9 := by
  revert hj j s
  decide

lemma sig_ge (s : Fin 4) (j : ℕ) (hj : 9 ≤ j) : (sig s).getD j j = j := by
  have hlen : (sig s).length = 9 := by
    revert s
    decide
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma sig_in (s : Fin 4) (y : Fin 9 → Bool) (j : ℕ) :
    (List.ofFn y).getD ((sig s).getD j j) false =
      (List.ofFn fun i => y (sigFin s i)).getD j false := by
  by_cases hj : j < 9
  · fin_cases s <;> interval_cases j <;> rfl
  · rw [sig_ge s j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

lemma sig_fold (s : Fin 4) (gs : List Gate) (W W' : List Bool)
    (hl : W.length = W'.length) (h9 : 9 ≤ W.length)
    (hW : ∀ j : ℕ, W'.getD ((sig s).getD j j) false = W.getD j false) (j : ℕ) :
    ((gs.map fun g : Gate =>
        Gate.mk g.op (g.inputs.map fun i => (sig s).getD i i)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD
        ((sig s).getD j j) false =
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
      j false := by
  induction gs generalizing W W' j with
  | nil => exact hW j
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [hl]
    · simp; omega
    · have hv : g.op.eval ((g.inputs.map fun i => (sig s).getD i i).map
          fun i => W'.getD i false) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact hW i
      intro k
      rw [hv]
      by_cases hk : k < W.length
      · have hk' : (sig s).getD k k < W'.length := by
          by_cases h : k < 9
          · have := sig_lt s k h; omega
          · rw [sig_ge s k (by omega)]; omega
        have hWk := hW k
        generalize (sig s).getD k k = r at hk' hWk ⊢
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hk', List.getElem?_append_left hk]
        simpa only [List.getD_eq_getElem?_getD] using hWk
      · rw [sig_ge s k (by omega)]
        by_cases hk2 : k = W.length
        · subst hk2
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl,
            List.getElem?_append_right (le_refl _), ← hl,
            List.getElem?_append_right (le_refl _)]
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

lemma ofFn_snoc {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

lemma ofFn_snoc2 (x : Fin 9 → Bool) (b1 b2 : Bool) :
    List.ofFn (Fin.snoc (Fin.snoc x b1) b2 : Fin 11 → Bool) = List.ofFn x ++ [b1, b2] := by
  rw [ofFn_snoc, ofFn_snoc, List.append_assoc, List.singleton_append]

def wireVal (x : Fin 9 → Bool) (i : ℕ) : Bool :=
  (List.ofFn x ++ [x 4 || x 6]).getD i false

def wireMask (i : ℕ) : ℕ :=
  if i < 9 then 1 <<< i else if i = 9 then 80 else 0

lemma maskVal_zero (x : Fin 9 → Bool) : maskVal 0 x = false := by
  revert x
  decide

lemma wireVal_eq_maskVal (i : ℕ) (x : Fin 9 → Bool) :
    wireVal x i = maskVal (wireMask i) x := by
  by_cases h10 : i < 10
  · revert x
    interval_cases i <;> decide
  · have hge : wireVal x i = false := by
      unfold wireVal
      rw [List.getD_eq_default _ false (by simp; omega)]
    have hm : wireMask i = 0 := by
      unfold wireMask
      split_ifs <;> omega
    rw [hge, hm, maskVal_zero]

lemma maskVal_or (m1 m2 : ℕ) (x : Fin 9 → Bool) :
    (maskVal m1 x || maskVal m2 x) = maskVal (m1 ||| m2) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [maskVal, Bool.or_eq_true, decide_eq_true_eq, Nat.testBit_or]
  constructor
  · rintro (⟨i, hi, hxi⟩ | ⟨i, hi, hxi⟩)
    · exact ⟨i, Or.inl hi, hxi⟩
    · exact ⟨i, Or.inr hi, hxi⟩
  · rintro ⟨i, hi1 | hi2, hxi⟩
    · exact Or.inl ⟨i, hi1, hxi⟩
    · exact Or.inr ⟨i, hi2, hxi⟩

lemma mask_exists (ins : List ℕ) (h : ins.length ≤ 2) :
    ∃ m ∈ maskList, ∃ s : Fin 4,
      ∀ x : Fin 9 → Bool,
        GateOp.or.eval (ins.map (wireVal (fun i => x (sigFin s i)))) = maskVal m x := by
  have hcheck : ∀ a : Fin 11, ∀ b : Fin 11,
      ∃ m ∈ maskList, ∃ s : Fin 4,
        (wireMask ((sig s).getD a.val a.val) ||| wireMask ((sig s).getD b.val b.val)) = m := by
    decide
  have hsig_wire : ∀ s : Fin 4, ∀ i : ℕ, ∀ x : Fin 9 → Bool,
      wireVal (fun k => x (sigFin s k)) i = wireVal x ((sig s).getD i i) := by
    intro s i x
    by_cases h10 : i < 10
    · revert x s
      interval_cases i <;> decide
    · unfold wireVal
      rw [sig_ge s i (by omega), List.getD_eq_default _ false (by simp; omega),
        List.getD_eq_default _ false (by simp; omega)]
  have hclamp : ∀ s : Fin 4, ∀ a : ℕ,
      wireMask ((sig s).getD a a) = wireMask ((sig s).getD (min a 10) (min a 10)) := by
    intro s a
    by_cases h10 : a < 10
    · rw [Nat.min_eq_left (by omega : a ≤ 10)]
    · rw [Nat.min_eq_right (by omega : 10 ≤ a), sig_ge s a (by omega), sig_ge s 10 (by omega)]
      unfold wireMask
      split_ifs <;> omega
  rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · refine ⟨0, by simp [maskList], 0, ?_⟩
    intro x
    simp [GateOp.eval, maskVal_zero]
  · let a' : Fin 11 := ⟨min a 10, by omega⟩
    obtain ⟨m, hm, s, hs⟩ := hcheck a' a'
    refine ⟨m, hm, s, ?_⟩
    intro x
    simp only [List.map, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
      hsig_wire, wireVal_eq_maskVal]
    have h1 : wireMask ((sig s).getD a a) = m := by
      rw [hclamp s a, ← hs, Nat.or_self]
    rw [h1]
  · let a' : Fin 11 := ⟨min a 10, by omega⟩
    let b' : Fin 11 := ⟨min b 10, by omega⟩
    obtain ⟨m, hm, s, hs⟩ := hcheck a' b'
    refine ⟨m, hm, s, ?_⟩
    intro x
    simp only [List.map, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
      hsig_wire, wireVal_eq_maskVal, maskVal_or]
    rw [hclamp s a, hclamp s b, hs]
  · simp at h

lemma wires_append (gs : List Gate) (w : List Bool) :
    ∃ extra, (Circuit.mk gs 0).wires w = w ++ extra ∧ extra.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [Circuit.wires], rfl⟩
  | cons g rest ih =>
    obtain ⟨extra, heq, hlen⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: extra, ?_, by simp [hlen]⟩
    change (Circuit.mk rest 0).wires (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [heq]
    simp [List.append_assoc]

end PEqualNP.Outside.L_meta_4439

open PEqualNP.Outside.L_meta_4439 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_4439 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (4 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x2.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → x2.size ≤ (15 : ℕ) → ∃ x8 ∈ [(0 : ℕ), (1 : ℕ), (4 : ℕ), (16 : ℕ), (128 : ℕ), (80 : ℕ), (3 : ℕ), (5 : ℕ), (9 : ℕ), (17 : ℕ), (33 : ℕ), (65 : ℕ), (129 : ℕ), (257 : ℕ), (20 : ℕ), (36 : ℕ), (132 : ℕ), (144 : ℕ), (81 : ℕ), (84 : ℕ), (208 : ℕ)], ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size ≤ (13 : ℕ) ∧ ∀ (x10 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x9 (Fin.snoc (Fin.snoc x10 (x10 (4 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)))) (Decidable.decide (∃ (x11 : Fin (9 : ℕ)), x8.testBit ↑x11 = Bool.true ∧ x10 x11 = Bool.true))) = x1 x10 := by
  dsimp only
  intro C hfan h9 hfun hg1 hsz
  rcases C with ⟨_ | ⟨g0, _ | ⟨g1, tail⟩⟩, out⟩
  · simp at hg1
  · simp at hg1
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      Option.some.injEq] at hg1
    have hg0 : ∀ x : Fin 9 → Bool,
        g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 || x 6) := by
      intro x
      let w0 := List.ofFn x
      let v0 := g0.op.eval (g0.inputs.map fun i => w0.getD i false)
      obtain ⟨extra, heq, _⟩ := wires_append (g1 :: tail) (w0 ++ [v0])
      have h := h9 x
      change ((Circuit.mk (g1 :: tail) 0).wires (w0 ++ [v0])).getD 9 false = _ at h
      rw [heq, List.getD_append _ _ false 9 (by simp [w0]),
        List.getD_append_right w0 [v0] false 9 (by simp [w0])] at h
      simpa [v0, w0] using h
    have hg1_fan := hfan g1 (by simp)
    obtain ⟨m, hm, s, hmask⟩ := mask_exists g1.inputs hg1_fan.2
    refine ⟨m, hm, ?_⟩
    have htail_len : tail.length ≤ 13 := by
      change (g0 :: g1 :: tail).length ≤ 15 at hsz
      simp only [List.length_cons] at hsz
      omega
    have htail_fan : FanInTwo ⟨tail, out⟩ := by
      intro g hg
      exact hfan g (by simp [hg])
    have heval_tail : ∀ x : Fin 9 → Bool,
        (Circuit.mk tail out).eval
          (List.ofFn x ++ [x 4 || x 6, g1.op.eval (g1.inputs.map (wireVal x))]) =
        edgeFun x := by
      intro x
      have hf := congrFun hfun x
      change (Circuit.mk (g0 :: g1 :: tail) out).eval (List.ofFn x) = edgeFun x at hf
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, hg0 x, List.append_assoc,
        List.singleton_append] at hf
      exact hf
    let tail' := tail.map fun g : Gate => Gate.mk g.op (g.inputs.map fun i => (sig s).getD i i)
    let out' := (sig s).getD out out
    have hfan' : FanInTwo ⟨tail', out'⟩ := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(htail_fan g' hg').1, by simpa using (htail_fan g' hg').2⟩
    have hlen' : (Circuit.mk tail' out').size ≤ 13 := by
      change tail'.length ≤ 13
      simpa [tail'] using htail_len
    refine ⟨⟨tail', out'⟩, hfan', hlen', ?_⟩
    intro x
    change (Circuit.mk tail' out').eval
      (List.ofFn (Fin.snoc (Fin.snoc x (x 4 || x 6)) (maskVal m x))) = edgeFun x
    rw [ofFn_snoc2]
    have h2x := hmask x
    rw [← hg1] at h2x
    rw [← h2x]
    let y : Fin 9 → Bool := fun i => x (sigFin s i)
    have hy46 : (y 4 || y 6) = (x 4 || x 6) := sig_46 s x
    let W := List.ofFn y ++ [y 4 || y 6, g1.op.eval (g1.inputs.map (wireVal y))]
    let W' := List.ofFn x ++ [x 4 || x 6, g1.op.eval (g1.inputs.map (wireVal y))]
    have hWW' : ∀ j : ℕ, W'.getD ((sig s).getD j j) false = W.getD j false := by
      intro j
      by_cases hj : j < 9
      · have hj' : (sig s).getD j j < 9 := sig_lt s j hj
        have hin := sig_in s x j
        generalize (sig s).getD j j = r at hj' hin ⊢
        dsimp only [W, W']
        rw [List.getD_append _ _ _ _ (by simp [hj']),
          List.getD_append _ _ _ _ (by simp [hj])]
        exact hin
      · rw [sig_ge s j (by omega)]
        by_cases hj9 : j = 9
        · subst hj9
          dsimp only [W, W']
          rw [List.getD_append_right _ _ _ 9 (by simp),
            List.getD_append_right _ _ _ 9 (by simp)]
          simp [hy46]
        · by_cases hj10 : j = 10
          · subst hj10
            dsimp only [W, W']
            rw [List.getD_append_right _ _ _ 10 (by simp),
              List.getD_append_right _ _ _ 10 (by simp)]
            simp
          · dsimp only [W, W']
            rw [List.getD_eq_default _ false (by simp; omega),
              List.getD_eq_default _ false (by simp; omega)]
    have hfold := sig_fold s tail W W' (by simp [W, W']) (by simp [W]) hWW' out
    change ((Circuit.mk tail' out').wires W').getD out' false = edgeFun x
    change ((Circuit.mk tail' out').wires W').getD out' false =
      ((Circuit.mk tail out).wires W).getD out false at hfold
    rw [hfold]
    exact (heval_tail y).trans (sig_edge s x)
