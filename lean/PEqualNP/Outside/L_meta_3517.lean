import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3517

open PEqualNP.CircuitLowerBounds

def ML : List (Fin 14) := [0, 1, 2, 3, 5, 6, 7, 8, 9, 12]

def f (i : ℕ) : ℕ := if i < 10 then ((ML.getD i 0 : Fin 14) : ℕ) else i + 4

def relabel (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_eq (w : List Bool) (g : Gate) :
    step w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

def extra (b o : ℕ) : List Gate :=
  [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [b, 5]⟩, ⟨GateOp.and, [10, b + 1]⟩,
   ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [b + 3, 6]⟩, ⟨GateOp.and, [11, b + 4]⟩,
   ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [b + 6, 4]⟩, ⟨GateOp.and, [13, b + 7]⟩,
   ⟨GateOp.or, [b + 2, b + 5]⟩, ⟨GateOp.or, [b + 9, b + 8]⟩, ⟨GateOp.or, [b + 10, o]⟩]

lemma f_lt (i : ℕ) : f i < 14 ∨ f i = i + 4 := by
  unfold f
  split
  · exact Or.inl (Fin.isLt _)
  · exact Or.inr rfl

lemma f_small (i : ℕ) (h : i < 10) : f i < 14 := by
  unfold f
  simp only [h, ↓reduceIte]
  exact Fin.isLt _

lemma f_big (i : ℕ) (h : ¬ i < 10) : f i = i + 4 := by
  unfold f
  simp only [h, ↓reduceIte]

lemma ML_inj : ∀ i j : Fin 10, ML.getD i 0 = ML.getD j 0 → i = j := by
  decide

lemma f_inj (i j : ℕ) (h : f i = f j) : i = j := by
  by_cases hi : i < 10 <;> by_cases hj : j < 10
  · unfold f at h
    simp only [hi, hj, ↓reduceIte] at h
    have := ML_inj ⟨i, hi⟩ ⟨j, hj⟩ (Fin.ext h)
    simpa using congrArg Fin.val this
  · have a := f_small i hi
    rw [f_big j hj] at h
    omega
  · have a := f_small j hj
    rw [f_big i hi] at h
    omega
  · rw [f_big i hi, f_big j hj] at h
    omega

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

lemma ofFn_getD_out {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : n ≤ i) :
    (List.ofFn x).getD i false = false := by
  rw [List.getD_eq_default _ _ (by simpa using h)]

lemma gd_left (l : List Bool) (a : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [a]).getD i false = l.getD i false :=
  List.getD_append _ _ _ _ h

lemma gd_new (l : List Bool) (a : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [a]).getD i false = a := by
  subst h
  simp

lemma gd_out (l : List Bool) (a : Bool) (i : ℕ) (h : l.length + 1 ≤ i) :
    (l ++ [a]).getD i false = false := by
  rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, step_eq]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [step_eq]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    rw [step_eq]
    exact gd_left _ _ _ hi

lemma relabel_wires (x y : List Bool) (hx : x.length = 10) (hy : y.length = 14)
    (h0 : ∀ i, y.getD (f i) false = x.getD i false) (gs : List Gate) :
    ∀ i, ((gs.map relabel).foldl step y).getD (f i) false = (gs.foldl step x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa using h0
  | append_singleton gs g ih =>
    intro i
    rw [List.map_append, List.foldl_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    have lP := foldl_length (gs.map relabel) y
    have lQ := foldl_length gs x
    rw [List.length_map] at lP
    set P' := (gs.map relabel).foldl step y with hP'
    set Q := gs.foldl step x with hQ
    have hv : (relabel g).op.eval ((relabel g).inputs.map fun j => P'.getD j false) =
        g.op.eval (g.inputs.map fun j => Q.getD j false) := by
      simp only [relabel, List.map_map, Function.comp_def, ih]
    rw [step_eq, step_eq, hv]
    rcases lt_trichotomy i (10 + gs.length) with h | h | h
    · have hf : f i < 14 + gs.length := by
        rcases f_lt i with a | a <;> omega
      rw [gd_left P' _ (f i) (by omega), gd_left Q _ i (by omega)]
      exact ih i
    · have hf : f i = 14 + gs.length := by
        rw [f_big i (by omega)]
        omega
      rw [gd_new P' _ (f i) (by omega), gd_new Q _ i (by omega)]
    · have hf : f i = i + 4 := f_big i (by omega)
      rw [gd_out P' _ (f i) (by omega), gd_out Q _ i (by omega)]

lemma extra_eval_in (P : List Bool) (b : ℕ) (hb : P.length = b) (h14 : 14 ≤ b) (o : ℕ)
    (ho : o < b) :
    ((extra b o).foldl step P).getD (b + 11) false =
      (((P.getD 10 false && (P.getD 0 false || P.getD 4 false || P.getD 5 false)) ||
        (P.getD 11 false && (P.getD 3 false || P.getD 4 false || P.getD 6 false)) ||
        (P.getD 13 false && (P.getD 1 false || P.getD 2 false || P.getD 4 false))) ||
        P.getD o false) := by
  subst hb
  simp (disch := omega)
    only [extra, step_eq, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true,
    Bool.or_false, List.append_assoc, List.cons_append, List.nil_append,
    List.getD_append, List.getD_append_right, Nat.add_sub_cancel_left, Nat.sub_self,
    List.getD_cons_succ, List.getD_cons_zero]

lemma tidy : ∀ a b c : Bool, (a || b || c || a) = (a || b || c) := by decide

lemma extra_eval_out (P : List Bool) (b : ℕ) (hb : P.length = b) (h14 : 14 ≤ b) :
    ((extra b (b + 2)).foldl step P).getD (b + 11) false =
      ((P.getD 10 false && (P.getD 0 false || P.getD 4 false || P.getD 5 false)) ||
        (P.getD 11 false && (P.getD 3 false || P.getD 4 false || P.getD 6 false)) ||
        (P.getD 13 false && (P.getD 1 false || P.getD 2 false || P.getD 4 false))) := by
  subst hb
  simp (disch := omega)
    only [extra, step_eq, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true,
    Bool.or_false, List.append_assoc, List.cons_append, List.nil_append,
    List.getD_append, List.getD_append_right, Nat.add_sub_cancel_left, Nat.sub_self,
    List.getD_cons_succ, List.getD_cons_zero]
  exact tidy _ _ _

lemma edge_eq (x : Fin 14 → Bool) :
    decide (∃ (a : Fin 14) (c : Fin 14), ((a : ℕ), (c : ℕ)) ∈
        [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)),
         ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)),
         ((6 : ℕ), (11 : ℕ))] ∧ x a = true ∧ x c = true) =
      ((x 10 && (x 0 || x 4 || x 5)) || (x 11 && (x 3 || x 4 || x 6)) ||
        (x 13 && (x 1 || x 2 || x 4))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨a, c, hm, ha, hc⟩
    fin_cases a <;> fin_cases c <;> simp_all
  · rintro ((⟨h10, (h0 | h4) | h5⟩ | ⟨h11, (h3 | h4) | h6⟩) | ⟨h13, (h1 | h2) | h4⟩)
    · exact ⟨0, 10, by simp, h0, h10⟩
    · exact ⟨4, 10, by simp, h4, h10⟩
    · exact ⟨5, 10, by simp, h5, h10⟩
    · exact ⟨3, 11, by simp, h3, h11⟩
    · exact ⟨4, 11, by simp, h4, h11⟩
    · exact ⟨6, 11, by simp, h6, h11⟩
    · exact ⟨1, 13, by simp, h1, h13⟩
    · exact ⟨2, 13, by simp, h2, h13⟩
    · exact ⟨4, 13, by simp, h4, h13⟩

end PEqualNP.Outside.L_meta_3517

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_3517 in
theorem PEqualNP.Outside.L_meta_3517 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (2 : ℕ) ≤ x4.size ∧ x4.size ≤ x1.size + (12 : ℕ) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = (x1.eval (List.ofFn fun (x6 : Fin (10 : ℕ)) => x5 ([(0 : Fin (14 : ℕ)), (1 : Fin (14 : ℕ)), (2 : Fin (14 : ℕ)), (3 : Fin (14 : ℕ)), (5 : Fin (14 : ℕ)), (6 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ)), (8 : Fin (14 : ℕ)), (9 : Fin (14 : ℕ)), (12 : Fin (14 : ℕ))].getD ↑x6 (0 : Fin (14 : ℕ)))) || Decidable.decide (∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true)) := by
  intro C hC hnd
  unfold PEqualNP.TopForm.IsAO2 at hC
  obtain ⟨hAO, hRB, hL2⟩ := hC
  have ho' : (if C.output < 10 + C.gates.length then f C.output else 14 + C.gates.length + 2) <
      14 + C.gates.length + 3 := by
    split_ifs with hc
    · rcases f_lt C.output with h | h <;> omega
    · omega
  generalize hdef : (if C.output < 10 + C.gates.length then f C.output
    else 14 + C.gates.length + 2) = o' at ho'
  refine ⟨⟨C.gates.map relabel ++ extra (14 + C.gates.length) o', 14 + C.gates.length + 11⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold PEqualNP.TopForm.IsAO2
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        exact hAO g0 hg0
      · simp only [extra, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp
    · intro j hj i hi
      simp only [List.length_append, List.length_map] at hj
      unfold gateAt at hi
      by_cases hjs : j < C.gates.length
      · rw [List.getD_append _ _ _ _ (by simpa using hjs)] at hi
        have e : (C.gates.map relabel).getD j ⟨GateOp.or, []⟩ = relabel (gateAt C j) :=
          List.getD_map C.gates ⟨GateOp.or, []⟩ relabel
        rw [e] at hi
        simp only [relabel] at hi
        obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
        have := hRB j hjs i0 hi0
        rcases f_lt i0 with h | h <;> omega
      · obtain ⟨k, rfl⟩ : ∃ k, j = C.gates.length + k := ⟨j - C.gates.length, by omega⟩
        rw [List.getD_append_right _ _ _ _ (by simp)] at hi
        simp only [List.length_map, Nat.add_sub_cancel_left] at hi
        have hk : k < 12 := by simp [extra] at hj; omega
        interval_cases k <;> simp [extra] at hi <;> omega
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        simp only [relabel, List.length_map]
        exact hL2 g0 hg0
      · simp only [extra, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      simp only [relabel]
      exact (hnd g0 hg0).map (fun a b h => f_inj a b h)
    · simp only [extra, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp <;> omega
  · simp only [Circuit.size, List.length_append, List.length_map, extra, List.length_cons,
      List.length_nil]
    omega
  · simp only [Circuit.size, List.length_append, List.length_map, extra, List.length_cons,
      List.length_nil]
    omega
  · intro x5
    rw [edge_eq]
    have hy : (List.ofFn x5).length = 14 := List.length_ofFn
    have hx : (List.ofFn fun x6 : Fin 10 => x5 (ML.getD ↑x6 0)).length = 10 := List.length_ofFn
    have h0 : ∀ i, (List.ofFn x5).getD (f i) false =
        (List.ofFn fun x6 : Fin 10 => x5 (ML.getD ↑x6 0)).getD i false := by
      intro i
      by_cases hi : i < 10
      · rw [ofFn_getD _ i hi]
        have hfi : f i = ((ML.getD i 0 : Fin 14) : ℕ) := by
          unfold f
          simp only [hi, ↓reduceIte]
        rw [hfi, ofFn_getD x5 _ (Fin.isLt _)]
      · rw [ofFn_getD_out _ i (by omega), ofFn_getD_out _ _ (by rw [f_big i hi]; omega)]
    have hrel := relabel_wires _ _ hx hy h0 C.gates
    have hP := foldl_length (C.gates.map relabel) (List.ofFn x5)
    rw [hy, List.length_map] at hP
    have hk : ∀ k (h : k < 14),
        ((C.gates.map relabel).foldl step (List.ofFn x5)).getD k false = x5 ⟨k, h⟩ := by
      intro k h
      rw [foldl_prefix _ _ _ (by rw [hy]; exact h), ofFn_getD x5 k h]
    show ((C.gates.map relabel ++ extra (14 + C.gates.length) o').foldl step
        (List.ofFn x5)).getD (14 + C.gates.length + 11) false =
      ((C.gates.foldl step (List.ofFn fun x6 : Fin 10 => x5 (ML.getD ↑x6 0))).getD C.output false
        || _)
    rw [List.foldl_append]
    by_cases hc : C.output < 10 + C.gates.length
    · simp only [hc, ↓reduceIte] at hdef
      have ho2 : o' < 14 + C.gates.length := by
        rw [← hdef]
        rcases f_lt C.output with h | h <;> omega
      rw [extra_eval_in _ _ hP (by omega) o' ho2, ← hdef, hrel C.output,
        hk 0 (by norm_num), hk 1 (by norm_num), hk 2 (by norm_num), hk 3 (by norm_num),
        hk 4 (by norm_num), hk 5 (by norm_num), hk 6 (by norm_num), hk 10 (by norm_num),
        hk 11 (by norm_num), hk 13 (by norm_num), Bool.or_comm]
      rfl
    · simp only [hc, ↓reduceIte] at hdef
      subst hdef
      rw [extra_eval_out _ _ hP (by omega)]
      have hout : (C.gates.foldl step
          (List.ofFn fun x6 : Fin 10 => x5 (ML.getD ↑x6 0))).getD C.output false = false :=
        List.getD_eq_default _ _ (by rw [foldl_length, hx]; omega)
      rw [hout, Bool.false_or,
        hk 0 (by norm_num), hk 1 (by norm_num), hk 2 (by norm_num), hk 3 (by norm_num),
        hk 4 (by norm_num), hk 5 (by norm_num), hk 6 (by norm_num), hk 10 (by norm_num),
        hk 11 (by norm_num), hk 13 (by norm_num)]
      rfl
