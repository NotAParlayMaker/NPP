import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3517

open PEqualNP.CircuitLowerBounds

def Ml : List (Fin 14) := [0, 1, 2, 3, 5, 6, 7, 8, 9, 12]

def sg (i : ℕ) : ℕ := if i < 10 then (Ml.getD i 0).val else i + 4

def rg (g : Gate) : Gate := ⟨g.op, g.inputs.map sg⟩

theorem sg_lt (i : ℕ) (hi : i < 10) : sg i < 14 := by
  simp only [sg, hi, ite_true]
  exact (Ml.getD i 0).isLt

theorem sg_ge (i : ℕ) (hi : ¬ i < 10) : sg i = i + 4 := by
  simp only [sg, hi, ite_false]

theorem sg_inj (i j : ℕ) (h : sg i = sg j) : i = j := by
  by_cases hi : i < 10 <;> by_cases hj : j < 10
  · simp only [sg, hi, hj, ite_true] at h
    interval_cases i <;> interval_cases j <;> simp_all [Ml]
  · have := sg_lt i hi; rw [sg_ge j hj] at h; omega
  · have := sg_lt j hj; rw [sg_ge i hi] at h; omega
  · rw [sg_ge i hi, sg_ge j hj] at h; omega

theorem key (x y L : List Bool) (hx : x.length = 10) (hy : y.length = 14)
    (hxy : ∀ i < 10, y.getD (sg i) false = x.getD i false) (i : ℕ) :
    (y ++ L).getD (sg i) false = (x ++ L).getD i false := by
  by_cases hi : i < 10
  · rw [List.getD_append _ _ _ _ (by have := sg_lt i hi; omega),
      List.getD_append _ _ _ _ (by omega)]
    exact hxy i hi
  · rw [sg_ge i hi, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

theorem fold_remap (x y : List Bool) (hx : x.length = 10) (hy : y.length = 14)
    (hxy : ∀ i < 10, y.getD (sg i) false = x.getD i false) (gs : List Gate) :
    ∀ L : List Bool, ∃ R : List Bool,
      (gs.map rg).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (y ++ L) = y ++ R ∧
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (x ++ L) = x ++ R := by
  induction gs with
  | nil => intro L; exact ⟨L, by simp, by simp⟩
  | cons g gs ih =>
    intro L
    obtain ⟨R, h1, h2⟩ := ih (L ++ [g.op.eval (g.inputs.map fun i => (x ++ L).getD i false)])
    refine ⟨R, ?_, ?_⟩
    · simp only [List.map_cons, List.foldl_cons]
      rw [← h1, List.append_assoc]
      simp only [rg, List.map_map]
      have hm : List.map ((fun i => (y ++ L).getD i false) ∘ sg) g.inputs
          = List.map (fun i => (x ++ L).getD i false) g.inputs :=
        List.map_congr_left (fun i _ => key x y L hx hy hxy i)
      rw [hm]
    · simp only [List.foldl_cons]
      rw [List.append_assoc]
      exact h2

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem snoc_lt (l : List Bool) (a : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [a]).getD i false = l.getD i false := List.getD_append _ _ _ _ h

theorem snoc_eq (l : List Bool) (a : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [a]).getD i false = a := by
  subst h
  simp

def ext (b t : ℕ) : List Gate :=
  [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [b, 5]⟩, ⟨GateOp.and, [10, b + 1]⟩,
   ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [b + 3, 6]⟩, ⟨GateOp.and, [11, b + 4]⟩,
   ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [b + 6, 4]⟩, ⟨GateOp.and, [13, b + 7]⟩,
   ⟨GateOp.or, [b + 2, b + 5]⟩, ⟨GateOp.or, [b + 9, b + 8]⟩, ⟨GateOp.or, [t, b + 10]⟩]

theorem ext_eval (W : List Bool) (b t : ℕ) (hW : W.length = b) (hb : 14 ≤ b) (ht : t < b) :
    ((ext b t).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
      (b + 11) false
      = (W.getD t false || ((W.getD 10 false && ((W.getD 0 false || W.getD 4 false) || W.getD 5 false)) ||
          (W.getD 11 false && ((W.getD 3 false || W.getD 4 false) || W.getD 6 false))) ||
          (W.getD 13 false && ((W.getD 1 false || W.getD 2 false) || W.getD 4 false))) := by
  subst hW
  simp (disch := (try ((try simp only [List.length_append, List.length_cons, List.length_nil]) <;> omega))) only
    [ext, List.foldl_cons, List.foldl_nil, snoc_lt, snoc_eq, List.map_cons, List.map_nil,
     GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id, Bool.or_false,
     Bool.and_true]
  simp only [Bool.or_assoc]


theorem ext_eval_out (W : List Bool) (b : ℕ) (hW : W.length = b) (hb : 14 ≤ b) :
    ((ext b (b + 9)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
      (b + 11) false
      = (((W.getD 10 false && ((W.getD 0 false || W.getD 4 false) || W.getD 5 false)) ||
          (W.getD 11 false && ((W.getD 3 false || W.getD 4 false) || W.getD 6 false))) ||
          (W.getD 13 false && ((W.getD 1 false || W.getD 2 false) || W.getD 4 false))) := by
  subst hW
  simp (disch := (try ((try simp only [List.length_append, List.length_cons, List.length_nil]) <;> omega))) only
    [ext, List.foldl_cons, List.foldl_nil, snoc_lt, snoc_eq, List.map_cons, List.map_nil,
     GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id, Bool.or_false,
     Bool.and_true]
  generalize W.getD 0 false = a0
  generalize W.getD 1 false = a1
  generalize W.getD 2 false = a2
  generalize W.getD 3 false = a3
  generalize W.getD 4 false = a4
  generalize W.getD 5 false = a5
  generalize W.getD 6 false = a6
  generalize W.getD 10 false = a10
  generalize W.getD 11 false = a11
  generalize W.getD 13 false = a13
  revert a0 a1 a2 a3 a4 a5 a6 a10 a11 a13
  decide

theorem stars (y5 : Fin 14 → Bool) :
    (((y5 10 && ((y5 0 || y5 4) || y5 5)) || (y5 11 && ((y5 3 || y5 4) || y5 6))) ||
      (y5 13 && ((y5 1 || y5 2) || y5 4)))
    = decide (∃ (x6 : Fin 14) (x7 : Fin 14), ((x6 : ℕ), (x7 : ℕ)) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)),
        ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)),
        ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ y5 x6 = true ∧ y5 x7 = true) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
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
  · rintro ⟨a, c, hmem, ha, hc⟩
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    · obtain ⟨a, ha'⟩ := a
      obtain ⟨c, hc'⟩ := c
      simp only at h1 h2
      subst h1 h2
      simp_all

end PEqualNP.Outside.L_meta_3517

theorem PEqualNP.Outside.L_meta_3517 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (2 : ℕ) ≤ x4.size ∧ x4.size ≤ x1.size + (12 : ℕ) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = (x1.eval (List.ofFn fun (x6 : Fin (10 : ℕ)) => x5 ([(0 : Fin (14 : ℕ)), (1 : Fin (14 : ℕ)), (2 : Fin (14 : ℕ)), (3 : Fin (14 : ℕ)), (5 : Fin (14 : ℕ)), (6 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ)), (8 : Fin (14 : ℕ)), (9 : Fin (14 : ℕ)), (12 : Fin (14 : ℕ))].getD ↑x6 (0 : Fin (14 : ℕ)))) || Decidable.decide (∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true)) := by
  intro C hC hnd
  obtain ⟨hAO, hRB, h2⟩ := hC
  open PEqualNP.Outside.L_meta_3517 in
  refine ⟨⟨C.gates.map rg ++ ext (14 + C.gates.length)
      (if C.output < 10 + C.gates.length then sg C.output else 14 + C.gates.length + 9),
      14 + C.gates.length + 11⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact hAO g0 hg0
    · simp only [ext, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    simp only [List.length_append, List.length_map] at hj
    by_cases hjs : j < C.gates.length
    · rw [List.getD_append _ _ _ _ (by simpa using hjs), List.getD_eq_getElem _ _ (by simpa using hjs),
        List.getElem_map] at hi
      simp only [rg, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hr := hRB j hjs i0 (by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
        rw [List.getD_eq_getElem _ _ hjs]
        exact hi0)
      by_cases h10 : i0 < 10
      · have := sg_lt i0 h10
        omega
      · rw [sg_ge i0 h10]
        omega
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi
      simp only [List.length_map] at hi
      obtain ⟨k, rfl⟩ : ∃ k, j = C.gates.length + k := ⟨j - C.gates.length, by omega⟩
      have hk : k < 12 := by simp [ext] at hj; omega
      rw [show C.gates.length + k - C.gates.length = k by omega] at hi
      interval_cases k <;> simp [ext] at hi <;> try omega
      split_ifs at hi with ho
      · rcases hi with rfl | rfl
        · by_cases h10 : C.output < 10
          · have := sg_lt _ h10
            omega
          · rw [sg_ge _ h10]
            omega
        · omega
      · omega
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      simp only [rg, List.length_map]
      exact h2 g0 hg0
    · simp only [ext, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact List.Nodup.map_on (fun a _ b _ h => sg_inj a b h) (hnd g0 hg0)
    · simp only [ext, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp <;> try omega
      split_ifs with ho
      · by_cases h10 : C.output < 10
        · have := sg_lt _ h10
          omega
        · rw [sg_ge _ h10]
          omega
      · omega
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, ext]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, ext]
  · intro y5
    have hx : (List.ofFn fun (x6 : Fin 10) => y5 (Ml.getD x6 0)).length = 10 := by simp
    have hy : (List.ofFn y5).length = 14 := by simp
    have hxy : ∀ i < 10, (List.ofFn y5).getD (sg i) false
        = (List.ofFn fun (x6 : Fin 10) => y5 (Ml.getD x6 0)).getD i false := by
      intro i hi
      interval_cases i <;> simp [sg, Ml, List.getD_eq_getElem?_getD]
    obtain ⟨R, h1, h3⟩ := fold_remap _ _ hx hy hxy C.gates []
    simp only [List.append_nil] at h1 h3
    have hR : R.length = C.gates.length := by
      have := fold_len C.gates (List.ofFn fun (x6 : Fin 10) => y5 (Ml.getD x6 0))
      rw [h3] at this
      simp only [List.length_append, List.length_ofFn] at this
      omega
    have hW : (List.ofFn y5 ++ R).length = 14 + C.gates.length := by
      rw [List.length_append, List.length_ofFn, hR]
    have hin : ∀ k (hk : k < 14), (List.ofFn y5 ++ R).getD k false = y5 ⟨k, hk⟩ := by
      intro k hk
      rw [List.getD_append _ _ _ _ (by simpa using hk)]
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
    have hC : C.eval (List.ofFn fun (x6 : Fin 10) => y5 (Ml.getD x6 0))
        = ((List.ofFn fun (x6 : Fin 10) => y5 (Ml.getD x6 0)) ++ R).getD C.output false := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [h3]
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [List.foldl_append]
    rw [h1]
    rw [← stars y5]
    change _ = (C.eval (List.ofFn fun (x6 : Fin 10) => y5 (Ml.getD x6 0)) || _)
    by_cases ho : C.output < 10 + C.gates.length
    · simp only [ho, ite_true]
      rw [ext_eval _ _ _ hW (by omega) (by
        by_cases h10 : C.output < 10
        · have := sg_lt _ h10
          omega
        · rw [sg_ge _ h10]
          omega)]
      rw [key _ _ R hx hy hxy, ← hC]
      rw [hin 0 (by norm_num), hin 1 (by norm_num), hin 2 (by norm_num), hin 3 (by norm_num),
        hin 4 (by norm_num), hin 5 (by norm_num), hin 6 (by norm_num), hin 10 (by norm_num),
        hin 11 (by norm_num), hin 13 (by norm_num)]
      simp only [Bool.or_assoc]
      rfl
    · simp only [ho, ite_false]
      rw [ext_eval_out _ _ hW (by omega)]
      have hf : C.eval (List.ofFn fun (x6 : Fin 10) => y5 (Ml.getD x6 0)) = false := by
        rw [hC]
        apply List.getD_eq_default
        simp only [List.length_append, List.length_ofFn, hR]
        omega
      rw [hf, Bool.false_or]
      rw [hin 0 (by norm_num), hin 1 (by norm_num), hin 2 (by norm_num), hin 3 (by norm_num),
        hin 4 (by norm_num), hin 5 (by norm_num), hin 6 (by norm_num), hin 10 (by norm_num),
        hin 11 (by norm_num), hin 13 (by norm_num)]
      simp only [Bool.or_assoc]
      rfl
