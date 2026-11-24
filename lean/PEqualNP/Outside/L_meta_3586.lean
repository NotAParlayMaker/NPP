import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3586

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepW_ext (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, gs.foldl stepW w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (stepW w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [stepW]

lemma foldl_stepW_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := foldl_stepW_ext gs w
  rw [ht]
  exact List.getD_append w t false i hi

def clamp10 (w : ℕ) : Fin 11 :=
  if h : w < 10 then ⟨w, by omega⟩ else ⟨10, by omega⟩

lemma getD_clamp10 (l : List Bool) (hl : l.length = 10) (w : ℕ) :
    l.getD (clamp10 w).val false = l.getD w false := by
  unfold clamp10
  split_ifs with h
  · rfl
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

lemma getD_10_false (l : List Bool) (hl : l.length = 10) : l.getD 10 false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma or_eval_le_two_uniform (ins : List ℕ) (hins : ins.length ≤ 2) :
    ∃ (x5 x6 : Fin 11), ∀ (l : List Bool), l.length = 10 →
      GateOp.or.eval (ins.map fun i => l.getD i false) =
        (l.getD x5.val false || l.getD x6.val false) := by
  match ins with
  | [] =>
    refine ⟨⟨10, by omega⟩, ⟨10, by omega⟩, fun l hl => ?_⟩
    simp only [GateOp.eval, List.map_nil, List.any_nil]
    rw [getD_10_false l hl]
    rfl
  | [a] =>
    refine ⟨clamp10 a, ⟨10, by omega⟩, fun l hl => ?_⟩
    rw [getD_clamp10 l hl a, getD_10_false l hl]
    simp [GateOp.eval]
  | [a, b] =>
    refine ⟨clamp10 a, clamp10 b, fun l hl => ?_⟩
    rw [getD_clamp10 l hl a, getD_clamp10 l hl b]
    simp [GateOp.eval]
  | _ :: _ :: _ :: _ =>
    simp at hins

end PEqualNP.Outside.L_meta_3586

theorem PEqualNP.Outside.L_meta_3586 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) →       Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or →         ∃ (x5 : Fin (11 : ℕ)) (x6 : Fin (11 : ℕ)) (x7 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x7 ∧             x7.size + (2 : ℕ) = x1.size ∧               ∀ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];                 x7.eval (x9 ++ [x9.getD (↑x5) Bool.false || x9.getD (↑x6) Bool.false]) = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 := by
  intro x1 hfan hw9 hg1
  cases hgs : x1.gates with
  | nil =>
    rw [hgs] at hg1
    simp at hg1
  | cons g0 gs1 =>
    cases gs1 with
    | nil =>
      rw [hgs] at hg1
      simp at hg1
    | cons g1 rest =>
      rw [hgs] at hg1
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
        Option.some.injEq] at hg1
      have hg1_fan : g1.inputs.length ≤ 2 := by
        have hmem : g1 ∈ x1.gates := by rw [hgs]; simp
        exact (hfan g1 hmem).2
      obtain ⟨x5, x6, hxy⟩ := PEqualNP.Outside.L_meta_3586.or_eval_le_two_uniform g1.inputs hg1_fan
      refine ⟨x5, x6, { gates := rest, output := x1.output }, ?_, ?_, ?_⟩
      · intro g hg
        apply hfan g
        rw [hgs]
        exact List.mem_cons_of_mem g0 (List.mem_cons_of_mem g1 hg)
      · simp [PEqualNP.CircuitLowerBounds.Circuit.size, hgs]
      · intro x8
        dsimp only
        set x9 : List Bool := List.ofFn x8 ++ [x8 0 || x8 4]
        have hx9_len : x9.length = 10 := by simp [x9]
        have hw1_eq : PEqualNP.Outside.L_meta_3586.stepW (List.ofFn x8) g0 = x9 := by
          have h9 := hw9 x8
          simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, hgs, List.foldl_cons] at h9
          change ((g1 :: rest).foldl PEqualNP.Outside.L_meta_3586.stepW
            (PEqualNP.Outside.L_meta_3586.stepW (List.ofFn x8) g0)).getD 9 false = _ at h9
          have hlt : 9 < (PEqualNP.Outside.L_meta_3586.stepW (List.ofFn x8) g0).length := by
            simp [PEqualNP.Outside.L_meta_3586.stepW]
          rw [PEqualNP.Outside.L_meta_3586.foldl_stepW_getD_lt _ _ 9 hlt] at h9
          simp only [PEqualNP.Outside.L_meta_3586.stepW] at h9 ⊢
          have hget : (List.ofFn x8 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x8).getD i false)]).getD 9 false =
              g0.op.eval (g0.inputs.map fun i => (List.ofFn x8).getD i false) := by
            simp
          rw [hget] at h9
          rw [h9]
        have hw2_eq : PEqualNP.Outside.L_meta_3586.stepW x9 g1 =
            x9 ++ [x9.getD x5.val false || x9.getD x6.val false] := by
          simp only [PEqualNP.Outside.L_meta_3586.stepW, hg1]
          rw [hxy x9 hx9_len]
        simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
          PEqualNP.CircuitLowerBounds.Circuit.wires, hgs, List.foldl_cons]
        change (rest.foldl PEqualNP.Outside.L_meta_3586.stepW
            (x9 ++ [x9.getD x5.val false || x9.getD x6.val false])).getD x1.output false =
          (rest.foldl PEqualNP.Outside.L_meta_3586.stepW
            (PEqualNP.Outside.L_meta_3586.stepW
              (PEqualNP.Outside.L_meta_3586.stepW (List.ofFn x8) g0) g1)).getD x1.output false
        rw [hw1_eq, hw2_eq]
