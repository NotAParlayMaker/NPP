import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3081

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl stepW w

theorem stepW_len (w : List Bool) (g : Gate) : (stepW w g).length = w.length + 1 := by
  simp [stepW]

theorem runW_len (gs : List Gate) : ∀ w : List Bool, (runW gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [runW]
  | cons g gs ih =>
    intro w
    change (runW gs (stepW w g)).length = _
    rw [ih, stepW_len]
    simp only [List.length_cons]
    omega

theorem runW_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (runW gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; simp [runW]
  | cons g gs ih =>
    intro w i hi
    change (runW gs (stepW w g)).getD i false = _
    rw [ih (stepW w g) i (by rw [stepW_len]; omega)]
    exact List.getD_append w [g.op.eval (g.inputs.map fun i => w.getD i false)] false i hi

def readsGate (g : Gate) (v : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs

theorem stepW_eval_agree (w1 w2 : List Bool) (g : Gate) (v : ℕ)
    (hagree : ∀ i, i ≠ v → w1.getD i false = w2.getD i false)
    (hnot : ¬ readsGate g v) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  by_cases hnotop : g.op = GateOp.not
  · cases hinp : g.inputs with
    | nil => simp [hnotop, GateOp.eval]
    | cons u us =>
      have huv : u ≠ v := fun e => hnot (Or.inl ⟨hnotop, by simp [hinp, e]⟩)
      simp only [hnotop, GateOp.eval, List.map_cons, List.headD_cons]
      exact congrArg Bool.not (hagree u huv)
  · congr 1
    apply List.map_congr_left
    intro u hu
    exact hagree u (fun e => hnot (Or.inr ⟨hnotop, e ▸ hu⟩))

theorem stepW_agree (w1 w2 : List Bool) (g : Gate) (v : ℕ)
    (hlen : w1.length = w2.length)
    (hagree : ∀ i, i ≠ v → w1.getD i false = w2.getD i false)
    (hnot : ¬ readsGate g v) :
    ∀ i, i ≠ v → (stepW w1 g).getD i false = (stepW w2 g).getD i false := by
  intro i hiv
  have hev := stepW_eval_agree w1 w2 g v hagree hnot
  by_cases hi : i < w1.length
  · simp only [stepW]
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hlen ▸ hi)]
    exact hagree i hiv
  · by_cases hie : i = w1.length
    · subst hie
      simp only [stepW, hev]
      rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length]
      rw [hlen, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
    · rw [List.getD_eq_default _ _ (by rw [stepW_len]; omega)]
      rw [List.getD_eq_default _ _ (by rw [stepW_len]; omega)]

theorem runW_agree (gs : List Gate) : ∀ (w1 w2 : List Bool) (v : ℕ),
    w1.length = w2.length →
    (∀ i, i ≠ v → w1.getD i false = w2.getD i false) →
    (∀ g ∈ gs, ¬ readsGate g v) →
    ∀ i, i ≠ v → (runW gs w1).getD i false = (runW gs w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 v _ hagree _ i hiv; simpa [runW] using hagree i hiv
  | cons g gs ih =>
    intro w1 w2 v hlen hagree hnone i hiv
    have hg : ¬ readsGate g v := hnone g List.mem_cons_self
    have hrest : ∀ g1 ∈ gs, ¬ readsGate g1 v := fun g1 hg1 => hnone g1 (List.mem_cons_of_mem _ hg1)
    exact ih (stepW w1 g) (stepW w2 g) v (by rw [stepW_len, stepW_len, hlen])
      (stepW_agree w1 w2 g v hlen hagree hg) hrest i hiv

theorem getD_ofFn_eq {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem prove_goal : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 = (0 : ℕ) ∨ x5 = (2 : ℕ) → ∃ x7 ∈ List.drop (1 : ℕ) x2.gates, x1 x7 x5 := by
  dsimp only
  intro C hw9 hfun v hv
  by_contra hnone
  have hx1 : ∀ g ∈ C.gates.drop 1, ¬ readsGate g v := fun g hg hread => hnone ⟨g, hg, hread⟩
  cases hgates : C.gates with
  | nil =>
    let z0 : Fin 9 → Bool := fun i => decide (i.val = 0)
    have hz0 := hw9 z0
    have hlen0 : (C.wires (List.ofFn z0)).length = 9 := by
      change (runW C.gates (List.ofFn z0)).length = 9
      rw [hgates, runW_len, List.length_ofFn]
      rfl
    have hdef : (C.wires (List.ofFn z0)).getD 9 false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hdef] at hz0
    revert hz0
    decide
  | cons g0 gs =>
    have hnone_gs : ∀ g ∈ gs, ¬ readsGate g v := by
      intro g hg
      exact hx1 g (by rw [hgates]; simpa using hg)
    have hvlt : v < 9 := by rcases hv with rfl | rfl <;> omega
    by_cases hout : C.output = v
    · let zv : Fin 9 → Bool := fun i => decide (i.val = v)
      have heval : circuitFun 9 C zv = true := by
        change (runW C.gates (List.ofFn zv)).getD C.output false = true
        rw [hout, runW_getD_lt C.gates (List.ofFn zv) v (by simp [hvlt]), getD_ofFn_eq zv v hvlt]
        simp [zv]
      have hpet : (fun (x4 : Fin 9 → Bool) => x4 0 && x4 1 || x4 1 && x4 2 || x4 2 && x4 3 || x4 3 && x4 4 || x4 4 && x4 0 || x4 0 && x4 5 || x4 1 && x4 6 || x4 2 && x4 7 || x4 3 && x4 8 || x4 5 && x4 7 || x4 6 && x4 8 || x4 8 && x4 5) zv = false := by
        rcases hv with rfl | rfl <;> decide
      have hf := congrArg (fun f => f zv) hfun
      change circuitFun 9 C zv = _ at hf
      rw [heval, hpet] at hf
      cases hf
    · have hwires_eq : ∀ z : Fin 9 → Bool,
          C.wires (List.ofFn z) = runW gs (stepW (List.ofFn z) g0) := by
        intro z
        change runW C.gates (List.ofFn z) = runW gs (stepW (List.ofFn z) g0)
        rw [hgates]
        rfl
      have hwire9 : ∀ z : Fin 9 → Bool,
          (stepW (List.ofFn z) g0).getD 9 false = (z 0 || z 2) := by
        intro z
        have hlen10 : (stepW (List.ofFn z) g0).length = 10 := by
          rw [stepW_len, List.length_ofFn]
        have hlt9 : 9 < (stepW (List.ofFn z) g0).length := by omega
        rw [← runW_getD_lt gs (stepW (List.ofFn z) g0) 9 hlt9]
        rw [← hwires_eq z]
        exact hw9 z
      let a : Fin 9 → Bool :=
        if v = 0 then fun i => decide (i.val = 2 ∨ i.val = 4)
        else fun i => decide (i.val = 0 ∨ i.val = 7)
      let b : Fin 9 → Bool :=
        if v = 0 then fun i => decide (i.val = 0 ∨ i.val = 2 ∨ i.val = 4)
        else fun i => decide (i.val = 0 ∨ i.val = 2 ∨ i.val = 7)
      have hlen_ab : (stepW (List.ofFn a) g0).length = (stepW (List.ofFn b) g0).length := by
        rw [stepW_len, stepW_len, List.length_ofFn, List.length_ofFn]
      have hagree_step : ∀ i, i ≠ v →
          (stepW (List.ofFn a) g0).getD i false = (stepW (List.ofFn b) g0).getD i false := by
        intro i hiv
        by_cases hi9 : i < 9
        · have hlenA : (List.ofFn a).length = 9 := List.length_ofFn
          have hlenB : (List.ofFn b).length = 9 := List.length_ofFn
          simp only [stepW]
          rw [List.getD_append _ _ _ _ (by rw [hlenA]; exact hi9), List.getD_append _ _ _ _ (by rw [hlenB]; exact hi9)]
          rw [getD_ofFn_eq a i hi9, getD_ofFn_eq b i hi9]
          rcases hv with rfl | rfl <;> simp [a, b, hiv]
        · by_cases hi9eq : i = 9
          · subst hi9eq
            rw [hwire9 a, hwire9 b]
            rcases hv with rfl | rfl <;> decide
          · rw [List.getD_eq_default _ _ (by rw [stepW_len, List.length_ofFn]; omega)]
            rw [List.getD_eq_default _ _ (by rw [stepW_len, List.length_ofFn]; omega)]
      have heq_out : circuitFun 9 C a = circuitFun 9 C b := by
        change (C.wires (List.ofFn a)).getD C.output false = (C.wires (List.ofFn b)).getD C.output false
        rw [hwires_eq a, hwires_eq b]
        exact runW_agree gs (stepW (List.ofFn a) g0) (stepW (List.ofFn b) g0) v hlen_ab hagree_step hnone_gs C.output hout
      have hfa := congrArg (fun f => f a) hfun
      have hfb := congrArg (fun f => f b) hfun
      change circuitFun 9 C a = _ at hfa
      change circuitFun 9 C b = _ at hfb
      rw [heq_out] at hfa
      have hdiff : (fun (x4 : Fin 9 → Bool) => x4 0 && x4 1 || x4 1 && x4 2 || x4 2 && x4 3 || x4 3 && x4 4 || x4 4 && x4 0 || x4 0 && x4 5 || x4 1 && x4 6 || x4 2 && x4 7 || x4 3 && x4 8 || x4 5 && x4 7 || x4 6 && x4 8 || x4 8 && x4 5) a ≠ (fun (x4 : Fin 9 → Bool) => x4 0 && x4 1 || x4 1 && x4 2 || x4 2 && x4 3 || x4 3 && x4 4 || x4 4 && x4 0 || x4 0 && x4 5 || x4 1 && x4 6 || x4 2 && x4 7 || x4 3 && x4 8 || x4 5 && x4 7 || x4 6 && x4 8 || x4 8 && x4 5) b := by
        rcases hv with rfl | rfl <;> decide
      exact hdiff (hfa.symm.trans hfb)

end PEqualNP.Outside.L_meta_3081

theorem PEqualNP.Outside.L_meta_3081 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 = (0 : ℕ) ∨ x5 = (2 : ℕ) → ∃ x7 ∈ List.drop (1 : ℕ) x2.gates, x1 x7 x5 :=
  PEqualNP.Outside.L_meta_3081.prove_goal
