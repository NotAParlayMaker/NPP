import Mathlib
import PEqualNP.Defs

-- A cut of L-meta-2153 by what the second gate (a NOT) reads. Removing the first two
-- gates turns the circuit into one on eleven inputs: the nine inputs, the first wire
-- (always x_0 or x_4) and the value the NOT gate produces. The NOT reads an input wire,
-- the first gate's wire, or a wire that does not exist yet (reading false, so producing
-- true), or reads nothing at all.

theorem PEqualNP.Outside.R_meta_2153_1
    (notInput : ∀ j : Fin (9 : ℕ), ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      (∀ x : Fin (9 : ℕ) → Bool, D.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)), !(x j)]) =
        (fun x4 : Fin (9 : ℕ) → Bool => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x) →
      (14 : ℕ) ≤ D.size)
    (notFirst : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      (∀ x : Fin (9 : ℕ) → Bool, D.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)), !(x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)))]) =
        (fun x4 : Fin (9 : ℕ) → Bool => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x) →
      (14 : ℕ) ≤ D.size)
    (notConst : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      (∀ x : Fin (9 : ℕ) → Bool, D.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)), true]) =
        (fun x4 : Fin (9 : ℕ) → Bool => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x) →
      (14 : ℕ) ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro C hfan hfirst hfun hsecond
  obtain ⟨g, hget, hnop⟩ : ∃ g, C.gates[(1 : ℕ)]? = some g ∧
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    cases h : C.gates[(1 : ℕ)]? with
    | none => simp [h] at hsecond
    | some g =>
      simp [h] at hsecond
      exact ⟨g, rfl, hsecond⟩
  obtain ⟨g0, gs, hgs⟩ : ∃ g0 gs, C.gates = g0 :: g :: gs := by
    cases h0 : C.gates with
    | nil => simp [h0] at hget
    | cons g0 rest =>
      cases h1 : rest with
      | nil => simp [h0, h1] at hget
      | cons g' gs =>
        obtain ⟨_, hv⟩ := List.getElem?_eq_some_iff.1 hget
        have hg' : g' = g := by simpa [h0, h1] using hv
        subst hg'
        exact ⟨g0, gs, by simp [h0, h1]⟩
  let step := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
      (hi : i < w.length) : (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  have hwiresC : ∀ w, C.wires w = C.gates.foldl step w := fun _ => rfl
  have hsplit : [g0, g] ++ gs = C.gates := by simp [hgs]
  have hfold (w : List Bool) :
      C.gates.foldl step w = gs.foldl step ([g0, g].foldl step w) := by
    rw [← hsplit, List.foldl_append]
  have h0 (x : Fin (9 : ℕ) → Bool) : ([g0, g].foldl step (List.ofFn x)) =
      List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false),
        g.op.eval (g.inputs.map fun i =>
          (List.ofFn x ++
            [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).getD i false)] := by
    simp [step, List.foldl_cons]
  have hv0 (x : Fin (9 : ℕ) → Bool) :
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) =
        (x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))) := by
    have h9 := hfirst x
    rw [hwiresC, hfold, h0] at h9
    rw [keep gs _ 9 (by simp)] at h9
    rw [List.getD_append_right _ _ _ _ (by simp)] at h9
    simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero] at h9
    exact h9
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, C.output⟩
  have hD_eval (x : Fin (9 : ℕ) → Bool) :
      D.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)),
        g.op.eval (g.inputs.map fun i =>
          (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD i false)]) =
        C.eval (List.ofFn x) := by
    show (gs.foldl step (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)),
        g.op.eval (g.inputs.map fun i =>
          (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD i false)])).getD
        C.output false =
      (C.gates.foldl step (List.ofFn x)).getD C.output false
    rw [hfold, h0, hv0]
  have hD_fun (x : Fin (9 : ℕ) → Bool) :
      D.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)),
        g.op.eval (g.inputs.map fun i =>
          (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD i false)]) =
        (fun x4 : Fin (9 : ℕ) → Bool => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x := by
    rw [hD_eval]
    have h := congrFun hfun x
    simpa [PEqualNP.MetaComplexity.circuitFun] using h
  have hfanD : PEqualNP.MetaComplexity.FanInTwo D := fun g' hm =>
    hfan g' (by rw [hgs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
  have hsize : C.size = gs.length + 2 := by
    simp [PEqualNP.CircuitLowerBounds.Circuit.size, hgs]
  cases hin : g.inputs with
  | nil =>
    have hv (x : Fin (9 : ℕ) → Bool) :
        g.op.eval (g.inputs.map fun i =>
          (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD i false) = true := by
      simp [hin, hnop, PEqualNP.CircuitLowerBounds.GateOp.eval]
    have h14 : (14 : ℕ) ≤ gs.length := notConst D hfanD (fun x => by
      have h := hD_fun x
      rw [hv x] at h
      exact h)
    omega
  | cons j rest =>
    have hv (x : Fin (9 : ℕ) → Bool) :
        g.op.eval (g.inputs.map fun i =>
          (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD i false) =
          !((List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD j false) := by
      simp [hin, hnop, PEqualNP.CircuitLowerBounds.GateOp.eval]
    rcases lt_trichotomy j (9 : ℕ) with hj | hj | hj
    · have hr (x : Fin (9 : ℕ) → Bool) :
          (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD j false =
            x ⟨j, hj⟩ := by
        rw [List.getD_append _ _ _ _ (by simp [hj])]
        rw [List.getD_eq_getElem _ _ (by simp [hj])]
        rw [List.getElem_ofFn]
      have h14 : (14 : ℕ) ≤ gs.length := notInput ⟨j, hj⟩ D hfanD (fun x => by
        have h := hD_fun x
        rw [hv x, hr x] at h
        exact h)
      omega
    · subst hj
      have hr (x : Fin (9 : ℕ) → Bool) :
          (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD 9 false =
            (x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))) := by
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
      have h14 : (14 : ℕ) ≤ gs.length := notFirst D hfanD (fun x => by
        have h := hD_fun x
        rw [hv x, hr x] at h
        exact h)
      omega
    · have hr (x : Fin (9 : ℕ) → Bool) :
          (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD j false = false := by
        rw [List.getD_eq_default _ _ (by simp; omega)]
      have hv' (x : Fin (9 : ℕ) → Bool) :
          g.op.eval (g.inputs.map fun i =>
            (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]).getD i false) = true := by
        rw [hv x, hr x]
        rfl
      have h14 : (14 : ℕ) ≤ gs.length := notConst D hfanD (fun x => by
        have h := hD_fun x
        rw [hv' x] at h
        exact h)
      omega
