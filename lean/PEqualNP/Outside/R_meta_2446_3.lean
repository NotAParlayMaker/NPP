import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2446_3
    (hEdges :
      ∀ p ∈ ([((0 : Fin 9), (1 : Fin 9)), ((0 : Fin 9), (4 : Fin 9))] : List (Fin 9 × Fin 9)),
        ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
          ∃ x : Fin 9 → Bool,
            D.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠
              (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
               x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
               x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hCycleNonEdges :
      ∀ p ∈ ([((0 : Fin 9), (2 : Fin 9)), ((0 : Fin 9), (3 : Fin 9))] : List (Fin 9 × Fin 9)),
        ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
          ∃ x : Fin 9 → Bool,
            D.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠
              (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
               x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
               x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hInnerDeg2 :
      ∀ p ∈ ([((0 : Fin 9), (6 : Fin 9)), ((4 : Fin 9), (6 : Fin 9))] : List (Fin 9 × Fin 9)),
        ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
          ∃ x : Fin 9 → Bool,
            D.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠
              (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
               x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
               x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x5 : Fin (9 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 x1.1 || x5 x1.2)) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x3.size := by
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (l : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (l.foldl step w).getD i false = w.getD i false := by
    induction l generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  intro p hp C hC hfirst hfun
  by_contra hlt
  have hsize : C.size ≤ 15 := by omega
  rcases hC_gates : C.gates with _ | ⟨g0, gs⟩
  · have h9 := hfirst (fun _ => true)
    have hw : C.wires (List.ofFn (fun _ : Fin 9 => true)) = List.ofFn (fun _ : Fin 9 => true) := by
      change C.gates.foldl step (List.ofFn (fun _ : Fin 9 => true)) = _
      rw [hC_gates]
      rfl
    rw [hw] at h9
    have hfalse : (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
      rfl
    rw [hfalse] at h9
    cases h9
  · let D : PEqualNP.CircuitLowerBounds.Circuit := { gates := gs, output := C.output }
    have hD_fan : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      exact hC g (by rw [hC_gates]; exact List.mem_cons_of_mem _ hg)
    have hD_size : D.size ≤ 14 := by
      have hlen : C.gates.length ≤ 15 := hsize
      rw [hC_gates, List.length_cons] at hlen
      change gs.length ≤ 14
      omega
    have hD_eval : ∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x p.1 || x p.2]) = C.eval (List.ofFn x) := by
      intro x
      let w0 := List.ofFn x
      let v0 := g0.op.eval (g0.inputs.map fun i => w0.getD i false)
      have hw0_len : w0.length = 9 := by simp [w0]
      have hCw : C.wires w0 = gs.foldl step (w0 ++ [v0]) := by
        change C.gates.foldl step w0 = gs.foldl step (w0 ++ [v0])
        rw [hC_gates]
        rfl
      have hv0 : v0 = (x p.1 || x p.2) := by
        have hget : (C.wires w0).getD 9 false = v0 := by
          rw [hCw, keep gs (w0 ++ [v0]) 9 (by simp [hw0_len])]
          rw [List.getD_eq_getElem?_getD, ← hw0_len, List.getElem?_append_right (le_refl _)]
          simp
        exact hget.symm.trans (hfirst x)
      have hDw : D.wires (w0 ++ [x p.1 || x p.2]) = C.wires w0 := by
        rw [hCw, ← hv0]
        rfl
      show (D.wires (w0 ++ [x p.1 || x p.2])).getD C.output false = (C.wires w0).getD C.output false
      rw [hDw]
    have hmiss : ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
           x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hEdges (0, 1) (by simp) D hD_fan hD_size
      · exact hCycleNonEdges (0, 2) (by simp) D hD_fan hD_size
      · exact hCycleNonEdges (0, 3) (by simp) D hD_fan hD_size
      · exact hEdges (0, 4) (by simp) D hD_fan hD_size
      · exact hInnerDeg2 (0, 6) (by simp) D hD_fan hD_size
      · exact hInnerDeg2 (4, 6) (by simp) D hD_fan hD_size
    rcases hmiss with ⟨x, hx⟩
    apply hx
    rw [hD_eval x]
    exact congrFun hfun x
