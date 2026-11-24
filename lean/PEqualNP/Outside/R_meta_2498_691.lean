import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2200000 in
theorem PEqualNP.Outside.R_meta_2498_691
    (sizeSmaller :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
      C.output < 9 + C.size →
      (∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 9 + j ∨ i = 24) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) →
      circuitFun 9 C = f →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          let w (x : Fin 9 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false
          ((∃ b : Bool, ∀ x, x v = false → w x (9+j) = b) ∨
            ∃ i < 9+j, ∀ x, x v = false → w x (9+j) = w x i)) → S.card ≤ 3) → False)
    (sizeFifteen :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : Circuit, FanInTwo C → C.size = 15 →
      C.output < 9 + C.size →
      (∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 9 + j ∨ i = 24) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) →
      circuitFun 9 C = f →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          let w (x : Fin 9 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false
          ((∃ b : Bool, ∀ x, x v = false → w x (9+j) = b) ∨
            ∃ i < 9+j, ∀ x, x v = false → w x (9+j) = w x i)) → S.card ≤ 3) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (16 : ℕ) ≤ x1.size := by
  intro C fan headWire computes few
  classical
  by_contra! small
  let cap (n i : ℕ) := if i < n then i else 24
  let normalize (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (cap n)⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have readCap (w : List Bool) (short : w.length ≤ 24) (i : ℕ) :
      w.getD (cap w.length i) false = w.getD i false := by
    unfold cap
    split_ifs with h
    · rfl
    · rw [List.getD_eq_default _ _ short, List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
  have gateEq (w : List Bool) (short : w.length ≤ 24) (g : Gate) :
      step w (normalize w.length g) = step w g := by
    have eq :
        (g.inputs.map (cap w.length)).map (fun i => w.getD i false) =
          g.inputs.map (fun i => w.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => readCap w short i)
    simp only [step, normalize, eq]
  have foldEq (gs : List Gate) (w : List Bool) (short : w.length + gs.length ≤ 24) :
      ((gs.mapIdx fun j => normalize (w.length+j)).foldl step w) = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.mapIdx_cons, Nat.add_zero, List.foldl_cons, gateEq w (by
        simp only [List.length_cons] at short
        omega)]
      have len : (step w g).length = w.length + 1 := by simp [step]
      have shift : (gs.mapIdx fun j => normalize (w.length + (j+1))) =
          (gs.mapIdx fun j => normalize ((step w g).length+j)) := by
        have indices :
            (fun j : ℕ => normalize (w.length + (j+1))) =
              (fun j : ℕ => normalize ((step w g).length+j)) := by
          funext j
          exact congrArg normalize (by omega)
        rw [indices]
      rw [shift]
      apply ih
      simp only [len, List.length_cons] at *
      omega
  let D : Circuit := ⟨C.gates.mapIdx (fun j => normalize (9+j)), C.output⟩
  have size : D.size = C.size := List.length_mapIdx
  have fanD : FanInTwo D := by
    intro g hg
    change g ∈ C.gates.mapIdx (fun j => normalize (9+j)) at hg
    obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp hg
    obtain ⟨op, arity⟩ := fan C.gates[j] (List.getElem_mem hj)
    exact ⟨op, by simpa only [normalize, List.length_map] using arity⟩
  have bounded (j : ℕ) (g : Gate) (hg : D.gates[j]? = some g) :
      ∀ i ∈ g.inputs, i < 9+j ∨ i = 24 := by
    change (C.gates.mapIdx (fun j => normalize (9+j)))[j]? = some g at hg
    rw [List.getElem?_mapIdx] at hg
    cases h : C.gates[j]? with
    | none => simp [h] at hg
    | some source =>
      simp only [h, Option.map_some, Option.some.injEq] at hg
      subst g
      intro i hi
      change i ∈ source.inputs.map (cap (9+j)) at hi
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hi
      by_cases hvalid : k < 9+j
      · exact Or.inl (by simpa only [cap, ite_eq_left hvalid] using hvalid)
      · exact Or.inr (by simp only [cap, ite_eq_right hvalid])
  have wiresEq (x : Fin 9 → Bool) : D.wires (List.ofFn x) = C.wires (List.ofFn x) := by
    change ((C.gates.mapIdx fun j => normalize (9+j)).foldl step (List.ofFn x)) =
      C.gates.foldl step (List.ofFn x)
    have len : (List.ofFn x).length = 9 := List.length_ofFn
    have short : (List.ofFn x).length + C.gates.length ≤ 24 := by
      change (List.ofFn x).length + C.size ≤ 24
      omega
    simpa only [len] using foldEq C.gates (List.ofFn x) short
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have computesD : circuitFun 9 D = f := by
    funext x
    have hx := congrFun computes x
    change (D.wires (List.ofFn x)).getD C.output false = f x
    rw [wiresEq]
    change circuitFun 9 C x = _
    rw [hx]
    rfl
  have headD (x : Fin 9 → Bool) :
      (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 1) := by
    rw [wiresEq]
    exact headWire x
  have fewD (v : Fin 9) (hv : v ∈ ([0,1,2,3,5,8] : List (Fin 9))) (S : Finset ℕ)
      (hS : ∀ j ∈ S, j < D.size ∧
        let w (x : Fin 9 → Bool) (i : ℕ) := (D.wires (List.ofFn x)).getD i false
        ((∃ b : Bool, ∀ x, x v = false → w x (9+j) = b) ∨
          ∃ i < 9+j, ∀ x, x v = false → w x (9+j) = w x i)) : S.card ≤ 3 := by
    apply few v hv S
    simpa only [size, wiresEq] using hS
  have lengthRun (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have validOut : D.output < 9+D.size := by
    by_contra! h
    let edge : Fin 9 → Bool := fun j => j == 0 || j == 1
    have value : circuitFun 9 D edge = true := (congrFun computesD edge).trans (by decide)
    change (D.gates.foldl step (List.ofFn edge)).getD D.output false = true at value
    have bad : (D.gates.foldl step (List.ofFn edge)).getD D.output false = false := by
      apply List.getD_eq_default
      rwa [lengthRun, List.length_ofFn]
    exact Bool.noConfusion (bad.symm.trans value)
  by_cases tight : D.size = 15
  · exact sizeFifteen D fanD tight validOut bounded headD computesD fewD
  · exact sizeSmaller D fanD (by omega) validOut bounded headD computesD fewD
