import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2841_731
    (base : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (overlap : ∀ (C : Circuit) (T : Finset (Fin 9)), FanInTwo C →
      T ∈ ([{0,1},{0,2},{0,3},{0,6},{1,4},{2,4},{3,4},{4,6}] : List (Finset (Fin 9))) →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4,decide (∃ a ∈ T,x a = true)]) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) → 14 ≤ C.size)
    (adjacent : ∀ (C : Circuit) (T : Finset (Fin 9)), FanInTwo C →
      T ∈ ([{1,2},{1,6},{2,3},{2,7}] : List (Finset (Fin 9))) →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4,decide (∃ a ∈ T,x a = true)]) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) → 14 ≤ C.size)
    (separate : ∀ (C : Circuit) (T : Finset (Fin 9)), FanInTwo C →
      T ∈ ([{1,3},{1,5},{1,7},{1,8},{2,6},{2,8},{3,6},{6,7}] : List (Finset (Fin 9))) →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4,decide (∃ a ∈ T,x a = true)]) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) → 14 ≤ C.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x6 ∈ x2, x5 x6 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) → (14 : ℕ) ≤ x1.size := by
  classical
  let edgeF := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  let targetManual := fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let remap (ρ : ℕ → ℕ) (C : Circuit) : Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op,g.inputs.map ρ⟩),ρ C.output⟩
  have transport (C : Circuit) (ρ : ℕ → ℕ) (xs ys : List Bool)
      (read : ∀ T : List Bool, T.length ≤ C.size → ∀ i : ℕ,
        (ys ++ T).getD (ρ i) false = (xs ++ T).getD i false) :
      (remap ρ C).eval ys = C.eval xs := by
    have run (gs : List Gate) (T : List Bool) (room : T.length + gs.length ≤ C.size) :
        ∃ U : List Bool,
          (gs.map (fun g => Gate.mk g.op (g.inputs.map ρ))).foldl step (ys ++ T) = ys ++ U ∧
          gs.foldl step (xs ++ T) = xs ++ U ∧ U.length = T.length + gs.length := by
      induction gs generalizing T with
      | nil => exact ⟨T,by simp,by simp,by simp⟩
      | cons g gs ih =>
        have eq : g.op.eval ((g.inputs.map ρ).map fun i => (ys ++ T).getD i false) =
            g.op.eval (g.inputs.map fun i => (xs ++ T).getD i false) := by
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact read T (by simp only [List.length_cons] at room; omega) i
        let v := g.op.eval (g.inputs.map fun i => (xs ++ T).getD i false)
        obtain ⟨U,hy,hx,hlen⟩ := ih (T ++ [v]) (by simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at *; omega)
        refine ⟨U,?_,?_,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hlen⟩
        · simpa only [List.map_cons,List.foldl_cons,step,eq,List.append_assoc] using hy
        · simpa only [List.foldl_cons,step,List.append_assoc] using hx
    obtain ⟨U,hy,hx,hlen⟩ := run C.gates [] (by change 0 + C.gates.length ≤ C.gates.length; omega)
    simp only [List.append_nil] at hy hx hlen
    change ((C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))).foldl step ys).getD (ρ C.output) false =
      (C.gates.foldl step xs).getD C.output false
    rw [hy,hx]
    exact read U (by change U.length ≤ C.gates.length; simpa only [List.length_nil,Nat.zero_add] using hlen.le) C.output
  have fanMap (C : Circuit) (ρ : ℕ → ℕ) (h : FanInTwo C) : FanInTwo (remap ρ C) := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa only [List.length_map] using h a ha
  have lowBound (C : Circuit) (T : Finset (Fin 9)) (k : ℕ)
      (hk : k < 10 ∨ k = 10 + C.size)
      (hmask : ∀ x : Fin 9 → Bool, decide (∃ a ∈ T, x a = true) =
        (List.ofFn x ++ [x 0 || x 4]).getD k false)
      (fan : FanInTwo C)
      (correct : ∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 4,decide (∃ a ∈ T, x a = true)]) = edgeF x) :
      14 ≤ C.size := by
    let ρ (i : ℕ) := if i < 10 then i else if i = 10 then k else i-1
    let D := remap ρ C
    have works (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 4]) = edgeF x := by
      let ys := List.ofFn x ++ [x 0 || x 4]
      let b := decide (∃ a ∈ T, x a = true)
      let xs := ys ++ [b]
      have ly : ys.length = 10 := by simp [ys]
      have lx : xs.length = 11 := by simp [xs,ly]
      have eq := transport C ρ xs ys (by
        intro U hU i
        by_cases hi : i < 10
        · have r : ρ i = i := by simp [ρ,hi]
          rw [r,List.getD_append ys U false i (by omega),List.getD_append xs U false i (by omega)]
          exact (List.getD_append ys [b] false i (by omega)).symm
        · by_cases he : i = 10
          · subst i
            have r : ρ 10 = k := by simp [ρ]
            have keep : (ys ++ U).getD k false = ys.getD k false := by
              rcases hk with hk | rfl
              · exact List.getD_append _ _ _ _ (by omega)
              · rw [List.getD_eq_default _ _ (by simp only [List.length_append]; omega),
                    List.getD_eq_default _ _ (by omega)]
            rw [r,keep,List.getD_append xs U false 10 (by omega)]
            change ys.getD k false = (ys ++ [b]).getD 10 false
            rw [List.getD_append_right ys [b] false 10 (by omega),ly]
            simpa [b,ys] using (hmask x).symm
          · have ge : 11 ≤ i := by omega
            have r : ρ i = i-1 := by simp [ρ,hi,he]
            rw [r,List.getD_append_right ys U false (i-1) (by omega),
              List.getD_append_right xs U false i (by omega),ly,lx]
            congr 1 <;> omega)
      exact eq.trans (by simpa only [xs,ys,List.append_assoc,List.singleton_append] using correct x)
    let E : Circuit := ⟨⟨GateOp.or,[0,4]⟩ :: D.gates,D.output⟩
    have fanE : FanInTwo E := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp,by decide⟩
      · exact fanMap C ρ fan g hg
    have calcE : circuitFun 9 E =
        (fun x : Fin 9 → Bool => edgeF x) := by
      funext x
      have first : step (List.ofFn x) ⟨GateOp.or,[0,4]⟩ = List.ofFn x ++ [x 0 || x 4] := by
        have ev (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
          cases a <;> cases b <;> rfl
        change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false,(List.ofFn x).getD 4 false]] = _
        rw [ev]
        rfl
      change (D.gates.foldl step (step (List.ofFn x) ⟨GateOp.or,[0,4]⟩)).getD D.output false = edgeF x
      rw [first]
      exact works x
    have table : (fun x : Fin 9 → Bool => edgeF x) = targetManual := by decide +kernel
    have lower := base E fanE (calcE.trans table)
    have sizeE : E.size = C.size + 1 := by
      change D.gates.length + 1 = C.gates.length + 1
      simp only [D,remap,List.length_map]
    omega
  let σ : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  have flipCircuit (C : Circuit) (T : Finset (Fin 9)) (fan : FanInTwo C)
      (correct : ∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 4,decide (∃ a ∈ T, x a = true)]) = edgeF x) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++
          [x 0 || x 4,decide (∃ a ∈ T.image σ, x a = true)]) = edgeF x := by
    let ρ (i : ℕ) := if h : i < 9 then (σ ⟨i,h⟩).val else i
    let D := remap ρ C
    have first : ∀ (x : Fin 9 → Bool) (b : Bool) (i : Fin 11),
        (List.ofFn x ++ [x 0 || x 4,b]).getD (ρ i.val) false =
        (List.ofFn (fun j => x (σ j)) ++ [x (σ 0) || x (σ 4),b]).getD i.val false := by
      decide +kernel
    have bound : ∀ i < 11, ρ i < 11 := by
      intro i hi
      interval_cases i <;> decide +kernel
    have symmF : ∀ x : Fin 9 → Bool, edgeF (fun j => x (σ j)) = edgeF x := by decide +kernel
    refine ⟨D,fanMap C ρ fan,by change D.gates.length = C.gates.length; simp only [D,remap,List.length_map],?_⟩
    intro x
    have mask : decide (∃ a ∈ T, x (σ a) = true) =
        decide (∃ a ∈ T.image σ, x a = true) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨a,ha,hx⟩
        exact ⟨σ a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,hx⟩
      · rintro ⟨b,hb,hx⟩
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
        exact ⟨a,ha,hx⟩
    let ys := List.ofFn x ++ [x 0 || x 4,decide (∃ a ∈ T.image σ, x a = true)]
    let xs := List.ofFn (fun j => x (σ j)) ++
      [x (σ 0) || x (σ 4),decide (∃ a ∈ T, x (σ a) = true)]
    have ly : ys.length = 11 := by simp [ys]
    have lx : xs.length = 11 := by simp [xs]
    have eq := transport C ρ xs ys (by
      intro U _ i
      by_cases hi : i < 11
      · rw [List.getD_append ys U false (ρ i) (by rw [ly]; exact bound i hi),
          List.getD_append xs U false i (by omega)]
        simpa only [xs,ys,mask] using first x (decide (∃ a ∈ T.image σ, x a = true)) ⟨i,hi⟩
      · have r : ρ i = i := by simp [ρ,show ¬ i < 9 by omega]
        rw [r,List.getD_append_right ys U false i (by omega),
          List.getD_append_right xs U false i (by omega),ly,lx])
    exact eq.trans ((correct (fun j => x (σ j))).trans (symmF x))
  let A : List (Finset (Fin 9)) := [{0,1},{0,2},{0,3},{0,6},{1,4},{2,4},{3,4},{4,6}]
  let B : List (Finset (Fin 9)) := [{1,2},{1,6},{2,3},{2,7}]
  let H : List (Finset (Fin 9)) := [{1,3},{1,5},{1,7},{1,8},{2,6},{2,8},{3,6},{6,7}]
  have classify : ∀ T : Finset (Fin 9), T.card ≤ 2 →
      T = ∅ ∨ (∃ a : Fin 9, T = {a}) ∨ T = {0,4} ∨
      T ∈ A ∨ T ∈ B ∨ T ∈ H ∨ T.image σ ∈ A ∨ T.image σ ∈ B ∨ T.image σ ∈ H := by
    decide +kernel
  intro C T fan card correct
  change ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4,decide (∃ a ∈ T,x a = true)]) = edgeF x at correct
  rcases classify T card with rfl | ⟨a,rfl⟩ | rfl | ha | hb | hh | ha | hb | hh
  · apply lowBound C ∅ (10+C.size) (Or.inr rfl) ?_ fan correct
    intro x
    rw [List.getD_eq_default _ _ (by simp)]
    simp
  · apply lowBound C {a} a.val (Or.inl (by have := a.isLt; omega)) ?_ fan correct
    fin_cases a <;> decide +kernel
  · exact lowBound C {0,4} 9 (Or.inl (by decide)) (by decide +kernel) fan correct
  · exact overlap C T fan ha correct
  · exact adjacent C T fan hb correct
  · exact separate C T fan hh correct
  · obtain ⟨D,hf,hs,he⟩ := flipCircuit C T fan correct
    have lower := overlap D (T.image σ) hf ha he
    omega
  · obtain ⟨D,hf,hs,he⟩ := flipCircuit C T fan correct
    have lower := adjacent D (T.image σ) hf hb he
    omega
  · obtain ⟨D,hf,hs,he⟩ := flipCircuit C T fan correct
    have lower := separate D (T.image σ) hf hh he
    omega
