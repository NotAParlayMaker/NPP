import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1900000 in
theorem PEqualNP.Outside.R_meta_1678_482
    (normalize :
      let f (x : Fin 9 → Bool) :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e =>
          x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
      let ps : Fin 4 → List ℕ := ![[0,1,2,3,4,5,6,7,8],[1,0,5,8,6,2,4,7,3],
        [3,8,5,0,4,2,6,7,1],[8,3,2,1,6,5,4,7,0]];
      let canonical (D : Circuit) := ∀ g, D.gates[0]? = some g →
        ∀ p : Fin 4, g.inputs ≤ g.inputs.map (fun i => (ps p).getD i i);
      let livePins (D : Circuit) := ∀ g, D.gates[0]? = some g → ∀ i ∈ g.inputs, i ≤ 10;
      let computes (D : Circuit) := ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) = f x;
      ∀ D : Circuit, FanInTwo D → computes D → livePins D →
        ∃ E : Circuit, FanInTwo E ∧ E.size = D.size ∧ computes E ∧ livePins E ∧ canonical E)
    (bounded :
      let f (x : Fin 9 → Bool) :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e =>
          x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
      let ps : Fin 4 → List ℕ := ![[0,1,2,3,4,5,6,7,8],[1,0,5,8,6,2,4,7,3],
        [3,8,5,0,4,2,6,7,1],[8,3,2,1,6,5,4,7,0]];
      let canonical (D : Circuit) := ∀ g, D.gates[0]? = some g →
        ∀ p : Fin 4, g.inputs ≤ g.inputs.map (fun i => (ps p).getD i i);
      let livePins (D : Circuit) := ∀ g, D.gates[0]? = some g → ∀ i ∈ g.inputs, i ≤ 10;
      let computes (D : Circuit) := ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) = f x;
      ∀ D : Circuit, FanInTwo D → computes D → livePins D → canonical D → 15 ≤ D.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C fan first computes
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let row (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (z : List Bool) (i : ℕ) (hi : i < z.length) :
      (gs.foldl step z).getD i false = z.getD i false := by
    induction gs generalizing z with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step z g)]
      · exact List.getD_append _ _ _ _ hi
      · simp only [step,List.length_append,List.length_singleton]
        omega
  have clipHead (D : Circuit) (fanD : FanInTwo D) :
      ∃ E : Circuit, FanInTwo E ∧ E.size = D.size ∧
        (∀ g, E.gates[0]? = some g → ∀ i ∈ g.inputs, i ≤ 10) ∧
        ∀ x, E.eval (row x) = D.eval (row x) := by
    rcases D with ⟨gs,o⟩
    cases gs with
    | nil =>
      refine ⟨⟨[],o⟩,fanD,rfl,?_,fun _ => rfl⟩
      intro g h
      cases h
    | cons g gs =>
      let g' : Gate := ⟨g.op,g.inputs.map (min 10)⟩
      let E : Circuit := ⟨g'::gs,o⟩
      refine ⟨E,?_,rfl,?_,?_⟩
      · intro a ha
        change a ∈ g'::gs at ha
        rcases List.mem_cons.mp ha with rfl | mem
        · obtain ⟨good,arity⟩ := fanD g List.mem_cons_self
          exact ⟨good,by simpa only [g',List.length_map] using arity⟩
        · exact fanD a (List.mem_cons_of_mem _ mem)
      · intro a eq i hi
        change some g' = some a at eq
        obtain rfl : g' = a := Option.some.inj eq
        change i ∈ g.inputs.map (min 10) at hi
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
        exact min_le_left _ _
      · intro x
        have len : (row x).length = 10 := by simp [row]
        have equal : step (row x) g' = step (row x) g := by
          simp only [step,g',List.map_map]
          apply congrArg (fun pins => row x ++ [g.op.eval pins])
          apply List.map_congr_left
          intro i _
          by_cases small : i ≤ 10
          · rw [Function.comp_apply,min_eq_right small]
          · rw [Function.comp_apply,min_eq_left (by omega),
              List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
        change (gs.foldl step (step (row x) g')).getD o false =
          (gs.foldl step (step (row x) g)).getD o false
        rw [equal]
  rcases C with ⟨gates,o⟩
  cases gates with
  | nil =>
    let x : Fin 9 → Bool := fun _ => true
    have contradiction := first x
    change false = true at contradiction
    exact Bool.noConfusion contradiction
  | cons g gs =>
    let D : Circuit := ⟨gs,o⟩
    have fanD : FanInTwo D := fun a ha => fan a (List.mem_cons_of_mem _ ha)
    have front (x : Fin 9 → Bool) : step (List.ofFn x) g = row x := by
      have eq := first x
      change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at eq
      rw [keep _ _ _ (by simp [step])] at eq
      have read : (step (List.ofFn x) g).getD 9 false = g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
        unfold step
        rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.sub_self]
        rfl
      rw [read] at eq
      change List.ofFn x ++ [_] = List.ofFn x ++ [_]
      rw [eq]
    have correct (x : Fin 9 → Bool) : D.eval (row x) = f x := by
      have eq := congrFun computes x
      change (gs.foldl step (step (List.ofFn x) g)).getD o false = _ at eq
      rw [front] at eq
      refine eq.trans ?_
      simp only [f,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
      rfl
    obtain ⟨N,fanN,szN,capN,rowN⟩ := clipHead D fanD
    obtain ⟨E,fanE,szE,compE,capE,canon⟩ :=
      normalize N fanN (fun x => (rowN x).trans (correct x)) capN
    have tail := bounded E fanE compE capE canon
    rw [szE,szN] at tail
    exact Nat.succ_le_succ tail
