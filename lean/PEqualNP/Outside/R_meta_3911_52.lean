import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3911_52
    (high : ∀ k ∈ ([1,2,3] : List (Fin 9)), ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y k)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (h04 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (h06 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (h46 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) : ∀ x1 ∈ [[(1 : Fin (11 : ℕ)), (3 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))]],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];           x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  classical
  intro pins member D fan small
  let edge := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  by_contra denied
  have correct (x : Fin 9 → Bool) :
      let w := List.ofFn x ++ [x 0 || x 2]
      D.eval (w ++ [GateOp.and.eval (pins.map fun i => w.getD i.val false)]) = edge x := by
    exact Classical.byContradiction fun ne => denied ⟨x,ne⟩
  have classification : ∃ (a b i j : Fin 9) (σ : Fin 9 → Fin 9),
      pins = [a.castLE (by decide), b.castLE (by decide)] ∧
      (i,j) ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)) ∧
      ((σ a = i ∧ σ b = j) ∨ (σ a = j ∧ σ b = i)) ∧
      ∀ x : Fin 9 → Bool, edge (x ∘ σ) = edge x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨1,3,0,2, ![3,2,1,0,4,8,7,6,5],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 8 && x 6) || (x 7 && x 5) || (x 5 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨1,4,0,6, ![1,0,5,8,6,2,4,7,3],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 2 && x 7) || (x 4 && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨1,6,0,4, ![1,0,5,8,6,2,4,7,3],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 2 && x 7) || (x 4 && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨1,8,0,3, ![1,0,5,8,6,2,4,7,3],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 2 && x 7) || (x 4 && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨3,4,0,4, ![3,2,1,0,4,8,7,6,5],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 8 && x 6) || (x 7 && x 5) || (x 5 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨3,5,0,2, ![3,8,5,0,4,2,6,7,1],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 8 && x 6) || (x 5 && x 7) || (x 0 && x 1) || (x 2 && x 7) || (x 6 && x 1) || (x 1 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨3,6,0,6, ![3,8,5,0,4,2,6,7,1],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 8 && x 6) || (x 5 && x 7) || (x 0 && x 1) || (x 2 && x 7) || (x 6 && x 1) || (x 1 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨3,7,0,6, ![3,2,1,0,4,8,7,6,5],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 8 && x 6) || (x 7 && x 5) || (x 5 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨3,8,0,1, ![3,8,5,0,4,2,6,7,1],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 8 && x 6) || (x 5 && x 7) || (x 0 && x 1) || (x 2 && x 7) || (x 6 && x 1) || (x 1 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨4,6,4,6, ![0,1,2,3,4,5,6,7,8],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨4,7,4,6, ![0,5,8,3,4,1,7,6,2],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨4,8,0,6, ![8,3,2,1,6,5,4,7,0],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 8 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 3 && x 4) || (x 2 && x 7) || (x 1 && x 0) || (x 5 && x 7) || (x 4 && x 0) || (x 0 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · refine ⟨6,8,0,4, ![2,3,8,5,7,1,4,6,0],rfl,by decide,by decide,?_⟩
      intro x
      change ((x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 1) || (x 3 && x 4) || (x 8 && x 6) || (x 5 && x 0) || (x 1 && x 6) || (x 4 && x 0) || (x 0 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
  obtain ⟨a,b,i,j,σ,rfl,representative,pair,automorphism⟩ := classification
  let ρ (k : ℕ) := if h : k < 9 then (σ ⟨k,h⟩).val else if k=9 then 10 else if k=10 then 9 else k
  let ren (g : Gate) : Gate := ⟨g.op,g.inputs.map ρ⟩
  let ga : Gate := ⟨.and,[(σ a).val,(σ b).val]⟩
  let go : Gate := ⟨.or,[(σ 0).val,(σ 2).val]⟩
  let C : Circuit := ⟨ga :: go :: D.gates.map ren,ρ D.output⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  have length_eq : C.size = D.size + 2 := by
    change (ga :: go :: D.gates.map ren).length = D.gates.length + 2
    simp
  have ff : FanInTwo C := by
    intro g hg
    change g ∈ ga :: go :: D.gates.map ren at hg
    simp only [List.mem_cons,List.mem_map] at hg
    rcases hg with rfl | rfl | ⟨h,hh,rfl⟩
    · simp [ga]
    · simp [go]
    · obtain ⟨o,len⟩ := fan h hh
      exact ⟨o,by simpa [ren] using len⟩
  have input (x : Fin 9 → Bool) (k : Fin 9) : (List.ofFn x).getD k.val false = x k := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have inputMore (x : Fin 9 → Bool) (k : Fin 9) (w : List Bool) :
      (List.ofFn x ++ w).getD k.val false = x k := by
    rw [List.getD_append _ _ _ _ (by simp), input]
  have first (x : Fin 9 → Bool) : step (List.ofFn x) ga =
      List.ofFn x ++ [x (σ a) && x (σ b)] := by
    change _ ++ [(List.ofFn x).getD (σ a).val false && ((List.ofFn x).getD (σ b).val false && true)] = _
    rw [input,input,Bool.and_true]
  have second (x : Fin 9 → Bool) (v : Bool) : step (List.ofFn x ++ [v]) go =
      List.ofFn x ++ [v,x (σ 0) || x (σ 2)] := by
    change (_ ++ [v]) ++ [((List.ofFn x) ++ [v]).getD (σ 0).val false ||
      (((List.ofFn x) ++ [v]).getD (σ 2).val false || false)] = _
    rw [inputMore,inputMore,Bool.or_false,List.append_assoc]
    rfl
  have keep (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
      (gs.foldl step w).getD k false = w.getD k false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hk
  have fstGate (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).getD 9 false = (x i && x j) := by
    change ((go :: D.gates.map ren).foldl step (step (List.ofFn x) ga)).getD 9 false = _
    rw [first, keep _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
    rcases pair with ⟨h,k⟩ | ⟨h,k⟩
    · rw [h,k]
    · rw [h,k,Bool.and_comm]
  have oldwire (k N : ℕ) (hk : k < N) (bound : 11 ≤ N) : ρ k < N := by
    by_cases h : k < 9
    · have z := (σ ⟨k,h⟩).isLt
      simp only [ρ,dite_eq_left h]
      omega
    · simp only [ρ,dite_eq_right h]
      split
      · omega
      · split <;> omega
  have fixed (k : ℕ) (h : 11 ≤ k) : ρ k = k := by
    simp [ρ, show ¬k<9 by omega,show k≠9 by omega,show k≠10 by omega]
  have transfer (gs : List Gate) (w z : List Bool) (len : w.length = z.length)
      (bound : 11 ≤ w.length) (eqv : ∀ k, w.getD k false = z.getD (ρ k) false) :
      ∀ k, (gs.foldl step w).getD k false = ((gs.map ren).foldl step z).getD (ρ k) false := by
    induction gs generalizing w z with
    | nil => exact eqv
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      have bits : g.inputs.map (fun k => w.getD k false) =
          (g.inputs.map ρ).map (fun k => z.getD k false) := by
        rw [List.map_map]
        exact List.map_congr_left fun k _ => eqv k
      let v := g.op.eval (g.inputs.map fun k => w.getD k false)
      have val : step z (ren g) = z ++ [v] := by
        change z ++ [g.op.eval ((g.inputs.map ρ).map fun k => z.getD k false)] = _
        rw [← bits]
      rw [val]
      apply ih (w ++ [v]) (z ++ [v]) (by simp [len]) (by simp; omega)
      intro k
      by_cases hk : k < w.length
      · rw [List.getD_append _ _ _ _ hk,List.getD_append _ _ _ _ (len ▸ oldwire k _ hk bound)]
        exact eqv k
      · rw [fixed k (by omega),List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega),len]
  have computes : circuitFun 9 C = edge := by
    funext x
    let y := x ∘ σ
    let v := y a && y b
    let q := y 0 || y 2
    let w := List.ofFn y ++ [q,v]
    let z := List.ofFn x ++ [v,q]
    have aligned (k : ℕ) : w.getD k false = z.getD (ρ k) false := by
      by_cases h : k < 9
      · let t : Fin 9 := ⟨k,h⟩
        change (List.ofFn y ++ [q,v]).getD t.val false = (List.ofFn x ++ [v,q]).getD (ρ k) false
        rw [show ρ k = (σ t).val by simp [ρ,h,t],inputMore,inputMore]
        rfl
      · by_cases h9 : k=9
        · subst k
          change (List.ofFn y ++ [q,v]).getD 9 false = (List.ofFn x ++ [v,q]).getD 10 false
          rw [List.getD_append_right _ _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)]
          rfl
        by_cases h10 : k=10
        · subst k
          change (List.ofFn y ++ [q,v]).getD 10 false = (List.ofFn x ++ [v,q]).getD 9 false
          rw [List.getD_append_right _ _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)]
          rfl
        rw [fixed k (by omega),List.getD_eq_default _ _ (by simp [w]; omega),
          List.getD_eq_default _ _ (by simp [z]; omega)]
    have hsim := transfer D.gates w z (by simp [w,z]) (by simp [w]) aligned D.output
    have evalOriginal : (D.gates.foldl step w).getD D.output false = edge y := by
      have ev := correct y
      change D.eval ((List.ofFn y ++ [q]) ++
        [((List.ofFn y ++ [q]).getD a.val false && (((List.ofFn y ++ [q]).getD b.val false) && true))]) = _ at ev
      rw [inputMore,inputMore,Bool.and_true,List.append_assoc] at ev
      exact ev
    change ((D.gates.map ren).foldl step (step (step (List.ofFn x) ga) go)).getD (ρ D.output) false = _
    rw [first,second]
    exact hsim.symm.trans (evalOriginal.trans (automorphism x))
  have lower : 16 ≤ C.size := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at representative
    rcases representative with h | h | h | h | h | h
    all_goals obtain ⟨rfl,rfl⟩ := h
    · exact high 1 (by decide) C ff fstGate computes
    · exact high 2 (by decide) C ff fstGate computes
    · exact high 3 (by decide) C ff fstGate computes
    · exact h04 C ff fstGate computes
    · exact h06 C ff fstGate computes
    · exact h46 C ff fstGate computes
  omega
