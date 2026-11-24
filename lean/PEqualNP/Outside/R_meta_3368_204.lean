import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_3368_204 (prev : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size) (few :
  let F := fun (x : Fin 9→Bool) => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun n => x (Fin.ofNat 9 (n/9)) && x (Fin.ofNat 9 (n % 9)))
  let V := fun (x : Fin 9→Bool) => List.ofFn (Function.update x 4 false)++[x 0 || x 4,x 4 || x 1]
  let cost := fun (g : Gate) => @GateOp.rec (fun _ => Bool) true true false (fun _ => true) true g.op
  ∀ C : Circuit, FanInTwo C → C.gates.countP cost≤12 → (∀ x,C.eval (V x)=F x) → False) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x1 x5) → False := by
  let loc (N i : Nat) := if i=4 then N else i
  let remap (N : Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (loc N)⟩
  let step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map (fun i => w.getD i false))]
  let build (C : Circuit) : Circuit :=
    ⟨⟨.or,[4,1]⟩::C.gates.map (remap (11+C.size)),loc (11+C.size) C.output⟩
  have mono (C : Circuit) (h : Monotone2 C) : Monotone2 (build C) := by
    intro g hg
    change g∈(⟨.or,[4,1]⟩ : Gate)::C.gates.map _ at hg
    rcases List.mem_cons.mp hg with rfl|ht
    · exact ⟨Or.inr rfl, by decide⟩
    · obtain ⟨v,hm,rfl⟩ := List.mem_map.mp ht
      exact ⟨(h v hm).1,by simpa [remap] using (h v hm).2⟩
  have read_eq (x : Fin 9→Bool) (t : List Bool) (N i : Nat) (h : 9+t.length≤N) :
      (List.ofFn x++t).getD (loc N i) false=(List.ofFn (Function.update x 4 false)++t).getD i false := by
    by_cases he : i=4
    · subst i
      simp only [loc,ite_true]
      rw [List.getD_eq_default _ _ (by simp;omega),List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
      simp
    · simp only [loc,he,ite_false]
      by_cases hi : i<9
      · rw [List.getD_append _ _ _ _ (by simpa using hi),List.getD_append _ _ _ _ (by simpa using hi)]
        rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn,List.getElem_ofFn]
        exact (Function.update_of_ne (by intro q;exact he (congrArg Fin.val q)) _ _).symm
      · rw [List.getD_append_right _ _ _ _ (by simp;omega),List.getD_append_right _ _ _ _ (by simp;omega)]
        simp
  have simulate (x : Fin 9→Bool) (gs : List Gate) (t : List Bool) (N : Nat)
      (h : 9+t.length+gs.length≤N) :
      ∃ u : List Bool, 9+u.length≤N ∧
        (gs.map (remap N)).foldl step (List.ofFn x++t)=List.ofFn x++u ∧
        gs.foldl step (List.ofFn (Function.update x 4 false)++t)=List.ofFn (Function.update x 4 false)++u := by
    induction gs generalizing t with
    | nil => exact ⟨t,by simpa using h,rfl,rfl⟩
    | cons g gs ih =>
      let z := g.op.eval (g.inputs.map fun i => (List.ofFn (Function.update x 4 false)++t).getD i false)
      obtain ⟨u,hu,hw,hv⟩ := ih (t++[z]) (by simp at h ⊢;omega)
      have e : (remap N g).op.eval ((remap N g).inputs.map fun i => (List.ofFn x++t).getD i false)=z := by
        apply congrArg g.op.eval
        simp only [remap,List.map_map]
        apply List.map_congr_left
        intro i _
        exact read_eq _ _ _ _ (by omega)
      exact ⟨u,hu,by simpa only [List.map_cons,List.foldl_cons,step,e,List.append_assoc] using hw,
        by simpa only [List.foldl_cons,step,List.append_assoc] using hv⟩
  have compute (C : Circuit) (x : Fin 9→Bool) :
      (build C).eval (List.ofFn x++[x 0 || x 4])=
        C.eval (List.ofFn (Function.update x 4 false)++[x 0 || x 4,x 4 || x 1]) := by
    let a := x 0 || x 4
    let b := x 4 || x 1
    let t := [a,b]
    let N := 11+C.size
    obtain ⟨u,hu,hw,hv⟩ := simulate x C.gates t N (by change 11+C.gates.length≤11+C.gates.length; exact Nat.le_refl _)
    have pre : step (List.ofFn x++[a]) ⟨.or,[4,1]⟩ = List.ofFn x++t := by
      change (List.ofFn x++[a])++[((List.ofFn x++[a]).getD 4 false || ((List.ofFn x++[a]).getD 1 false || false))]=_
      rw [List.getD_append _ _ _ _ (by simp),List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn,List.getElem_ofFn]
      simp [t,b]
    change ((C.gates.map (remap N)).foldl step (step (List.ofFn x++[a]) ⟨.or,[4,1]⟩)).getD (loc N C.output) false =
      (C.gates.foldl step (List.ofFn (Function.update x 4 false)++t)).getD C.output false
    rw [pre,hw,hv]
    exact read_eq _ _ _ _ hu
  dsimp only
  intro C fan hc fit
  by_cases hm : Monotone2 C
  · let D := build C
    have small : D.size=C.size+1 := by change (_::C.gates.map _).length=C.gates.length+1; simp
    have bound := prev D (mono C hm) (by
      intro r hr
      let x : Fin 9→Bool := fun i => r.testBit i.val
      change (build C).eval (List.ofFn x++[x 0 || x 4]) = _
      rw [compute C x]
      change C.eval (List.ofFn (Function.update x 4 false)++[x 0 || x 4,x 4 || x 1])=_
      rw [fit]
      let E : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
      have truth : ∀ r∈([3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402] : List ℕ), E.any (fun e => r.testBit e.1.val && r.testBit e.2.val)=decide (r∈([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]: List ℕ)) := by decide +kernel
      exact truth r hr)
    omega
  · let cost := fun (g : Gate) => @GateOp.rec (fun _ => Bool) true true false (fun _ => true) true g.op
    have miss : ∃ g∈C.gates, g.op=.not := by
      by_contra! h
      apply hm
      intro g hg
      obtain ⟨ho,hl⟩ := fan g hg
      change g.op=.and ∨ g.op=.or ∨ g.op=.not at ho
      exact ⟨ho.elim Or.inl (fun hh => Or.inr (hh.resolve_right (h g hg))),hl⟩
    obtain ⟨g,hg,hn⟩ := miss
    have no : cost g=false := by simp only [cost,hn]
    have li := List.countP_le_length (p:=cost) (l:=C.gates)
    have neq : C.gates.countP cost ≠ C.gates.length := by
      intro eq
      have yes := List.countP_eq_length.mp eq g hg
      exact Bool.noConfusion (no.symm.trans yes)
    change C.gates.length≤13 at hc
    apply few C fan (by change C.gates.countP cost≤12;omega)
    intro x
    exact fit x
