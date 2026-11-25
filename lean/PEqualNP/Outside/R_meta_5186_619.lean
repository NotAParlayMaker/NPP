import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- The two-coordinate projection uses five active lines and their twelve incident points.
-- The monotone evaluation proof follows jturcot42's public R_meta_2712_1 (PR 5230).
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_5186_619
    (embed : ∀ (a b : Nat) (f : Fin a→Fin b) (C : Circuit), Monotone2 C → C.output<a+C.size →
    ∃D : Circuit,Monotone2 D ∧ D.size=C.size ∧ D.output<b+D.size ∧
    ∀ x : Fin b→Bool,circuitFun b D x=circuitFun a C (x ∘ f))
    (coverage : let L : List Nat := [267, 534, 1068, 2136, 177, 98, 452, 648, 1296, 2848, 1601, 3202, 2053]
  let wt (s : Nat) := (List.range 12).countP s.testBit
  let rows := [385, 770, 1184, 1540, 2112, 2240, 2368, 2624, 3136] ++ (List.range 4096).filter (fun s => (wt s==4) && L.all (fun l=>decide (wt (s &&& l)≤2)))
  let neg (j : Fin 171) (i : Fin 17) := let s:=rows.getD j.val 0
    if i.val<5 then (s &&& L.getD i.val 0)==0 else s.testBit (i.val-5)
  let loc (i : Fin 17) := if i.val < 5 then i.val+13 else if i.val < 13 then i.val-5 else i.val-4
  let near (p l : Fin 13) := let v:=(p.val+13-l.val)%13; v=0 ∨ v=1 ∨ v=3 ∨ v=9
  ∀ P L : Finset (Fin 13), (∀p∈P,∀l∈L,¬near p l) →
    (∀ l, (P.filter (fun p=>near p l)).card≤2) → (∀ p, (L.filter (fun l=>near p l)).card≤2) →
    ∃j : Fin 171,∀i,((∃p∈P,loc i=p.val) ∨ ∃l∈L,loc i=13+l.val) → neg j i=true)
    (synthesis : let L : List Nat := [267, 534, 1068, 2136, 177, 98, 452, 648, 1296, 2848, 1601, 3202, 2053]
  let wt (s : Nat) := (List.range 12).countP s.testBit
  let rows := [385, 770, 1184, 1540, 2112, 2240, 2368, 2624, 3136] ++ (List.range 4096).filter (fun s => (wt s==4) && L.all (fun l=>decide (wt (s &&& l)≤2)))
  let neg (j : Fin 171) (i : Fin 17) := let s:=rows.getD j.val 0
    if i.val<5 then (s &&& L.getD i.val 0)==0 else s.testBit (i.val-5)
  ∃ C : Circuit, Monotone2 C ∧ C.size≤23 ∧ C.output<17+C.size ∧
    (∀ l p : Nat, l<5 → p<12 → (L.getD l 0).testBit p=true →
       circuitFun 17 C (fun i=>decide (i.val=l ∨ i.val=5+p))=true) ∧
    ∀j : Fin 171,circuitFun 17 C (neg j)=false) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (23 : ℕ) ∧ x2.output < (26 : ℕ) + x2.size ∧ (∀ (x3 x4 : Fin (13 : ℕ)), ↑x4 < (5 : ℕ) → x3 - x4 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (13 : ℕ) x3 ∨ x7 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, x5 - x7 ∉ x1) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 - x8 ∈ x1}.card ≤ (2 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x3, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ x9 ∈ x4, x8 = Fin.natAdd (13 : ℕ) x9)) = Bool.false := by
  dsimp only
  let L : List Nat := [267, 534, 1068, 2136, 177, 98, 452, 648, 1296, 2848, 1601, 3202, 2053]
  let wt (s : Nat) := (List.range 12).countP s.testBit
  let rows := [385, 770, 1184, 1540, 2112, 2240, 2368, 2624, 3136] ++ (List.range 4096).filter (fun s => (wt s==4) && L.all (fun l=>decide (wt (s &&& l)≤2)))
  let neg (j : Fin 171) (i : Fin 17) := let s:=rows.getD j.val 0
    if i.val<5 then (s &&& L.getD i.val 0)==0 else s.testBit (i.val-5)
  let taps (i : Fin 17) := Fin.ofNat 26 (if i.val < 5 then i.val+13 else if i.val < 13 then i.val-5 else i.val-4)
  let loc (i : Fin 17) := if i.val < 5 then i.val+13 else if i.val < 13 then i.val-5 else i.val-4
  have tapEq : ∀i,(taps i).val=loc i := by decide +kernel
  let D0 : Finset (Fin 13) := {0,1,3,9}
  let near (p l : Fin 13) := let v:=(p.val+13-l.val)%13; v=0 ∨ v=1 ∨ v=3 ∨ v=9
  have equiv : ∀ p l : Fin 13,p-l∈D0 ↔ near p l := by decide +kernel
  change ∀ P L : Finset (Fin 13), (∀p∈P,∀l∈L,¬near p l) →
    (∀l,(P.filter (fun p=>near p l)).card≤2) → (∀p,(L.filter (fun l=>near p l)).card≤2) →
    ∃j : Fin 171,∀i,((∃p∈P,loc i=p.val) ∨ ∃l∈L,loc i=13+l.val) → neg j i=true at coverage
  change ∃ C : Circuit, Monotone2 C ∧ C.size≤23 ∧ C.output<17+C.size ∧
    (∀ l p : Nat, l<5 → p<12 → (L.getD l 0).testBit p=true →
       circuitFun 17 C (fun i=>decide (i.val=l ∨ i.val=5+p))=true) ∧
    ∀j : Fin 171,circuitFun 17 C (neg j)=false at synthesis
  obtain ⟨C,hm,sz,out,accepted,rejected⟩:=synthesis
  obtain ⟨D,good,budget,valid,compute⟩:=embed 17 26 taps C hm out
  have trueRows : ∀p l : Fin 13,l.val<5 → p-l∈D0 → ∃ k : Fin 12,∃q : Fin 5,
      (L.getD q.val 0).testBit k.val=true ∧ ∀i : Fin 17,
      decide (taps i=Fin.castAdd 13 p ∨ taps i=Fin.natAdd 13 l)=decide (i.val=q.val ∨ i.val=5+k.val) := by decide +kernel
  have monotoneEval (x y : Fin 17 → Bool) (hxy : ∀ i, x i = true → y i = true) :
      circuitFun 17 C x = true → circuitFun 17 C y = true := by
    let V (w : List Bool) (i : ℕ) := w.getD i false
    let R (w z : List Bool) := w.length = z.length ∧ ∀ i, V w i = true → V z i = true
    have step (g : Gate) (hg : g ∈ C.gates) (w z : List Bool) (hr : R w z) :
        g.op.eval (g.inputs.map (V w)) = true →
        g.op.eval (g.inputs.map (V z)) = true := by
      have hops := (hm g hg).1
      change g.op = .and ∨ g.op = .or at hops
      rcases hops with h | h <;> rw [h]
      · change (g.inputs.map (V w)).all id = true → (g.inputs.map (V z)).all id = true
        simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        exact fun all i hi => hr.2 i (all i hi)
      · change (g.inputs.map (V w)).any id = true → (g.inputs.map (V z)).any id = true
        simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨i,hi,hval⟩
        exact ⟨i,hi,hr.2 i hval⟩
    let evalStep (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map (V w))]
    have run (gs : List Gate) (hsub : ∀ g ∈ gs, g ∈ C.gates) (w z : List Bool) (hr : R w z) :
        R (gs.foldl evalStep w) (gs.foldl evalStep z) := by
      induction gs generalizing w z with
      | nil => exact hr
      | cons g gs ih =>
        apply ih (fun h hh => hsub h (List.mem_cons_of_mem _ hh))
        refine ⟨by simp only [evalStep,List.length_append,List.length_singleton,hr.1], ?_⟩
        intro i
        change (w ++ [_]).getD i false = true → (z ++ [_]).getD i false = true
        by_cases h : i < w.length
        · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (by simpa only [← hr.1] using h)]
          exact hr.2 i
        · rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by rw [← hr.1]; omega),← hr.1]
          cases i-w.length with
          | zero => exact step g (hsub g List.mem_cons_self) w z hr
          | succ k => simp
    have hi : R (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp only [List.length_ofFn], ?_⟩
      intro i
      by_cases h : i < 17
      · change (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true
        have hx : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact h
        have hy : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact h
        rw [List.getD_eq_getElem _ _ hx,List.getD_eq_getElem _ _ hy,
          List.getElem_ofFn,List.getElem_ofFn]
        exact hxy ⟨i,h⟩
      · change (List.ofFn x).getD i false = true → _
        rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
        intro hf; cases hf
    exact (run C.gates (fun _ h => h) _ _ hi).2 C.output

  refine ⟨D,good,budget ▸ sz,valid,?_,?_⟩
  · intro p l lsmall edge
    obtain ⟨k,q,on,e⟩:=trueRows p l lsmall edge
    rw [compute]
    exact (congrArg (circuitFun 17 C) (funext e)).trans (accepted q.val k.val q.isLt k.isLt on)
  · intro P T independent pointCap lineCap
    obtain ⟨j,sub⟩:=coverage P T
      (fun p hp l hl h=>independent p hp l hl ((equiv p l).mpr h))
      (by simpa only [←equiv] using pointCap) (by simpa only [←equiv] using lineCap)
    rw [compute]
    apply Bool.eq_false_iff.mpr
    intro passed
    have smaller (i : Fin 17) (on : decide ((∃p∈P,taps i=Fin.castAdd 13 p) ∨ ∃l∈T,taps i=Fin.natAdd 13 l)=true) : neg j i=true := by
      apply sub i
      rw [←tapEq i]
      rcases of_decide_eq_true on with ⟨p,m,e⟩|⟨l,m,e⟩
      · exact Or.inl ⟨p,m,congrArg (fun z : Fin 26=>z.val) e⟩
      · exact Or.inr ⟨l,m,congrArg (fun z : Fin 26=>z.val) e⟩
    have h:=monotoneEval _ (neg j) smaller passed
    exact Bool.noConfusion (h.symm.trans (rejected j))
