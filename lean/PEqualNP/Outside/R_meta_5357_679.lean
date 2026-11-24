import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- The monotone evaluation lemmas and the argument for disjoining two earlier
-- clean wires adapt jturcot42's reduction in PR 10398. The size-preserving
-- raw-edge substitution and the three gate weights give the normalization here.
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_5357_679
    (rawOwn : ∀ (n : ℕ) (C : Circuit) (j : ℕ), j<C.size → ∀ u v : Fin n,
      gateAt C j = ⟨.and,[u.val,v.val]⟩ → Owns n C j u v)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      G.CliqueFree 3 → NoFourCycle G →
      IsMinimalMonoCircuit n D → circuitFun n D = graphFun G ∅ →
      D.size < G.edgeSet.ncard + G.vertexCoverNum.toNat - 1 →
      let missing := fun (E : Circuit) (j : ℕ) => j<E.size ∧ (gateAt E j).op = .and ∧
        ¬∃ u v : Fin n, G.Adj u v ∧ Owns n E j u v
      ∀ j, missing D j →
      let Z := Circuit.mk (D.gates.set j ⟨.or,[]⟩) D.output
      let lost := fun u v : Fin n => G.Adj u v ∧ circuitFun n Z (pairInput u v) = false
      (∃ u v a b, s(u,v) ≠ s(a,b) ∧ lost u v ∧ lost a b) →
      (let early := fun i => i<j ∧ BelowF G D i
       ∀ i k, early i → early k → ∃ u v, lost u v ∧ ∀ q ∈ [i,k], gateVal n D q (pairInput u v) = false) →
      ∃ E : Circuit, IsMinimalMonoCircuit n E ∧ circuitFun n E = circuitFun n D ∧
        ∀ t, ¬missing E t) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 → x4.size < x2.edgeSet.ncard + x9.card - (1 : ℕ)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x4.size ∧ ∀ x11 < x10.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x14 : Fin x1) (x15 : Fin x1), x2.Adj x14 x15 ∧ PEqualNP.EdgeOwnership.Owns x1 x10 x11 x14 x15 := by
  classical
  have stabilize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
        ∀ j < D.size, (gateAt D j = ⟨.or,[]⟩ ∨ ∃ u v : Fin n, G.Adj u v ∧ gateAt D j = ⟨.and,[u.val,v.val]⟩) ∨
          let Z := Circuit.mk (D.gates.set j ⟨.or,[]⟩) D.output
          let lost := fun u v : Fin n => G.Adj u v ∧ circuitFun n Z (pairInput u v) = false
          (∃ u v a b : Fin n, s(u,v) ≠ s(a,b) ∧ lost u v ∧ lost a b) ∧
          ((gateAt D j).op = .and → ∀ i < j, ∀ k < j, BelowF G D i → BelowF G D k →
            ∃ u v : Fin n, lost u v ∧ gateVal n D i (pairInput u v) = false ∧
              gateVal n D k (pairInput u v) = false) := by
    classical
    have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

    have wire_len (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        change (gs.foldl step (step w g)).length = _
        rw [ih]
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega

    have old_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change (gs.foldl step (step w g)).getD i false = _
        rw [ih _ (by simp [step]; omega)]
        apply List.getD_append
        exact hi

    have eval_preserves_true (g : Gate) (basis : g.op = .and ∨ g.op = .or)
        (a b : ℕ → Bool) (pointwise : ∀ i, a i = true → b i = true)
        (yes : g.op.eval (g.inputs.map a) = true) : g.op.eval (g.inputs.map b) = true := by
      rcases basis with hop | hop
      · rw [hop] at yes ⊢
        change (g.inputs.map a).all id = true at yes
        change (g.inputs.map b).all id = true
        apply List.all_eq_true.mpr
        intro t ht
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        exact pointwise i (List.all_eq_true.mp yes _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
      · rw [hop] at yes ⊢
        change (g.inputs.map a).any id = true at yes
        change (g.inputs.map b).any id = true
        obtain ⟨t, ht, htTrue⟩ := List.any_eq_true.mp yes
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        exact List.any_eq_true.mpr ⟨b i, List.mem_map.mpr ⟨i,hi,rfl⟩, pointwise i htTrue⟩

    have run_preserves_true (gs : List Gate)
        (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
        (a b : List Bool) (len : a.length = b.length)
        (h : ∀ i, a.getD i false = true → b.getD i false = true) :
        ∀ i, (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true := by
      induction gs generalizing a b with
      | nil => exact h
      | cons g gs ih =>
        have basis_g := basis g (by simp)
        have basis_tail : ∀ z ∈ gs, z.op = .and ∨ z.op = .or := fun z hz => basis z (by simp [hz])
        change ∀ i, (gs.foldl step (step a g)).getD i false = true →
          (gs.foldl step (step b g)).getD i false = true
        apply ih basis_tail
        · simp [step, len]
        · intro i hi
          by_cases hs : i < a.length
          · have ht : i < b.length := by omega
            change (a ++ [_]).getD i false = true at hi
            rw [List.getD_append _ _ _ _ hs] at hi
            change (b ++ [_]).getD i false = true
            rw [List.getD_append _ _ _ _ ht]
            exact h i hi
          · change (a ++ [_]).getD i false = true at hi
            change (b ++ [_]).getD i false = true
            rw [List.getD_append_right _ _ _ _ (by omega : a.length ≤ i)] at hi
            rw [List.getD_append_right _ _ _ _ (by omega : b.length ≤ i), ←len]
            by_cases eq : i = a.length
            · simp only [eq, Nat.sub_self, List.getD_cons_zero] at hi ⊢
              exact eval_preserves_true g basis_g (fun p => a.getD p false) (fun p => b.getD p false) h hi
            · have positive : 0 < i - a.length := by omega
              rw [List.getD_eq_default _ _ (by simp; omega)] at hi
              contradiction

    have wire_preserves_true {n : ℕ} (C : Circuit) (basis : AndOrOnly C)
        (a b : Fin n → Bool) (pointwise : ∀ j, a j = true → b j = true) (w : ℕ) :
        wireVal n C w a = true → wireVal n C w b = true := by
      apply run_preserves_true C.gates basis (List.ofFn a) (List.ofFn b) (by simp) _ w
      intro i hi
      by_cases h : i < n
      · have aTrue : a ⟨i,h⟩ = true := by simpa [List.getD_eq_getElem?_getD, h] using hi
        simpa [List.getD_eq_getElem?_getD, h] using pointwise ⟨i,h⟩ aTrue
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        contradiction

    have gate_from_earlier {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
        (x : Fin n → Bool) :
        gateVal n C j x = (gateAt C j).op.eval
          ((gateAt C j).inputs.map fun i =>
            ((C.gates.take j).foldl step (List.ofFn x)).getD i false) := by
      let pre := C.gates.take j
      let post := C.gates.drop (j+1)
      let g := C.gates[j]
      have hGate : gateAt C j = g := List.getD_eq_getElem _ _ hj
      have split : C.gates = pre ++ g :: post := by
        dsimp only [pre, g, post]
        rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
      let before := pre.foldl step (List.ofFn x)
      have sizeBefore : before.length = n+j := by
        simp [before, wire_len, pre, List.length_take, Nat.min_eq_left hj.le]
      rw [hGate]
      change (C.gates.foldl step (List.ofFn x)).getD (n+j) false =
        g.op.eval (g.inputs.map fun i => before.getD i false)
      conv_lhs => rw [split, List.foldl_append]
      change (post.foldl step (step before g)).getD (n+j) false = _
      rw [old_read _ _ _ (by simp [step, sizeBefore])]
      change (before ++ [_]).getD (n+j) false = _
      rw [List.getD_append_right _ _ _ _ (by omega : before.length ≤ n+j), sizeBefore,
        Nat.sub_self, List.getD_cons_zero]

    have basisOf (C : Circuit) (m : Monotone2 C) : AndOrOnly C := fun g hg => (m g hg).1

    have edgeTest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → Bool) :
        graphFun G ∅ a = true ↔ ∃ u v, G.Adj u v ∧ a u = true ∧ a v = true := by
      change (decide (∃ i ∈ (∅ : Finset (Fin n)), a i = true) || decide _) = true ↔ _
      simp

    have pairEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n)
        (h : G.Adj a b) : graphFun G ∅ (pairInput a b) = true := by
      apply (edgeTest G _).mpr
      exact ⟨a,b,h,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩

    have edgeComplete {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
        (m : Monotone2 D) (cap : ∀ a, circuitFun n D a = true → graphFun G ∅ a = true)
        (hits : ∀ u v, G.Adj u v → circuitFun n D (pairInput u v) = true) :
        circuitFun n D = graphFun G ∅ := by
      funext a
      apply Bool.eq_iff_iff.mpr
      refine ⟨cap a, ?_⟩
      intro h
      obtain ⟨u,v,edge,hu,hv⟩ := (edgeTest G a).mp h
      apply wire_preserves_true D (basisOf D m) (pairInput u v) a _ D.output (hits u v edge)
      intro i hi
      change decide (i = u ∨ i = v) = true at hi
      rcases (show i = u ∨ i = v from of_decide_eq_true hi) with rfl | rfl
      · exact hu
      · exact hv
    let patch (D : Circuit) (j : ℕ) (g : Gate) : Circuit :=
      ⟨D.gates.set j g, D.output⟩
    let prefixVals {n : ℕ} (D : Circuit) (j : ℕ) (x : Fin n → Bool) :=
      (D.gates.take j).foldl step (List.ofFn x)
    let finish {n : ℕ} (D : Circuit) (j : ℕ) (x : Fin n → Bool) (b : Bool) :=
      ((D.gates.drop (j+1)).foldl step (prefixVals D j x ++ [b])).getD D.output false
    have patchMono (D : Circuit) (m : Monotone2 D) (j : ℕ) (g : Gate)
        (legal : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) : Monotone2 (patch D j g) := by
      intro gate hg
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
      change (D.gates.set j _)[i]? = some gate at hi
      by_cases h : j = i
      · subst i
        by_cases b : j < D.gates.length
        · rw [List.getElem?_set_self b] at hi
          cases hi
          exact legal
        · rw [List.getElem?_eq_none (by simp; omega)] at hi
          contradiction
      · rw [List.getElem?_set_ne h] at hi
        exact m _ (List.mem_iff_getElem?.mpr ⟨i,hi⟩)
    have replay {n : ℕ} (D : Circuit) (j : ℕ) (hj : j < D.size) (x : Fin n → Bool)
        (gNew : Gate) :
        circuitFun n D x = finish D j x (gateVal n D j x) ∧
        circuitFun n (patch D j gNew) x = finish D j x
          (gNew.op.eval (gNew.inputs.map fun w => (prefixVals D j x).getD w false)) := by
      let pre := prefixVals D j x
      let post := D.gates.drop (j+1)
      let g := D.gates[j]'hj
      have hs : D.gates = D.gates.take j ++ g :: post := by
        rw [show g :: post = D.gates.drop j from (List.drop_eq_getElem_cons hj).symm, List.take_append_drop]
      have orig : step pre g = pre ++ [gateVal n D j x] := by
        rw [gate_from_earlier D j hj x, show gateAt D j = g from List.getD_eq_getElem _ _ hj]
      constructor
      · change (D.gates.foldl step (List.ofFn x)).getD D.output false = _
        conv_lhs => rw [hs, List.foldl_append]
        exact congrArg (fun w => (post.foldl step w).getD D.output false) orig
      · change ((D.gates.set j gNew).foldl step (List.ofFn x)).getD D.output false = _
        rw [List.set_eq_take_append_cons_drop, ite_eq_left (show j < D.gates.length from hj), List.foldl_append]
        rfl
    have finishUp {n : ℕ} (D : Circuit) (m : Monotone2 D) (j : ℕ) (x : Fin n → Bool)
        (b : Bool) : finish D j x false = true → finish D j x b = true := by
      apply run_preserves_true _ (fun g h => basisOf D m g (List.mem_of_mem_drop h)) _ _ (by simp)
      intro i hi
      let pre := prefixVals D j x
      change (pre ++ [false]).getD i false = true at hi
      change (pre ++ [b]).getD i false = true
      by_cases lo : i < pre.length
      · rw [List.getD_append _ _ _ _ lo] at hi ⊢
        exact hi
      · rw [List.getD_append_right _ _ _ _ (by omega : pre.length ≤ i)] at hi
        by_cases eq : i = pre.length
        · simp only [eq, Nat.sub_self, List.getD_cons_zero] at hi
          contradiction
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          contradiction
    have prefixGate {n : ℕ} (D : Circuit) (j : ℕ) (hj : j < D.size) (i : ℕ) (hi : i < j)
        (x : Fin n → Bool) : (prefixVals D j x).getD (n+i) false = gateVal n D i x := by
      change _ = (D.gates.foldl step (List.ofFn x)).getD (n+i) false
      conv_rhs => rw [← List.take_append_drop j D.gates, List.foldl_append]
      symm
      apply old_read
      rw [wire_len, List.length_take, List.length_ofFn, Nat.min_eq_left (show j ≤ D.gates.length from hj.le)]
      omega
    have lostPair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
        (m : Monotone2 D) (notExact : circuitFun n D ≠ graphFun G ∅)
        (cap : ∀ x, circuitFun n D x = true → graphFun G ∅ x = true) :
        ∃ u v, G.Adj u v ∧ circuitFun n D (pairInput u v) = false := by
      by_contra! none
      apply notExact
      exact edgeComplete G D m cap (fun u v edge => Bool.eq_true_of_not_eq_false (none u v edge))
    intro n G inst C mC fC
    let cheap (g : Gate) : Prop := g = ⟨.or,[]⟩ ∨ ∃ u v : Fin n, G.Adj u v ∧ g = ⟨.and,[u.val,v.val]⟩
    let weight (g : Gate) : ℕ := if cheap g then 0 else if g.op = .and then 2 else 1
    let cost (D : Circuit) := (D.gates.map weight).sum
    let available (k : ℕ) := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ cost D = k
    have nonempty : ∃ k, available k := ⟨_,C,mC,fC,rfl,rfl⟩
    obtain ⟨D,mD,fD,sizeD,countD⟩ := Nat.find_spec nonempty
    refine ⟨D,mD,fD,sizeD,?_⟩
    intro j hj
    by_cases easy : cheap (gateAt D j)
    · exact Or.inl easy
    right
    let Z := patch D j ⟨.or,[]⟩
    let pivot (u v : Fin n) := G.Adj u v ∧ circuitFun n Z (pairInput u v)=false
    have noLighter (g : Gate) (ch : weight g < weight (gateAt D j)) (hm : Monotone2 (patch D j g)) :
        circuitFun n (patch D j g) ≠ graphFun G ∅ := by
      intro eq
      let E := patch D j g
      have sz : E.size=D.size := List.length_set
      have hs : D.gates.take j ++ gateAt D j :: D.gates.drop (j+1) = D.gates := by
        rw [show gateAt D j = D.gates[j]'hj from List.getD_eq_getElem _ _ hj,← List.drop_eq_getElem_cons hj,List.take_append_drop]
      have less : cost E < cost D := by
        change ((D.gates.set j g).map weight).sum < (D.gates.map weight).sum
        conv_rhs => rw [← hs]
        rw [List.set_eq_take_append_cons_drop,ite_eq_left (show j<D.gates.length from hj)]
        simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons]
        omega
      have low := Nat.find_min' nonempty (show available (cost E) from ⟨E,hm,eq,sz.trans sizeD,rfl⟩)
      omega
    have forbidden (g : Gate) (ch : cheap g) (hm : Monotone2 (patch D j g)) :
        circuitFun n (patch D j g) ≠ graphFun G ∅ := by
      apply noLighter g _ hm
      simp only [weight,ite_eq_left ch,ite_eq_right easy]
      split <;> decide
    have zm : Monotone2 Z := patchMono D mD j ⟨.or,[]⟩ ⟨Or.inr rfl,by decide⟩
    have zrun (x : Fin n → Bool) : circuitFun n Z x = finish D j x false := (replay D j hj x ⟨.or,[]⟩).2
    have drun (x : Fin n → Bool) : circuitFun n D x = finish D j x (gateVal n D j x) :=
      (replay D j hj x ⟨.or,[]⟩).1
    have cap (x : Fin n → Bool) (yes : circuitFun n Z x = true) : graphFun G ∅ x = true := by
      rw [zrun] at yes
      rw [← fD,drun]
      exact finishUp D mD j x _ yes
    constructor
    · change ∃ u v a b, s(u,v)≠s(a,b) ∧ pivot u v ∧ pivot a b
      have existsPivot : ∃ u v, pivot u v := by
        by_contra! none
        apply forbidden ⟨.or,[]⟩ (Or.inl rfl) zm
        apply edgeComplete G Z zm cap
        intro u v adj
        by_contra! no
        exact none u v ⟨adj,Bool.eq_false_of_not_eq_true no⟩
      obtain ⟨u,v,uv⟩ := existsPivot
      by_contra! only
      let g : Gate := ⟨.and,[u.val,v.val]⟩
      let E := patch D j g
      have em : Monotone2 E := patchMono D mD j g ⟨Or.inl rfl,by simp [g]⟩
      have erun (x : Fin n → Bool) : circuitFun n E x = finish D j x (x u && x v) := by
        have raw (a : Fin n) : (prefixVals D j x).getD a.val false = x a := by
          change ((D.gates.take j).foldl step (List.ofFn x)).getD a.val false = _
          rw [old_read _ _ _ (by simpa using a.isLt)]
          simp [List.getD_eq_getElem?_getD]
        have h := (replay D j hj x g).2
        simpa only [g,evalAnd,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id,Bool.and_true,raw] using h
      apply forbidden g (Or.inr ⟨u,v,uv.1,rfl⟩) em
      apply edgeComplete G E em
      · intro x yes
        by_cases bits : x u=true ∧ x v=true
        · exact (edgeTest G x).mpr ⟨u,v,uv.1,bits⟩
        · have no : (x u && x v) = false := Bool.eq_false_of_not_eq_true (fun h => bits (by simpa using h))
          rw [erun,no] at yes
          exact cap x ((zrun x).symm ▸ yes)
      · intro a b ab
        by_cases h : circuitFun n Z (pairInput a b) = false
        · have same : s(u,v) = s(a,b) := by
            by_contra diff
            exact only u v a b diff uv ⟨ab,h⟩
          have hu : pairInput a b u = true := by
            apply decide_eq_true
            simpa only [Sym2.mem_iff] using (same ▸ Sym2.mem_mk_left u v : u ∈ s(a,b))
          have hv : pairInput a b v = true := by
            apply decide_eq_true
            simpa only [Sym2.mem_iff] using (same ▸ Sym2.mem_mk_right u v : v ∈ s(a,b))
          have old := congrFun fD (pairInput a b)
          rw [pairEdge G a b ab,drun] at old
          rw [erun,hu,hv]
          cases val : gateVal n D j (pairInput a b) with
          | false =>
            rw [val] at old
            exact finishUp D mD j _ true old
          | true => rwa [val] at old
        · rw [erun]
          apply finishUp D mD j
          exact (zrun _).symm ▸ Bool.eq_true_of_not_eq_false h
    · intro op i hi k hk ci ck
      let E := patch D j ⟨.or,[n+i,n+k]⟩
      have erun (x : Fin n → Bool) : circuitFun n E x =
          finish D j x (gateVal n D i x || gateVal n D k x) := by
        rw [(replay D j hj x ⟨.or,[n+i,n+k]⟩).2]
        simp only [evalOr,List.map_cons, List.map_nil, List.any_cons, id_eq, List.any_nil,
          Bool.or_false, prefixGate D j hj i hi, prefixGate D j hj k hk]
      have capE (x : Fin n → Bool) (yes : circuitFun n E x = true) : graphFun G ∅ x = true := by
        by_cases a : gateVal n D i x = true
        · exact ci x a
        by_cases b : gateVal n D k x = true
        · exact ck x b
        have h₁ := Bool.eq_false_of_not_eq_true a
        have h₂ := Bool.eq_false_of_not_eq_true b
        rw [erun, h₁, h₂] at yes
        exact cap x ((zrun x).trans yes)
      have em : Monotone2 E := patchMono D mD j _ ⟨Or.inr rfl,by simp⟩
      have lighter : weight ⟨.or,[n+i,n+k]⟩ < weight (gateAt D j) := by
        simp only [weight,ite_eq_right easy,ite_eq_left op]
        split <;> simp
      obtain ⟨u,v,edge,off⟩ := lostPair G E em (noLighter _ lighter em) capE
      let p := pairInput u v
      have old : circuitFun n D p = true := (congrFun fD p).trans (pairEdge G u v edge)
      have noJoin : (gateVal n D i p || gateVal n D k p) ≠ true := by
        intro join
        have done : finish D j p true = true := by
          rw [drun] at old
          cases h : gateVal n D j p with
          | false => rw [h] at old; exact finishUp D mD j p true old
          | true => rwa [h] at old
        have eqn := erun p
        rw [join, done, show circuitFun n E p = false from off] at eqn
        contradiction
      have ni : gateVal n D i (pairInput u v) ≠ true := fun h => noJoin (by rw [show gateVal n D i p = true from h]; rfl)
      have nk : gateVal n D k (pairInput u v) ≠ true := fun h => noJoin (by rw [show gateVal n D k p = true from h, Bool.or_true])
      have patched := erun p
      rw [Bool.eq_false_of_not_eq_true noJoin, ←zrun] at patched
      exact ⟨u,v,⟨edge,patched.symm.trans off⟩,Bool.eq_false_of_not_eq_true ni,Bool.eq_false_of_not_eq_true nk⟩
  intro n G dec C tri four minC funC bound
  obtain ⟨D,mono,funD,sizeD,stable⟩ := stabilize n G C minC.1 funC
  have eq : circuitFun n D = circuitFun n C := funD.trans funC.symm
  have md : IsMinimalMonoCircuit n D := ⟨mono,fun H hm he => sizeD ▸ minC.2 H hm (he.trans eq)⟩
  let owns (E : Circuit) (j : ℕ) := ∃ u v : Fin n, G.Adj u v ∧ Owns n E j u v
  by_cases done : ∀ j<D.size, (gateAt D j).op = .and → owns D j
  · exact ⟨D,mono,funD,sizeD.le,done⟩
  push Not at done
  obtain ⟨j,hj,op,none⟩ := done
  rcases stable j hj with (zero|⟨u,v,uv,literal⟩)|⟨two,miss⟩
  · rw [zero] at op
    contradiction
  · exact (none ⟨u,v,uv,rawOwn n D j hj u v literal⟩).elim
  · have triangle : G.CliqueFree 3 := by
      intro F hF
      obtain ⟨a,b,c,ab,ac,bc,_⟩ := SimpleGraph.is3Clique_iff.mp hF
      exact tri a b c ab bc ac.symm
    obtain ⟨K,coverSize,Kcover⟩ := G.vertexCoverNum_exists
    have finiteSize : K.toFinset.card = G.vertexCoverNum.toNat :=
      (Set.toFinset_card _).trans ((Set.fintypeCard_eq_ncard _).trans (congrArg ENat.toNat coverSize))
    have cover : CoverPromise.IsVertexCover G K.toFinset := fun a b h => by
      simpa only [Set.mem_toFinset] using Kcover h
    have db := bound K.toFinset cover
    rw [finiteSize,←sizeD] at db
    have avoid := miss op
    obtain ⟨E,me,fe,all⟩ := repair n G D triangle four md funD db j ⟨hj,op,none⟩ two (by
      intro early i k hi hk
      obtain ⟨u,v,h,li,lk⟩ := avoid i hi.1 k hk.1 hi.2 hk.2
      refine ⟨u,v,h,?_⟩
      intro q mem
      rcases (show q=i ∨ q=k by simpa using mem) with rfl|rfl
      · exact li
      · exact lk)
    refine ⟨E,me.1,fe.trans funD,(me.2 D mono fe.symm).trans sizeD.le,?_⟩
    intro t ht top
    by_contra absent
    exact all t ⟨ht,top,absent⟩
