import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Minimize the AND count at the optimum size. A pivotal edge must survive outside
-- any two clean ancestors' truth sets, since otherwise their OR can replace the gate.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5357_1
    (dirtyOnly : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let missing (D : Circuit) (i : ℕ) := i < D.size ∧ (gateAt D i).op = .and ∧
        ¬∃ u v, G.Adj u v ∧ Owns n D i u v
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      (∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T →
        max (C.size+1) ({u : Fin n | ∃ v, G.Adj u v} : Set (Fin n)).ncard < G.edgeSet.ncard + T.card) →
      ∀ j, missing C j →
      ∀ u v, G.Adj u v → circuitFun n (Circuit.mk (C.gates.set j ⟨.or,[]⟩) C.output) (pairInput u v) = false →
      (∃ i ∈ junk G C, InCone n C i j ∧ s(u,v) ∈ gammaE G C i) →
      (∀ i < j, i ∈ tops G C → InCone n C i j → s(u,v) ∉ gammaE G C i) → ∃ E : Circuit, IsMinimalMonoCircuit n E ∧ circuitFun n E = circuitFun n C ∧
        ∀ a, ¬missing E a)
    (cleanCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let missing (D : Circuit) (i : ℕ) := i < D.size ∧ (gateAt D i).op = .and ∧
        ¬∃ u v, G.Adj u v ∧ Owns n D i u v
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      (∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T →
        max (C.size+1) ({u : Fin n | ∃ v, G.Adj u v} : Set (Fin n)).ncard < G.edgeSet.ncard + T.card) →
      ∀ j, missing C j →
      let clean (i : ℕ) := i < j ∧ i ∈ tops G C ∧ InCone n C i j
      (∃ i, clean i) → (∀ i k, clean i → clean k → ∃ u v, G.Adj u v ∧
        circuitFun n (Circuit.mk (C.gates.set j ⟨.or,[]⟩) C.output) (pairInput u v) = false ∧
        s(u,v) ∉ gammaE G C i ∧ s(u,v) ∉ gammaE G C k ∧ ∃ t, clean t ∧ s(u,v) ∈ gammaE G C t) → ∃ E : Circuit, IsMinimalMonoCircuit n E ∧ circuitFun n E = circuitFun n C ∧
        ∀ a, ¬missing E a)
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 → x4.size < x2.edgeSet.ncard + x9.card - (1 : ℕ)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x4.size ∧ ∀ x11 < x10.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x14 : Fin x1) (x15 : Fin x1), x2.Adj x14 x15 ∧ PEqualNP.EdgeOwnership.Owns x1 x10 x11 x14 x15 := by
  classical
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
  have activeVerticesBound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (model : Monotone2 C) (compute : circuitFun n C = graphFun G ∅) :
      (Finset.univ.filter fun u : Fin n => ∃ v : Fin n, G.Adj u v).card ≤ C.size + 1 := by
    classical
    let before (j : ℕ) (x : Fin n → Bool) := (C.gates.take j).foldl step (List.ofFn x)
    have before_len (j : ℕ) (hj : j ≤ C.gates.length) (x : Fin n → Bool) :
        (before j x).length = n+j := by
      simp [before, wire_len, List.length_take, Nat.min_eq_left hj]
    have earlier (j : ℕ) (hj : j ≤ C.gates.length) (x : Fin n → Bool)
        (i : ℕ) (hi : i < n + j) :
        (before j x).getD i false = wireVal n C i x := by
      change (before j x).getD i false = (C.gates.foldl step (List.ofFn x)).getD i false
      have split : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
      conv_rhs => rw [split, List.foldl_append]
      exact (old_read _ _ _ (by rw [before_len j hj]; exact hi)).symm
    have raw (x : Fin n → Bool) (i : Fin n) : wireVal n C i x = x i := by
      change (C.gates.foldl step (List.ofFn x)).getD i.val false = x i
      rw [old_read _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, i.isLt]
    have evalCongr (j : ℕ) (hj : j < C.gates.length) (x y : Fin n → Bool)
        (known : ∀ i ∈ (gateAt C j).inputs, i < n+j → wireVal n C i x = wireVal n C i y) :
        wireVal n C (n+j) x = wireVal n C (n+j) y := by
      change gateVal n C j x = gateVal n C j y
      rw [gate_from_earlier C j hj x, gate_from_earlier C j hj y]
      apply congrArg (gateAt C j).op.eval
      apply List.map_congr_left
      intro i hi
      change (before j x).getD i false = (before j y).getD i false
      by_cases lo : i < n+j
      · rw [earlier j hj.le x i lo, earlier j hj.le y i lo]
        exact known i hi lo
      · rw [List.getD_eq_default _ _ (by rw [before_len j hj.le]; omega),
          List.getD_eq_default _ _ (by rw [before_len j hj.le]; omega)]
    have deps : ∀ (j : ℕ), j ≤ C.gates.length → ∀ (W : Finset ℕ),
        (∀ i ∈ W, i < n+j) →
        ∃ R : Finset ℕ, R.card ≤ W.card + j ∧
          ∀ x y : Fin n → Bool, (∀ a : Fin n, a.val ∈ R → x a = y a) →
            ∀ i ∈ W, wireVal n C i x = wireVal n C i y := by
      intro j
      induction j with
      | zero =>
        intro _ W hw
        refine ⟨W, by omega, ?_⟩
        intro x y agree i hi
        let a : Fin n := ⟨i, by have h := hw i hi; omega⟩
        change wireVal n C a x = wireVal n C a y
        rw [raw, raw]
        exact agree a hi
      | succ j ih =>
        intro hj W hw
        have jl : j < C.gates.length := by omega
        by_cases hwnew : n+j ∈ W
        · let pins := ((gateAt C j).inputs.filter fun i => decide (i < n+j)).toFinset
          let T := W.erase (n+j) ∪ pins
          have pinCount : pins.card ≤ 2 := by
            have gateMem : gateAt C j ∈ C.gates := by
              change C.gates.getD j ⟨.or,[]⟩ ∈ C.gates
              rw [List.getD_eq_getElem _ _ jl]
              exact List.getElem_mem _
            exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans (model _ gateMem).2)
          have tSmall : T.card ≤ W.card + 1 := by
            have union := Finset.card_union_le (W.erase (n+j)) pins
            have reduced := Finset.card_erase_add_one hwnew
            change (W.erase (n+j) ∪ pins).card ≤ W.card + 1
            omega
          have tLt : ∀ i ∈ T, i < n+j := by
            intro i hi
            rcases Finset.mem_union.mp hi with old | pin
            · have ne := (Finset.mem_erase.mp old).1
              have hW := (Finset.mem_erase.mp old).2
              have lim := hw i hW
              omega
            · have hp := (List.mem_filter.mp (List.mem_toFinset.mp pin)).2
              exact of_decide_eq_true hp
          obtain ⟨R, hR, agrees⟩ := ih jl.le T tLt
          refine ⟨R, by omega, ?_⟩
          intro x y hxy i hi
          by_cases eq : i = n+j
          · subst i
            apply evalCongr j jl x y
            intro k hk back
            exact agrees x y hxy k (Finset.mem_union.mpr (Or.inr
              (List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hk, decide_eq_true back⟩))))
          · exact agrees x y hxy i (Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨eq, hi⟩)))
        · have beforeW : ∀ i ∈ W, i < n+j := by
            intro i hi
            have ne : i ≠ n+j := fun e => hwnew (e ▸ hi)
            have lim := hw i hi
            omega
          obtain ⟨R, hR, agree⟩ := ih jl.le W beforeW
          exact ⟨R, by omega, agree⟩
    let active := Finset.univ.filter fun u : Fin n => ∃ v : Fin n, G.Adj u v
    have pairTest (u v : Fin n) :
        graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
      change (decide (∃ i ∈ (∅ : Finset (Fin n)), pairInput u v i = true) ||
        decide (∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true)) = true ↔ _
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        have a' : a = u ∨ a = v := of_decide_eq_true ha
        have b' : b = u ∨ b = v := of_decide_eq_true hb
        rcases a' with rfl | rfl <;> rcases b' with rfl | rfl
        · exact (hab.ne rfl).elim
        · exact hab
        · exact hab.symm
        · exact (hab.ne rfl).elim
      · intro huv
        exact ⟨u, v, huv, by change decide (u = u ∨ u = v) = true; simp,
          by change decide (v = u ∨ v = v) = true; simp⟩
    change active.card ≤ C.size+1
    by_cases out : C.output < n + C.gates.length
    · obtain ⟨R, hR, aud⟩ := deps C.gates.length le_rfl {C.output}
        (by intro i hi; rw [Finset.mem_singleton.mp hi]; exact out)
      let emb : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
      have sub : active.map emb ⊆ R := by
        intro i hi
        obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hi
        obtain ⟨_, v, adj⟩ := Finset.mem_filter.mp hu
        by_contra lacks
        have agree : ∀ a : Fin n, a.val ∈ R → pairInput u v a = pairInput v v a := by
          intro a ha
          have ne : a ≠ u := fun e => lacks (e ▸ ha)
          change decide (a = u ∨ a = v) = decide (a = v ∨ a = v)
          simp [ne]
        have clash : circuitFun n C (pairInput u v) = circuitFun n C (pairInput v v) :=
          aud (pairInput u v) (pairInput v v) agree C.output (Finset.mem_singleton_self _)
        rw [compute, (pairTest u v).mpr adj] at clash
        exact (G.loopless.irrefl v) ((pairTest v v).mp clash.symm)
      have nActive := Finset.card_le_card sub
      rw [Finset.card_map] at nActive
      change active.card ≤ C.gates.length + 1
      simpa [Nat.add_comm] using nActive.trans hR
    · have empty : active = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨_, v, adj⟩ := Finset.mem_filter.mp hu
        have on : circuitFun n C (pairInput u v) = true := by
          rw [compute]
          exact (pairTest u v).mpr adj
        change (C.gates.foldl step (List.ofFn (pairInput u v))).getD C.output false = true at on
        rw [List.getD_eq_default _ _ (by rw [wire_len]; simp; omega)] at on
        contradiction
      simp [empty]

  let patch (D : Circuit) (j : ℕ) (pins : List ℕ) : Circuit :=
    ⟨D.gates.set j ⟨.or,pins⟩, D.output⟩
  let prefixVals {n : ℕ} (D : Circuit) (j : ℕ) (x : Fin n → Bool) :=
    (D.gates.take j).foldl step (List.ofFn x)
  let finish {n : ℕ} (D : Circuit) (j : ℕ) (x : Fin n → Bool) (b : Bool) :=
    ((D.gates.drop (j+1)).foldl step (prefixVals D j x ++ [b])).getD D.output false
  have patchMono (D : Circuit) (m : Monotone2 D) (j : ℕ) (pins : List ℕ)
      (arity : pins.length ≤ 2) : Monotone2 (patch D j pins) := by
    intro g hg
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
    change (D.gates.set j _)[i]? = some g at hi
    by_cases h : j = i
    · subst i
      by_cases b : j < D.gates.length
      · rw [List.getElem?_set_self b] at hi
        cases hi
        exact ⟨Or.inr rfl,arity⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at hi
        contradiction
    · rw [List.getElem?_set_ne h] at hi
      exact m _ (List.mem_iff_getElem?.mpr ⟨i,hi⟩)
  have replay {n : ℕ} (D : Circuit) (j : ℕ) (hj : j < D.size) (x : Fin n → Bool)
      (pins : List ℕ) :
      circuitFun n D x = finish D j x (gateVal n D j x) ∧
      circuitFun n (patch D j pins) x = finish D j x
        ((pins.map fun w => (prefixVals D j x).getD w false).any id) := by
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
    · change ((D.gates.set j ⟨.or,pins⟩).foldl step (List.ofFn x)).getD D.output false = _
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
  let ands (D : Circuit) := (Finset.range D.size).filter fun j => (gateAt D j).op = .and
  have dropAnd (D : Circuit) (j : ℕ) (hj : j < D.size) (op : (gateAt D j).op = .and)
      (pins : List ℕ) : (ands (patch D j pins)).card < (ands D).card := by
    let E := patch D j pins
    have sizeE : E.size = D.size := List.length_set
    have changed : (gateAt E j).op = .or := by
      change ((D.gates.set j _).getD j ⟨.or, []⟩).op = .or
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hj]
      rfl
    have removed : j ∉ ands E := by
      intro h
      have h' := (Finset.mem_filter.mp h).2
      rw [changed] at h'
      contradiction
    have narrower : ands E ⊆ ands D := by
      intro i hi
      obtain ⟨ilt,iand⟩ := Finset.mem_filter.mp hi
      have diff : j ≠ i := fun h => removed (h ▸ hi)
      have eqg : gateAt E i = gateAt D i := by
        change (D.gates.set j _).getD i ⟨.or,[]⟩ = D.gates.getD i ⟨.or,[]⟩
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne diff]
      exact Finset.mem_filter.mpr ⟨sizeE ▸ ilt,(congrArg Gate.op eqg).symm.trans iand⟩
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset narrower).mpr
      ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,op⟩,removed⟩)
  have lostPair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
      (m : Monotone2 D) (notExact : circuitFun n D ≠ graphFun G ∅)
      (cap : ∀ x, circuitFun n D x = true → graphFun G ∅ x = true) :
      ∃ u v, G.Adj u v ∧ circuitFun n D (pairInput u v) = false := by
    by_contra! none
    apply notExact
    exact edgeComplete G D m cap (fun u v edge => Bool.eq_true_of_not_eq_false (none u v edge))
  intro n G inst C tri four mC fC budget
  let candidates (k : ℕ) := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
    D.size ≤ C.size ∧ (ands D).card = k
  have existsCount : ∃ k, candidates k := ⟨_,C,mC.1,fC,le_rfl,rfl⟩
  obtain ⟨D,mD,fD,sz,countEq⟩ := Nat.find_spec existsCount
  have best : IsMinimalMonoCircuit n D := ⟨mD,fun E hm eq => sz.trans
    (mC.2 E hm (eq.trans (fD.trans fC.symm)))⟩
  have cost (T : Finset (Fin n)) (hT : CoverPromise.IsVertexCover G T) :
      max (D.size+1) ({u : Fin n | ∃ v, G.Adj u v} : Set (Fin n)).ncard <
        G.edgeSet.ncard + T.card := by
    let active := Finset.univ.filter fun u : Fin n => ∃ v, G.Adj u v
    have hact : ({u : Fin n | ∃ v, G.Adj u v} : Set (Fin n)) = (active : Set (Fin n)) := by
      ext u
      simp only [active,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq]
    have ac := activeVerticesBound G D mD fD
    have b := budget T hT
    rw [hact, Set.ncard_coe_finset]
    change active.card ≤ D.size + 1 at ac
    omega
  by_cases owned : ∀ j < D.size, (gateAt D j).op = .and → ∃ u v, G.Adj u v ∧ Owns n D j u v
  · exact ⟨D,mD,fD,sz,owned⟩
  push Not at owned
  obtain ⟨j,hj,op,noOwn⟩ := owned
  have noPatch (pins : List ℕ) (arity : pins.length ≤ 2) :
      circuitFun n (patch D j pins) ≠ graphFun G ∅ := by
    intro patched
    have same : (patch D j pins).size = D.size := List.length_set
    have l := Nat.find_min' existsCount
      ⟨patch D j pins,patchMono D mD j pins arity,patched,same ▸ sz,rfl⟩
    have lt := dropAnd D j hj op pins
    omega
  let cut := patch D j []
  let pivot (u v : Fin n) := G.Adj u v ∧ circuitFun n cut (pairInput u v) = false
  let live (i : ℕ) (u v : Fin n) := gateVal n D i (pairInput u v) = true
  let anc (i : ℕ) := i < j ∧ InCone n D i j ∧ (gateAt D i).op = .and
  let clean (i : ℕ) := anc i ∧ BelowF G D i
  have cutRun (x : Fin n → Bool) : circuitFun n cut x = finish D j x false := (replay D j hj x []).2
  have origRun (x : Fin n → Bool) : circuitFun n D x = finish D j x (gateVal n D j x) := (replay D j hj x []).1
  have cutCap (x : Fin n → Bool) (yes : circuitFun n cut x = true) : graphFun G ∅ x = true := by
    rw [←fD,origRun]
    exact finishUp D mD j x _ ((cutRun x).symm.trans yes)
  obtain ⟨u₀,v₀,first⟩ : ∃ u v, pivot u v := lostPair G cut (patchMono D mD j [] (by decide))
    (noPatch [] (by decide)) cutCap
  have jLive {u v : Fin n} (pv : pivot u v) : live j u v := by
    have old : circuitFun n D (pairInput u v) = true := (congrFun fD _).trans (pairEdge G u v pv.1)
    apply Bool.eq_true_of_not_eq_false
    intro zero
    rw [origRun,zero,←cutRun,pv.2] at old
    contradiction
  have someAncestor {u v : Fin n} (pv : pivot u v) : ∃ i, anc i ∧ live i u v := by
    by_contra h
    apply noOwn u v pv.1
    refine ⟨hj,op,jLive pv,?_⟩
    intro i il cone ai
    exact Bool.eq_false_of_not_eq_true (fun yes => h ⟨i,⟨il,cone,ai⟩,yes⟩)
  have missTwo (i k : ℕ) (ci : clean i) (ck : clean k) :
      ∃ u v, pivot u v ∧ ¬live i u v ∧ ¬live k u v := by
    let E := patch D j [n+i,n+k]
    have erun (x : Fin n → Bool) : circuitFun n E x =
        finish D j x (gateVal n D i x || gateVal n D k x) := by
      rw [(replay D j hj x [n+i,n+k]).2]
      simp only [List.map_cons, List.map_nil, List.any_cons, id_eq, List.any_nil,
        Bool.or_false, prefixGate D j hj i ci.1.1, prefixGate D j hj k ck.1.1]
    have cap (x : Fin n → Bool) (yes : circuitFun n E x = true) : graphFun G ∅ x = true := by
      by_cases a : gateVal n D i x = true
      · exact ci.2 x a
      by_cases b : gateVal n D k x = true
      · exact ck.2 x b
      have h₁ := Bool.eq_false_of_not_eq_true a
      have h₂ := Bool.eq_false_of_not_eq_true b
      rw [erun, h₁, h₂] at yes
      exact cutCap x ((cutRun x).trans yes)
    obtain ⟨u,v,edge,off⟩ := lostPair G E (patchMono D mD j _ (by simp)) (noPatch _ (by simp)) cap
    let p := pairInput u v
    have old : circuitFun n D p = true := (congrFun fD p).trans (pairEdge G u v edge)
    have noJoin : (gateVal n D i p || gateVal n D k p) ≠ true := by
      intro join
      have done : finish D j p true = true := by
        rw [origRun] at old
        cases h : gateVal n D j p with
        | false => rw [h] at old; exact finishUp D mD j p true old
        | true => rwa [h] at old
      have eqn := erun p
      rw [join, done, show circuitFun n E p = false from off] at eqn
      contradiction
    have ni : ¬live i u v := fun h => noJoin (by rw [show gateVal n D i p = true from h]; rfl)
    have nk : ¬live k u v := fun h => noJoin (by rw [show gateVal n D k p = true from h, Bool.or_true])
    have patched := erun p
    rw [Bool.eq_false_of_not_eq_true noJoin, ←cutRun] at patched
    exact ⟨u,v,⟨edge,patched.symm.trans off⟩,ni,nk⟩
  let missing (E : Circuit) (a : ℕ) := a < E.size ∧ (gateAt E a).op = .and ∧
    ¬∃ u v, G.Adj u v ∧ Owns n E a u v
  have bad : missing D j := by
    refine ⟨hj,op,?_⟩
    rintro ⟨u,v,edge,h⟩
    exact noOwn u v edge h
  have out (h : ∃ E : Circuit, IsMinimalMonoCircuit n E ∧ circuitFun n E = circuitFun n D ∧
      ∀ a, ¬missing E a) :
      ∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧ E.size ≤ C.size ∧
        ∀ a < E.size, (gateAt E a).op = .and → ∃ u v, G.Adj u v ∧ Owns n E a u v := by
    obtain ⟨E,m,f,h⟩ := h
    refine ⟨E,m.1,f.trans fD,(m.2 D mD f.symm).trans sz,?_⟩
    intro a al ao
    by_contra no
    exact h a ⟨al,ao,no⟩
  have cleanIff (i : ℕ) : clean i ↔ i < j ∧ i ∈ tops G D ∧ InCone n D i j := by
    let _ : DecidableEq GateOp := gateOpDecEq
    constructor
    · rintro ⟨⟨lt,cone,ai⟩,sound⟩
      exact ⟨lt,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt.trans hj),ai,sound⟩,cone⟩
    · rintro ⟨lt,member,cone⟩
      obtain ⟨_,ai,sound⟩ := Finset.mem_filter.mp member
      exact ⟨⟨lt,cone,ai⟩,sound⟩
  have gammaIff {u v : Fin n} (edge : G.Adj u v) (i : ℕ) :
      s(u,v) ∈ gammaE G D i ↔ live i u v := by
    constructor
    · intro h
      obtain ⟨_,a,b,eq,yes⟩ := Finset.mem_filter.mp h
      rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact yes
      · have swap : pairInput v u = pairInput u v := by
          funext x
          change decide (x = v ∨ x = u) = decide (x = u ∨ x = v)
          by_cases hu : x = u <;> by_cases hv : x = v <;> simp [hu, hv]
        change gateVal n D i (pairInput u v) = true
        rwa [←swap]
    · intro h
      exact Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr edge,u,v,rfl,h⟩
  by_cases all : ∀ u v, pivot u v → ∃ i, clean i ∧ live i u v
  · apply out
    apply cleanCover n G D tri four best fD cost j bad
    · obtain ⟨i,ci,_⟩ := all u₀ v₀ first
      exact ⟨i,(cleanIff i).mp ci⟩
    · intro i k ci ck
      obtain ⟨u,v,p,ni,nk⟩ := missTwo i k ((cleanIff i).mpr ci) ((cleanIff k).mpr ck)
      obtain ⟨t,ct,yes⟩ := all u v p
      exact ⟨u,v,p.1,p.2,fun h => ni ((gammaIff p.1 i).mp h),fun h => nk ((gammaIff p.1 k).mp h),
        t,(cleanIff t).mp ct,(gammaIff p.1 t).mpr yes⟩
  · push Not at all
    obtain ⟨u,v,p,noClean⟩ := all
    apply out
    apply dirtyOnly n G D tri four best fD cost j bad u v p.1 p.2
    · obtain ⟨i,ai,yes⟩ := someAncestor p
      have ns : ¬BelowF G D i := fun sound => noClean i ⟨ai,sound⟩ yes
      have dirty : ∃ x, gateVal n D i x = true ∧ graphFun G ∅ x = false := by
        by_contra no
        apply ns
        intro x hx
        exact Bool.eq_true_of_not_eq_false (fun hf => no ⟨x,hx,hf⟩)
      obtain ⟨x,hx,hf⟩ := dirty
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ai.1.trans hj),ai.2.2,ai.1.trans hj,x,hx,hf⟩,
        ai.2.1,(gammaIff p.1 i).mpr yes⟩
    · intro i il it cone yes
      exact noClean i ((cleanIff i).mpr ⟨il,it,cone⟩) ((gammaIff p.1 i).mp yes)
