import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first two premises are the cover construction and the four-reader elimination theorem.
-- Below the cover budget, count the input slots of a minimum circuit on the cubic part.
-- Unless a vertex has only one reader, the endpoints of some edge and all their neighbors have two readers each.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4051_24
    (stars : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
      (∃ i j : Fin n, G.Adj i j) →
      (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
      HasCircuitSize n (fun x : Fin n → Bool => decide
        (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
        (G.edgeFinset.card + T.card - 1))
    (readCut : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (v : Fin n),
      FanInTwo C → circuitFun n C = f → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∃ x y, f (Function.update x v false) ≠ f (Function.update y v false)) →
      let rs := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (4 ≤ rs.length ∨ rs.length = 3 ∧ ∃ g ∈ rs, g.op ≠ .or) →
      ∃ t, t + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t)
    (rareCase : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let rs := fun (v : Fin n) => C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      IsMinimalCircuit n C →
      (∀ x, circuitFun n C x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      (∀ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) →
        C.size + 1 < G.edgeFinset.card + T.card) →
      (∀ v, (rs v).length ≤ 3 ∧ ((rs v).length = 3 → ∀ g ∈ rs v, g.op = .or)) →
      (∃ v, (rs v).length = 1) →
      ∃ v : Fin n, ∃ t : ℕ, t + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) t)
    (edgeCase : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let rs := fun (v : Fin n) => C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      IsMinimalCircuit n C →
      (∀ x, circuitFun n C x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      (∀ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) →
        C.size + 1 < G.edgeFinset.card + T.card) →
      (∀ v, (rs v).length ≤ 3 ∧ ((rs v).length = 3 → ∀ g ∈ rs v, g.op = .or)) →
      ((∀ w, 2 ≤ (rs w).length) ∧
        (∀ S : Finset (Fin n), (∀ w ∈ S, 3 ≤ (rs w).length) → 6 * S.card < n) ∧
        ∃ u v, G.Adj u v ∧ ∀ w, w = u ∨ w = v ∨ G.Adj u w ∨ G.Adj v w → (rs w).length = 2) →
      ∃ v : Fin n, ∃ t : ℕ, t + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) t)
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 : Fin x1 → Bool), x3 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x8 → ∃ (x10 : Fin x1), (x2.neighborSet x10).ncard = (3 : ℕ) ∧ ∃ (x11 : ℕ), x11 + (4 : ℕ) ≤ x8 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update x12 x10 Bool.false)) x11 := by
  classical
  -- Restrict to the nonisolated vertices, then lift the resulting circuit back.
  have stripIsolates (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool),
      (∀ v, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∃ a b, G.Adj a b) →
      (∀ x, f x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      ∀ s, HasCircuitSize n f s → ∃ v : Fin n, ∃ t : ℕ, t + 4 ≤ s ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) t) :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 : Fin x1 → Bool), x3 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x8 → ∃ (x10 : Fin x1), (x2.neighborSet x10).ncard = (3 : ℕ) ∧ ∃ (x11 : ℕ), x11 + (4 : ℕ) ≤ x8 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update x12 x10 Bool.false)) x11 := by
    have relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
        (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
      have getD_snoc_eq (L : List Bool) (S d : Bool) : (L ++ [S]).getD L.length d = S := by simp
      let wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
        if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

      let relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
        ⟨g.op, g.inputs.map (wmap n m π)⟩

      let relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
        ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

      let step (w : List Bool) (g : Gate) : List Bool :=
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

      let Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
        n ≤ W.length ∧ W'.length + n = W.length + m ∧
          ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

      have rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
          (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
        obtain ⟨h1, h2, h3⟩ := h
        have hv : (relGate n m π g).op.eval
            ((relGate n m π g).inputs.map fun i => W'.getD i false)
            = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          simp only [relGate, List.map_map]
          congr 1
          apply List.map_congr_left
          intro a _
          exact h3 a
        refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
        intro w
        simp only [step, hv]
        rcases Nat.lt_trichotomy w W.length with hw | hw | hw
        · have hlt : wmap n m π w < W'.length := by
            unfold wmap
            split
            · have := (π ⟨w, by assumption⟩).2; omega
            · omega
          rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
          exact h3 w
        · have he : wmap n m π w = W'.length := by
            unfold wmap
            split
            · omega
            · omega
          rw [he, hw, getD_snoc_eq, getD_snoc_eq]
        · have hge : W'.length + 1 ≤ wmap n m π w := by
            unfold wmap
            split
            · omega
            · omega
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

      have rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
          ∀ W W' : List Bool, Rel n m π W W' →
            Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
        induction gs with
        | nil => intro W W' h; exact h
        | cons g gs ih =>
          intro W W' h
          exact ih _ _ (rel_step n m π W W' g h)

      have rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
          Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
        refine ⟨by simp, by simp; omega, ?_⟩
        intro w
        unfold wmap
        split
        · rename_i hw
          rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
          simp
        · rename_i hw
          rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

      obtain ⟨C, ok, hsz, hev⟩ := hc
      refine ⟨relabel n m π C, ?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
      · change (C.gates.map (relGate n m π)).length ≤ s
        simpa only [List.length_map] using (show C.gates.length ≤ s from hsz)
      · intro x
        show _ = h (x ∘ π)
        rw [← hev (x ∘ π)]
        have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
        exact this

    have liftCut {n m : ℕ} (e : Fin m ↪ Fin n) (r : Fin n → Fin m)
        (ret : ∀ v, r (e v) = v) (f : (Fin n → Bool) → Bool)
        (agree : ∀ x y : Fin n → Bool, (∀ v, x (e v) = y (e v)) → f x = f y)
        (v : Fin m) (k : ℕ)
        (hc : HasCircuitSize m (fun y => f ((Function.update y v false) ∘ r)) k) :
        HasCircuitSize n (fun x => f (Function.update x (e v) false)) k := by
      have eq : (fun x : Fin n → Bool => f ((Function.update (x ∘ e) v false) ∘ r))
          = (fun x => f (Function.update x (e v) false)) := by
        funext x
        apply agree
        intro w
        by_cases h : w = v
        · subst w
          simp [ret]
        · simp [ret,Function.update_of_ne h,Function.update_of_ne (e.injective.ne h)]
      rw [← eq]
      exact relabel_size e _ k hc
    intro n G f degrees girth edge computes s circuit
    obtain ⟨a,b,ab⟩ := edge
    let live (u : Fin n) := ∃ w, G.Adj u w
    let A := {u : Fin n // live u}
    let m := Fintype.card A
    let code : A ≃ Fin m := Fintype.equivFin A
    let e : Fin m ↪ Fin n := code.symm.toEmbedding.trans (Function.Embedding.subtype live)
    let r (u : Fin n) : Fin m := if h : live u then code ⟨u,h⟩ else code ⟨a,⟨b,ab⟩⟩
    have er (u : Fin n) (h : live u) : e (r u) = u := by
      change (code.symm (r u)).val = u
      simp [r,h]
    have on (v : Fin m) : live (e v) := (code.symm v).property
    have ret (v : Fin m) : r (e v) = v := e.injective (er (e v) (on v))
    let K := G.comap e
    have edges (u v : Fin m) : K.Adj u v ↔ G.Adj (e u) (e v) := Iff.rfl
    have oldEdge (u v : Fin n) (h : G.Adj u v) : K.Adj (r u) (r v) := by
      rw [edges,er u ⟨v,h⟩,er v ⟨u,h.symm⟩]
      exact h
    have degree (v : Fin m) : (G.neighborSet (e v)).ncard = 3 := by
      obtain ⟨w,hw⟩ := on v
      exact (degrees (e v)).resolve_left (Set.ncard_ne_zero_of_mem hw)
    have regular (v : Fin m) : (K.neighborSet v).ncard = 3 := by
      rw [← degree v,show K.neighborSet v = e ⁻¹' G.neighborSet (e v) from G.neighborSet_comap e v]
      apply Set.ncard_preimage_of_injective_subset_range e.injective
      intro w hw
      exact ⟨r w,er w ⟨e v,G.adj_symm hw⟩⟩
    have cycles (v : Fin m) (w : K.Walk v v) (h : w.IsCycle) : 7 ≤ w.length := by
      let emb := SimpleGraph.Embedding.comap e G
      simpa only [SimpleGraph.Walk.length_map] using
        girth (emb v) (w.map emb.toHom) (h.map emb.injective)
    have agrees (x y : Fin n → Bool) (h : ∀ v, x (e v) = y (e v)) : f x = f y := by
      apply Bool.eq_iff_iff.mpr
      rw [computes x,computes y]
      have same (u : Fin n) (hu : live u) : x u = y u := by
        simpa only [er u hu] using h (r u)
      constructor <;> rintro ⟨u,v,uv,hu,hv⟩
      · exact ⟨u,v,uv,(same u ⟨v,uv⟩).symm.trans hu,(same v ⟨u,uv.symm⟩).symm.trans hv⟩
      · exact ⟨u,v,uv,(same u ⟨v,uv⟩).trans hu,(same v ⟨u,uv.symm⟩).trans hv⟩
    let g (y : Fin m → Bool) := f (y ∘ r)
    have reduced (x : Fin m → Bool) :
        g x = true ↔ ∃ u v, K.Adj u v ∧ x u = true ∧ x v = true := by
      rw [show g x = f (x ∘ r) from rfl,computes]
      constructor
      · rintro ⟨u,v,uv,hu,hv⟩
        exact ⟨r u,r v,oldEdge _ _ uv,hu,hv⟩
      · rintro ⟨u,v,uv,hu,hv⟩
        refine ⟨e u,e v,(edges _ _).mp uv,?_,?_⟩
        · simpa only [Function.comp_apply,ret] using hu
        · simpa only [Function.comp_apply,ret] using hv
    obtain ⟨v,k,le,small⟩ := core m K g regular cycles ⟨r a,r b,oldEdge _ _ ab⟩ reduced s
        (relabel_size r f s circuit)
    exact ⟨e v,degree v,k,le,liftCut e r ret f agrees v k small⟩
  -- Bound the cover size by taking the complement of a large independent set.
  have largeIndependent (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (degree : ∀ v, (G.neighborSet v).ncard = 3)
      (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) :
      ∃ I : Finset (Fin n), (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) ∧ n ≤ 3 * I.card := by
    have triangleFree {v a b : Fin n} (ha : G.Adj v a) (hb : G.Adj v b) : ¬G.Adj a b := by
      intro hab
      let walk : G.Walk v v := .cons ha (.cons hab (.cons hb.symm .nil))
      have cycle : walk.IsCycle := by
        apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        simp [walk,SimpleGraph.Walk.isPath_def,hab.ne,Ne.symm ha.ne,Ne.symm hb.ne]
      have h := girth v walk cycle
      simp [walk] at h
    let independent (I : Finset (Fin n)) := ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b
    have add {S : Finset (Fin n)} (hS : independent S) {v : Fin n}
        (sep : ∀ w ∈ S, ¬G.Adj w v) : independent (insert v S) := by
      intro u hu w hw uw
      by_cases same : u = v
      · subst u
        rcases Finset.mem_insert.mp hw with h | hw
        · exact G.irrefl (h ▸ uw : G.Adj v v)
        · exact sep _ hw uw.symm
      · have inS := (Finset.mem_insert.mp hu).resolve_left same
        rcases Finset.mem_insert.mp hw with h | hw
        · exact sep _ inS (h ▸ uw)
        · exact hS _ inS _ hw uw
    let family := Finset.univ.filter independent
    have member (I : Finset (Fin n)) : I ∈ family ↔ independent I := by simp [family]
    obtain ⟨I,hI,largest⟩ := family.exists_max_image Finset.card
        ⟨∅,(member ∅).mpr (by simp [independent])⟩
    have ind := (member I).mp hI
    refine ⟨I,ind,?_⟩
    let J : Finset (Fin n) := Finset.univ \ I
    let N (v : Fin n) := I.filter fun u => G.Adj u v
    have nonempty (v : Fin n) (hv : v ∈ J) : (N v).Nonempty := by
      by_contra! none
      have sep (u : Fin n) (hu : u ∈ I) (uv : G.Adj u v) : False :=
        (Finset.notMem_empty u) (none ▸ (Finset.mem_filter.mpr ⟨hu,uv⟩ : u ∈ N v))
      have more := largest (insert v I) ((member _).mpr (add ind sep))
      have hv' := (Finset.mem_sdiff.mp hv).2
      simp [Finset.card_insert_of_notMem hv'] at more
    let singles := J.filter fun v => (N v).card = 1
    have near (v : Fin n) (hv : v ∈ J) := Classical.choose_spec (nonempty v hv)
    let owner (v : Fin n) := if hv : v ∈ J then Classical.choose (nonempty v hv) else v
    have owns (v : Fin n) (hv : v ∈ J) : owner v ∈ N v := by simpa [owner,hv] using near v hv
    have unique (v : Fin n) (hv : v ∈ singles) (u : Fin n) (hu : u ∈ N v) : u = owner v :=
      Finset.card_le_one.mp (Finset.mem_filter.mp hv).2.le _ hu _ (owns _ (Finset.mem_filter.mp hv).1)
    have privateBound : singles.card ≤ I.card := by
      apply Finset.card_le_card_of_injOn owner
      · intro v hv
        exact (Finset.mem_filter.mp (owns _ (Finset.mem_filter.mp hv).1)).1
      · intro x hx y hy same
        by_contra xy
        let v := owner x
        have hxJ := (Finset.mem_filter.mp hx).1
        have hyJ := (Finset.mem_filter.mp hy).1
        have bothX := Finset.mem_filter.mp (owns _ hxJ)
        have bothY := Finset.mem_filter.mp (owns _ hyJ)
        have vx : G.Adj v x := bothX.2
        have vy : G.Adj v y := by
          change G.Adj (owner x) y
          rw [same]
          exact bothY.2
        have none (u : Fin n) (hu : u ∈ I.erase v) : ¬G.Adj u x ∧ ¬G.Adj u y := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hu
          exact ⟨fun h => ne (unique x hx u (Finset.mem_filter.mpr ⟨mem,h⟩)),
            fun h => ne ((unique y hy u (Finset.mem_filter.mpr ⟨mem,h⟩)).trans same.symm)⟩
        have erased : independent (I.erase v) := fun a ha b hb =>
          ind a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
        have addX := add erased (fun u hu => (none u hu).1)
        have swapped : independent (insert y (insert x (I.erase v))) := by
          apply add addX
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact triangleFree vx vy
          · exact (none u hu).2
        have more := largest _ ((member _).mpr swapped)
        have xout : x ∉ I.erase v := fun h => (Finset.mem_sdiff.mp hxJ).2 (Finset.mem_of_mem_erase h)
        have yout : y ∉ insert x (I.erase v) := by
          intro h
          rcases Finset.mem_insert.mp h with h | h
          · exact xy h.symm
          · exact (Finset.mem_sdiff.mp hyJ).2 (Finset.mem_of_mem_erase h)
        rw [Finset.card_insert_of_notMem yout,Finset.card_insert_of_notMem xout,
          Finset.card_erase_of_mem bothX.1] at more
        omega
    have upper : ∑ v ∈ J, (N v).card ≤ 3 * I.card := by
      have swap := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := I) (t := J) G.Adj
      change (∑ a ∈ I, (J.filter (G.Adj a)).card) = ∑ v ∈ J, (N v).card at swap
      rw [← swap]
      calc
        _ ≤ ∑ _a ∈ I, 3 := by
          apply Finset.sum_le_sum
          intro a _
          have sub : J.filter (G.Adj a) ⊆ G.neighborFinset a := fun b hb =>
            (G.mem_neighborFinset a b).mpr (Finset.mem_filter.mp hb).2
          exact (Finset.card_le_card sub).trans_eq ((G.ncard_neighborSet a).symm.trans (degree a))
        _ = _ := by simp [Nat.mul_comm]
    have lower : 2 * J.card ≤ (∑ v ∈ J, (N v).card) + singles.card := by
      have count : (∑ v ∈ J, if (N v).card = 1 then 1 else 0) = singles.card := by
        simp [singles,Finset.sum_boole]
      rw [← count,← Finset.sum_add_distrib]
      calc
        _ = ∑ _v ∈ J, 2 := by simp [Nat.mul_comm]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro v hv
          have h := Finset.card_pos.mpr (nonempty v hv)
          split <;> omega
    have total : J.card + I.card = n := by
      simpa only [Finset.card_univ,Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I)
    omega
  have doubleStar (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (degree : ∀ v, (G.neighborSet v).ncard = 3) (H : Finset (Fin n))
      (few : 6 * H.card < n) :
      ∃ u v, G.Adj u v ∧ ∀ w, w = u ∨ w = v ∨ G.Adj u w ∨ G.Adj v w → w ∉ H := by
    classical
    let B := (H.biUnion (fun x => G.neighborFinset x)) \ H
    let C := (H ∪ B)ᶜ
    have deg (x : Fin n) : (G.neighborFinset x).card = 3 := by
      simpa only [SimpleGraph.ncard_neighborSet, SimpleGraph.card_neighborFinset_eq_degree]
        using degree x
    have inC {x : Fin n} : x ∈ C ↔ x ∉ H ∧ x ∉ B := by simp [C]
    have avoids {x : Fin n} (hx : x ∈ C) {y : Fin n} (hxy : G.Adj x y) : y ∉ H := by
      intro hy
      apply (inC.mp hx).2
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr
        ⟨y, hy, (G.mem_neighborFinset _ _).mpr hxy.symm⟩, (inC.mp hx).1⟩
    suffices ∃ u ∈ C, ∃ v ∈ C, G.Adj u v by
      obtain ⟨u, hu, v, hv, edge⟩ := this
      refine ⟨u, v, edge, ?_⟩
      intro w hw
      rcases hw with rfl | rfl | adj | adj
      · exact (inC.mp hu).1
      · exact (inC.mp hv).1
      · exact avoids hu adj
      · exact avoids hv adj
    by_contra! none
    have smallB : B.card ≤ 3 * H.card := calc
      B.card ≤ (H.biUnion (fun x => G.neighborFinset x)).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ ∑ x ∈ H, (G.neighborFinset x).card := Finset.card_biUnion_le
      _ = 3 * H.card := by simp [deg, Nat.mul_comm]
    have fromC (x : Fin n) (hx : x ∈ C) : 3 ≤ (B.bipartiteAbove G.Adj x).card := by
      rw [← deg x]
      apply Finset.card_le_card
      intro y hy
      have adj := (G.mem_neighborFinset _ _).mp hy
      refine (Finset.mem_bipartiteAbove _).mpr ⟨?_, adj⟩
      by_contra hyB
      exact none x hx y (inC.mpr ⟨avoids hx adj, hyB⟩) adj
    have fromB (y : Fin n) (hy : y ∈ B) : (C.bipartiteBelow G.Adj y).card ≤ 2 := by
      obtain ⟨z, hz, hzy⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hy).1
      have hzy' : z ∈ G.neighborFinset y :=
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hzy).symm
      have sub : C.bipartiteBelow G.Adj y ⊆ (G.neighborFinset y).erase z := by
        intro x hx
        obtain ⟨xc, adj⟩ := (Finset.mem_bipartiteBelow _).mp hx
        exact Finset.mem_erase.mpr ⟨fun h => (inC.mp xc).1 (h ▸ hz),
          (G.mem_neighborFinset _ _).mpr adj.symm⟩
      calc
        _ ≤ ((G.neighborFinset y).erase z).card := Finset.card_le_card sub
        _ = 2 := by rw [Finset.card_erase_of_mem hzy', deg]
    have balance := Finset.card_nsmul_le_card_nsmul G.Adj fromC fromB
    have capacity : C.card * 3 ≤ B.card * 2 := by simpa using balance
    have total : C.card + (H ∪ B).card = n := by
      simpa only [C, Fintype.card_fin] using (H ∪ B).card_compl_add_card
    have union := Finset.card_union_le H B
    omega
  have twoReadEdge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (degree : ∀ v, (G.neighborSet v).ncard = 3) (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length)
      (r : Fin n → ℕ) (s : ℕ)
      (ports : ∑ v, r v ≤ s + 1)
      (small : ∀ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) →
        s + 1 < G.edgeFinset.card + T.card) :
      (∃ v, r v ≤ 1) ∨ ((∀ w, 2 ≤ r w) ∧
      (∀ S : Finset (Fin n), (∀ w ∈ S, 3 ≤ r w) → 6 * S.card < n) ∧
      ∃ u v, G.Adj u v ∧ ∀ w, w = u ∨ w = v ∨ G.Adj u w ∨ G.Adj v w → r w = 2) := by
    by_cases rare : ∃ v, r v ≤ 1
    · exact Or.inl rare
    right
    have two (v : Fin n) : 2 ≤ r v := by
      have h : ¬r v ≤ 1 := fun h => rare ⟨v,h⟩
      omega
    let H := Finset.univ.filter (fun v => 3 ≤ r v)
    have count (v : Fin n) : 2 + (if 3 ≤ r v then 1 else 0) ≤ r v := by
      have := two v
      split <;> omega
    have cost := Finset.sum_le_sum (s := Finset.univ) (fun v _ => count v)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Finset.sum_boole] at cost
    change n * 2 + H.card ≤ ∑ v, r v at cost
    obtain ⟨I,ind,large⟩ := largeIndependent n G degree girth
    have cover : ∀ a b, G.Adj a b → a ∈ Iᶜ ∨ b ∈ Iᶜ := by
      intro a b adj
      by_cases ha : a ∈ I
      · right
        exact Finset.mem_compl.mpr (fun hb => ind a ha b hb adj)
      · exact Or.inl (Finset.mem_compl.mpr ha)
    have budget := small Iᶜ cover
    have partition : Iᶜ.card + I.card = n := by simp
    have deg (v : Fin n) : G.degree v = 3 := (G.ncard_neighborSet v).symm.trans (degree v)
    have sumDeg := G.sum_degrees_eq_twice_card_edges
    simp only [deg,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at sumDeg
    have few : 6 * H.card < n := by omega
    have density (S : Finset (Fin n)) (high : ∀ w ∈ S, 3 ≤ r w) : 6 * S.card < n := by
      have sub : S ⊆ H := fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _,high w hw⟩
      have := Finset.card_le_card sub
      omega
    obtain ⟨u,v,edge,clear⟩ := doubleStar n G degree H few
    refine ⟨two,density,u,v,edge,fun w near => ?_⟩
    have low : ¬3 ≤ r w := fun hw =>
      clear w near (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)
    have := two w
    omega
  -- Deleting a cover vertex removes three edges and one cover vertex.
  have coverCut (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (f : (Fin n → Bool) → Bool) (degree : ∀ v, (G.neighborSet v).ncard = 3)
      (edge : ∃ a b, G.Adj a b)
      (spec : ∀ x, f x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
      (s : ℕ) (T : Finset (Fin n)) (cover : ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T)
      (budget : G.edgeFinset.card + T.card ≤ s + 1) :
      ∃ v : Fin n, ∃ t : ℕ, t+4 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t := by
    obtain ⟨a,b,ab⟩ := edge
    have coveredEdge : ∃ v ∈ T, ∃ u, G.Adj u v := by
      rcases cover a b ab with h | h
      · exact ⟨a,h,b,ab.symm⟩
      · exact ⟨b,h,a,ab⟩
    obtain ⟨v,hv,u,uv⟩ := coveredEdge
    let H := G.deleteIncidenceSet v
    let T' := T.erase v
    have other : ∃ j, G.Adj u j ∧ j ≠ v := by
      by_contra! h
      have sub : G.neighborSet u ⊆ {v} := fun j hj => Set.mem_singleton_iff.mpr (h j hj)
      have small := Set.ncard_le_ncard sub
      rw [degree,Set.ncard_singleton] at small
      omega
    obtain ⟨j,uj,hj⟩ := other
    have kept : H.Adj u j := SimpleGraph.deleteIncidenceSet_adj.mpr ⟨uj,uv.ne,hj⟩
    have pos : 0 < H.edgeFinset.card := Finset.card_pos.mpr
        ⟨s(u,j),SimpleGraph.mem_edgeFinset.mpr kept⟩
    have cover' (a b : Fin n) (hab : H.Adj a b) : a ∈ T' ∨ b ∈ T' := by
      obtain ⟨old,ha,hb⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hab
      exact (cover a b old).imp (fun h => Finset.mem_erase.mpr ⟨ha,h⟩)
        (fun h => Finset.mem_erase.mpr ⟨hb,h⟩)
    have he : H.edgeFinset.card = G.edgeFinset.card - 3 := by
      have hd : G.degree v = 3 := (G.ncard_neighborSet v).symm.trans (degree v)
      exact (G.card_edgeFinset_deleteIncidenceSet v).trans (by rw [hd])
    have ht : T'.card = T.card - 1 := Finset.card_erase_of_mem hv
    have bound : H.edgeFinset.card + T'.card - 1 + 4 ≤ s := by
      have htp := Finset.card_pos.mpr ⟨v,hv⟩
      omega
    have cut := stars n H T' ⟨u,j,kept⟩ cover'
    have evalCut : (fun x : Fin n → Bool => decide (∃ i j, H.Adj i j ∧ x i = true ∧ x j = true))
        = (fun x : Fin n → Bool => f (Function.update x v false)) := by
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq,spec]
      constructor
      · rintro ⟨i,j,ij,hi,hj'⟩
        obtain ⟨old,ni,nj⟩ := SimpleGraph.deleteIncidenceSet_adj.mp ij
        exact ⟨i,j,old,by simpa [Function.update_of_ne ni] using hi,
          by simpa [Function.update_of_ne nj] using hj'⟩
      · rintro ⟨i,j,ij,hi,hj'⟩
        have ni : i ≠ v := by intro eq; simp [eq] at hi
        have nj : j ≠ v := by intro eq; simp [eq] at hj'
        exact ⟨i,j,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ij,ni,nj⟩,
          by simpa [Function.update_of_ne ni] using hi,by simpa [Function.update_of_ne nj] using hj'⟩
    exact ⟨v,_,bound,evalCut ▸ cut⟩
  have readerCases (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool) (C : Circuit)
      (degree : ∀ v, (G.neighborSet v).ncard = 3) (edge : ∃ i j, G.Adj i j)
      (spec : ∀ x, f x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
      (fan : FanInTwo C) (eval : circuitFun n C = f)
      (least : ∀ s, HasCircuitSize n f s → C.size ≤ s) :
      (∀ v : Fin n, let rs := C.gates.filter fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
        rs.length ≤ 3 ∧ (rs.length = 3 → ∀ g ∈ rs, g.op = .or)) ∨
      ∃ v : Fin n, ∃ t, t + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t := by
    classical
    let readers (v : Fin n) := C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    by_cases high : ∃ v : Fin n, 4 ≤ (readers v).length ∨
        (readers v).length = 3 ∧ ∃ g ∈ readers v, g.op ≠ .or
    · obtain ⟨v,hv⟩ := high
      obtain ⟨i,j,hij⟩ := edge
      have distinct : ∃ u : Fin n, u ≠ v := by
        by_cases hi : i = v
        · exact ⟨j, fun hj => hij.ne (hi.trans hj.symm)⟩
        · exact ⟨i, hi⟩
      obtain ⟨u,hu⟩ := distinct
      have survives : ∃ w, G.Adj u w ∧ w ≠ v := by
        by_contra! h
        have sub : G.neighborSet u ⊆ {v} := fun w hw => Set.mem_singleton_iff.mpr (h w hw)
        have small := Set.ncard_le_ncard sub
        simp [degree u] at small
      obtain ⟨w,huw,hw⟩ := survives
      have nonconstant : ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false) := by
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        have hz : f (Function.update (fun _ => false) v false) ≠ true := by
          intro pos
          obtain ⟨a,b,_,ha,_⟩ := (spec _).mp pos
          simp [Function.update] at ha
        have ho : f (Function.update (fun _ => true) v false) = true :=
          (spec _).mpr ⟨u,w,huw,by simp [Function.update_of_ne hu],by simp [Function.update_of_ne hw]⟩
        rw [ho]
        exact hz
      exact Or.inr ⟨v, readCut n f C v fan eval least nonconstant hv⟩
    · left
      intro v
      change (readers v).length ≤ 3 ∧ ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)
      constructor
      · by_contra h
        exact high ⟨v, Or.inl (by omega)⟩
      · intro h3 g hg
        by_contra h
        exact high ⟨v, Or.inr ⟨h3,g,hg,h⟩⟩
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have getD_snoc_lt {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    simp [List.getD, List.getElem?_append_left hi]

  have getD_snoc_eq {α : Type} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
      (l ++ [x]).getD i d = x := by
    subst hi
    simp [List.getD]
  let reads (v : ℕ) (g : Gate) :=
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
  have positiveReads (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
      (hC : FanInTwo C)
      (hf : ∀ x, circuitFun n C x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
      (degree : ∀ v, (G.neighborSet v).ncard = 3) (v : Fin n) :
      0 < (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length := by
    classical
    have ofFn_getD_lt : ∀ (x : Fin n → Bool) (i : ℕ) (hi : i < n),
        (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
      intro x i hi
      rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]
    have gate_eval_agree : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
        g.inputs.length ≤ 2 → ∀ (w₁ w₂ : List Bool) (v : ℕ),
        (∀ i, i ≠ v → w₁.getD i false = w₂.getD i false) →
        reads v g = false →
        g.op.eval (g.inputs.map fun i => w₁.getD i false) =
          g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
      intro g hop hlen w₁ w₂ v hag hnr
      have hnr' : v ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2) := by
        intro hm
        have ht : reads v g = true := List.contains_iff_mem.2 hm
        rw [hnr] at ht
        cases ht
      have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
      rcases hop' with h | h | h
      · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
          rw [h]
          have : GateOp.and.eval [false] = false := rfl
          rw [this]
          exact List.take_of_length_le hlen
        rw [ht2] at hnr'
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hag i (fun he => hnr' (he ▸ hi))
      · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
          rw [h]
          have : GateOp.or.eval [false] = false := rfl
          rw [this]
          exact List.take_of_length_le hlen
        rw [ht2] at hnr'
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hag i (fun he => hnr' (he ▸ hi))
      · rw [h] at hnr' ⊢
        have : GateOp.not.eval [false] = true := rfl
        rw [this] at hnr'
        rcases hgins : g.inputs with _ | ⟨a, rest⟩
        · rfl
        · rw [hgins] at hnr'
          have hav : a ≠ v := fun he => hnr' (by simp [he])
          show (!(w₁.getD a false)) = (!(w₂.getD a false))
          rw [hag a hav]
    have wiresFrom_agree_eff : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        ∀ (v : ℕ) (w₁ w₂ : List Bool), w₁.length = w₂.length →
        (∀ i, i ≠ v → w₁.getD i false = w₂.getD i false) →
        (∀ g ∈ gs, reads v g = false) →
        ∀ i, i ≠ v → (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
      intro gs
      induction gs with
      | nil => intro _ v w₁ w₂ _ hag _ i hi; exact hag i hi
      | cons g rest ih =>
        intro hok v w₁ w₂ hlen hag hnr i hi
        have h1 : wiresFrom (g :: rest) w₁ =
            wiresFrom rest (w₁ ++ [g.op.eval (g.inputs.map fun k => w₁.getD k false)]) := rfl
        have h2 : wiresFrom (g :: rest) w₂ =
            wiresFrom rest (w₂ ++ [g.op.eval (g.inputs.map fun k => w₂.getD k false)]) := rfl
        rw [h1, h2]
        have hge := gate_eval_agree g (hok g List.mem_cons_self).1 (hok g List.mem_cons_self).2
          w₁ w₂ v hag (hnr g List.mem_cons_self)
        apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) v _ _
          (by simp [hlen]) _ (fun g' hg' => hnr g' (List.mem_cons_of_mem _ hg')) i hi
        intro j hj
        by_cases hlt : j < w₁.length
        · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
          exact hag j hj
        · by_cases heq : j = w₁.length
          · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega), hge]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    change 0 < (C.gates.filter (reads v.val)).length
    have hd : (G.neighborSet v).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [degree v]; decide)
    by_contra h0
    have hempty : ∀ g ∈ C.gates, reads v.val g = false := by
      intro g hg
      cases hr : reads v.val g with
      | false => rfl
      | true =>
        have hm : g ∈ C.gates.filter (reads v.val) := List.mem_filter.2 ⟨hg, hr⟩
        have hpos : 0 < (C.gates.filter (reads v.val)).length := List.length_pos_of_mem hm
        omega
    by_cases hout : C.output = v.val
    · let xv : Fin n → Bool := fun j => decide (j = v)
      have h1 : circuitFun n C xv = true := by
        show (wiresFrom C.gates (List.ofFn xv)).getD C.output false = true
        have hlen : (List.ofFn xv).length = n := List.length_ofFn
        have hkeep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
            (wiresFrom gs w).getD i false = w.getD i false := by
          intro gs
          induction gs with
          | nil => intro w i _; rfl
          | cons g rest ih =>
            intro w i hi
            have hstep : wiresFrom (g :: rest) w =
                wiresFrom rest (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) := rfl
            rw [hstep, ih _ i (by simp; omega), getD_snoc_lt _ _ _ _ hi]
        rw [hout, hkeep _ _ _ (by rw [hlen]; exact v.isLt), ofFn_getD_lt xv v.val v.isLt]
        simp [xv]
      obtain ⟨u,w,huw,hu,hw⟩ := (hf xv).mp h1
      have ueq : u = v := by simpa [xv] using hu
      have weq : w = v := by simpa [xv] using hw
      exact huw.ne (ueq.trans weq.symm)
    · obtain ⟨u, hu⟩ := hd
      have huv : G.Adj v u := hu
      let x1 : Fin n → Bool := fun j => decide (j = u)
      let x2 : Fin n → Bool := fun j => decide (j = u ∨ j = v)
      have hag : ∀ i, i ≠ v.val → (List.ofFn x1).getD i false = (List.ofFn x2).getD i false := by
        intro i hi
        by_cases hlt : i < n
        · rw [ofFn_getD_lt x1 i hlt, ofFn_getD_lt x2 i hlt]
          have hne : (⟨i, hlt⟩ : Fin n) ≠ v := fun e => hi (congrArg Fin.val e)
          simp [x1, x2, hne]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have heq : circuitFun n C x1 = circuitFun n C x2 :=
        wiresFrom_agree_eff C.gates hC v.val (List.ofFn x1) (List.ofFn x2) (by simp) hag hempty
          C.output hout
      have hf2 : circuitFun n C x2 = true := (hf x2).2 ⟨v, u, huv, by simp [x2], by simp [x2]⟩
      have hf1 : circuitFun n C x1 ≠ true := by
        intro h
        obtain ⟨a,b,hab,ha,hb⟩ := (hf _).mp h
        have au : a = u := by simpa [x1] using ha
        have bu : b = u := by simpa [x1] using hb
        exact hab.ne (au.trans bu.symm)
      exact hf1 (heq.trans hf2)
  -- Every gate output of a minimum circuit occupies a later input slot or the output slot.
  have readerBudget : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
    (∑ v : Fin n, (C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length) ≤ C.size + 1 := by
    have wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

    have wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
        wiresFrom (g :: gs) w =
          wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

    have wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
        wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
      induction gs₁ generalizing w with
      | nil => rfl
      | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

    have wiresFrom_length (gs : List Gate) (w : List Bool) :
        (wiresFrom gs w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp [wiresFrom]
      | cons g gs ih =>
        rw [wiresFrom_cons, ih]
        simp
        omega

    let OkGate (g : Gate) : Prop :=
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

    let substWire (k a i : ℕ) : ℕ :=
      if i < k then i else if i = k then a else i - 1

    let substGate (k a : ℕ) (g : Gate) : Gate :=
      ⟨g.op, g.inputs.map (substWire k a)⟩

    have substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
      ⟨h.1, by simp [substGate]; exact h.2⟩

    let deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
      ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
        substWire (m + j) a C.output⟩

    have deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
        (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h1 | h1
      · exact hok g (List.mem_of_mem_take h1)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
        exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))


    have deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
        (deleteGate m C j a).gates.length = C.gates.length - 1 := by
      simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
      omega


    have deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
        (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
        (x : List Bool) (hx : x.length = m) :
        ∀ i < m + C.gates.length, i ≠ m + j →
          ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
            (C.wires x).getD i false := by
      have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
        have h1 := List.take_append_drop j C.gates
        have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
        rw [h2] at h1
        simpa only [List.append_assoc, List.singleton_append] using h1.symm
      show ∀ i < m + C.gates.length, i ≠ m + j →
          (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
              (substWire (m + j) 0 i) false =
            (wiresFrom C.gates x).getD i false
      set w₂ := wiresFrom (C.gates.take j) x with hw₂
      set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
      have hw₂_len : w₂.length = m + j := by
        rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
      have hw₁_len : w₁.length = m + j + 1 := by
        rw [hw₁, wiresFrom_length, hw₂_len]; simp
      have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
        intro g hg
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
        rw [List.getElem_drop]
        exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
      have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
          w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
          (∀ g ∈ gs, (m + j) ∉ g.inputs) →
          (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
          ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
            (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
              (wiresFrom gs w₁').getD i false := by
        intro gs
        induction gs with
        | nil =>
          intro w₁' w₂' _ _ _ hag i hi hne
          exact hag i hi hne
        | cons g rest ih =>
          intro w₁' w₂' hlen' hk' hnod hag'
          rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
          have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
              (g.inputs.map fun i => w₁'.getD i false) := by
            simp only [substGate, List.map_map]
            apply List.map_congr_left
            intro i hi
            simp only [Function.comp_apply]
            have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
            by_cases hlt : i < w₁'.length
            · exact hag' i hlt hne
            · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
                unfold substWire; split_ifs <;> omega
              rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
          rw [hmap]
          apply ih _ _ (by simp [hlen']) (by simp; omega)
            (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
          intro i hi hne
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlt : i < w₁'.length
          · have hsublt : substWire (m + j) 0 i < w₂'.length := by
              unfold substWire; split_ifs <;> omega
            rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
            exact hag' i hlt hne
          · have hieq : i = w₁'.length := by omega
            have hsubeq : substWire (m + j) 0 i = w₂'.length := by
              unfold substWire; split_ifs <;> omega
            rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
      intro i hi hne
      rw [wiresFrom_append, ← hw₂]
      conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
      have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
        rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
      apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
      intro u hu hune
      have hlt : u < m + j := by omega
      simp only [substWire, hlt, ↓reduceIte]
      rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

    have deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
        (j : ℕ) (hj : j < C.gates.length)
        (hout : C.output ≠ m + j)
        (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
        HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
      refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
        by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
      intro x
      show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
        (C.wires (List.ofFn x)).getD C.output false
      by_cases hlt : C.output < m + C.gates.length
      · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
      · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
          rw [deleteGate_len m C j 0 hj]
          unfold substWire
          split_ifs <;> omega
        have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
            m + (deleteGate m C j 0).gates.length := by
          show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
        have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
          show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    let slots (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs

    have gateSlotBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
        (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
      induction gs with
      | nil => simp
      | cons g tail ih =>
        have hg := h g List.mem_cons_self
        have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega

    have countBound (xs : List ℕ) (S : Finset ℕ) :
        ∑ i ∈ S, xs.count i ≤ xs.length := by
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
        by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

    have filteredSlots (v : ℕ) (gs : List Gate) :
        (gs.filter (reads v)).length ≤ (gs.flatMap Gate.inputs).count v := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        simp only [List.flatMap_cons, List.count_append, List.filter_cons]
        split
        next h =>
          have hm : v ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.mp h)
          have hp := List.count_pos_iff.mpr hm
          simp only [List.length_cons]
          omega
        next => omega

    have internalSlot {n : ℕ} (C : Circuit) (hC : FanInTwo C)
        (hmin : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
        (i : ℕ) (hi : i < C.gates.length) : n+i ∈ slots C := by
      by_contra hn
      have hout : C.output ≠ n+i := fun e => hn (by simp [slots,e])
      have hno : ∀ j, (hj : j < C.gates.length) → i < j → n+i ∉ C.gates[j].inputs := by
        intro j hj _ hm
        exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,List.getElem_mem hj,hm⟩))
      have bad := hmin _ (deleteDeadGate C hC i hi hout hno)
      change C.gates.length ≤ C.gates.length - 1 at bad
      omega


    intro n C least
    classical
    have sizeBound (s : ℕ) (has : HasCircuitSize n (circuitFun n C) s) : C.size ≤ s := by
      obtain ⟨D,fan,small,same⟩ := has
      exact (least.2 D fan (funext same)).trans small
    let cnt (i : ℕ) := (slots C).count i
    have input (v : Fin n) : (C.gates.filter (reads v.val)).length ≤ cnt v.val := by
      have bound := filteredSlots v.val C.gates
      simp only [cnt, slots, List.count_cons]
      omega
    have internal (i : ℕ) (hi : i ∈ Finset.range C.gates.length) : 1 ≤ cnt (n+i) :=
      List.count_pos_iff.mpr (internalSlot C least.1 sizeBound i (Finset.mem_range.mp hi))
    have lowerI := Finset.sum_le_sum internal
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at lowerI
    have lowerV := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => input v)
    rw [Fin.sum_univ_eq_sum_range] at lowerV
    have total := countBound (slots C) (Finset.range (n+C.gates.length))
    change ∑ i ∈ Finset.range (n+C.gates.length), cnt i ≤ (slots C).length at total
    rw [Finset.sum_range_add] at total
    have lengthBound := gateSlotBound C.gates (fun g hg => (least.1 g hg).2)
    simp only [slots, List.length_cons] at total
    change (∑ v : Fin n, (C.gates.filter (reads v.val)).length) ≤ C.gates.length + 1
    omega
  apply stripIsolates
  intro n G f degree girth edge spec s size
  let _ : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  let k := Nat.find (show ∃ j, HasCircuitSize n f j from ⟨s,size⟩)
  have best : HasCircuitSize n f k := Nat.find_spec _
  obtain ⟨C,fan,hk,eval⟩ := best
  have hfun : circuitFun n C = f := funext eval
  have least (j : ℕ) (hc : HasCircuitSize n f j) : C.size ≤ j :=
    hk.trans (Nat.find_min' _ hc)
  have minimal : IsMinimalCircuit n C := ⟨fan,fun D hD eq =>
    least D.size ⟨D,hD,le_rfl,congrFun (eq.trans hfun)⟩⟩
  suffices cut : ∃ v : Fin n, ∃ t, t + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) t by
    obtain ⟨v,t,ht,hc⟩ := cut
    exact ⟨v,t,ht.trans (least s size),hc⟩
  by_cases paid : ∃ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1
  · obtain ⟨T,covers,budget⟩ := paid
    exact coverCut n G f degree edge spec C.size T covers budget
  have small (T : Finset (Fin n)) (covers : ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) :
      C.size + 1 < G.edgeFinset.card + T.card :=
    lt_of_not_ge (fun budget => paid ⟨T,covers,budget⟩)
  rcases readerCases n G f C degree edge spec fan hfun least with sparse | cut
  · let rs (v : Fin n) := C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    have graphSpec : ∀ x, circuitFun n C x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
      simpa only [hfun] using spec
    rcases twoReadEdge n G degree girth (fun v => (rs v).length) C.size
        (readerBudget n C minimal) small with rare | ball
    · obtain ⟨v,hv⟩ := rare
      have pos : 0 < (rs v).length := positiveReads n G C fan graphSpec degree v
      have one : (rs v).length = 1 := by omega
      simpa only [hfun] using rareCase n G C degree girth minimal graphSpec small sparse ⟨v,one⟩
    · simpa only [hfun] using edgeCase n G C degree girth minimal graphSpec small sparse ball
  · exact cut
