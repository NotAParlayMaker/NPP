import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1872_846
  (overlapping :
    let S := PEqualNP.HeptadCover.singerLines3
    let X := fun (T L : Finset (Fin 13)) =>
      (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ L))
    let V := fun (C : Circuit) (r : ℕ) (x : List Bool) => (C.wires x).getD r false
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C →
      a < 26 + C.size → b < 26 + C.size →
      (∀ g ∈ C.gates, a ∉ g.inputs ∧ b ∉ g.inputs) →
      (∀ p l, p ∈ S l → V C a (X {p} {l}) = true ∨ V C b (X {p} {l}) = true) →
      (∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q →
        V C a (X Q (PEqualNP.HeptadCover.missLines S Q)) = false ∧
        V C b (X Q (PEqualNP.HeptadCover.missLines S Q)) = false) →
      (∃ p l, p ∈ S l ∧ V C a (X {p} {l}) = true ∧ V C b (X {p} {l}) = false) →
      (∃ p l, p ∈ S l ∧ V C b (X {p} {l}) = true ∧ V C a (X {p} {l}) = false) →
      (∃ p l, p ∈ S l ∧ V C a (X {p} {l}) = true ∧ V C b (X {p} {l}) = true) → 63 ≤ C.size)
  (disjoint :
    let S := PEqualNP.HeptadCover.singerLines3
    let X := fun (T L : Finset (Fin 13)) =>
      (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ L))
    let V := fun (C : Circuit) (r : ℕ) (x : List Bool) => (C.wires x).getD r false
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C →
      a < 26 + C.size → b < 26 + C.size →
      (∀ g ∈ C.gates, a ∉ g.inputs ∧ b ∉ g.inputs) →
      (∀ p l, p ∈ S l → V C a (X {p} {l}) = true ∨ V C b (X {p} {l}) = true) →
      (∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q →
        V C a (X Q (PEqualNP.HeptadCover.missLines S Q)) = false ∧
        V C b (X Q (PEqualNP.HeptadCover.missLines S Q)) = false) →
      (∃ p l, p ∈ S l ∧ V C a (X {p} {l}) = true ∧ V C b (X {p} {l}) = false) →
      (∃ p l, p ∈ S l ∧ V C b (X {p} {l}) = true ∧ V C a (X {p} {l}) = false) →
      (∀ p l, p ∈ S l → V C a (X {p} {l}) = false ∨ V C b (X {p} {l}) = false) → 63 ≤ C.size)
  :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  -- The fold monotonicity proof adapts LowMergeWires.lean from this repository (Apache-2.0).
  let step (x : List Bool) (g : Gate) : List Bool :=
    x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]

  let run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

  let AO (g : Gate) : Prop := g.op = .and ∨ g.op = .or

  let isAnd (op : GateOp) : Bool :=
    @GateOp.rec (fun _ => Bool) true false false (fun _ => false) false op

  let prune (w : ℕ) (g : Gate) : Gate :=
    if isAnd g.op then
      if w ∈ g.inputs then ⟨.or, []⟩ else g
    else ⟨g.op, g.inputs.filter (· != w)⟩

  have pruneAnd (w : ℕ) (is : List ℕ) :
      prune w ⟨.and,is⟩ = (if w ∈ is then ⟨.or,[]⟩ else ⟨.and,is⟩) := rfl

  have pruneOr (w : ℕ) (is : List ℕ) :
      prune w ⟨.or,is⟩ = ⟨.or,is.filter (· != w)⟩ := rfl

  let removeReads (C : Circuit) (w : ℕ) : Circuit := ⟨C.gates.map (prune w), C.output⟩

  let cut (w : ℕ) (x : List Bool) (i : ℕ) : Bool :=
    if i = w then false else x.getD i false

  have prune_eval (w : ℕ) (g : Gate) (hg : AO g) (x : List Bool) :
      (prune w g).op.eval ((prune w g).inputs.map fun i => x.getD i false) =
        g.op.eval (g.inputs.map (cut w x)) := by
    obtain ⟨op,is⟩ := g
    rcases hg with e | e <;> change op = _ at e <;> subst op
    · by_cases hw : w ∈ is
      · have af : (is.map (cut w x)).all id = false := by
          cases hv : (is.map (cut w x)).all id
          · rfl
          · have := List.all_eq_true.mp hv (cut w x w) (List.mem_map.mpr ⟨w,hw,rfl⟩)
            simp [cut] at this
        rw [pruneAnd, if_pos hw]
        exact af.symm
      · have hm : is.map (fun i => x.getD i false) = is.map (cut w x) :=
          List.map_congr_left (fun i hi => by
            have hne : i ≠ w := fun e => hw (e ▸ hi)
            simp [cut,hne])
        rw [pruneAnd, if_neg hw]
        change (is.map (fun i => x.getD i false)).all id = (is.map (cut w x)).all id
        rw [hm]
    · rw [pruneOr]
      apply Bool.eq_iff_iff.mpr
      change ((is.filter (· != w)).map (fun i => x.getD i false)).any id = true ↔
        (is.map (cut w x)).any id = true
      simp only [List.any_eq_true, List.mem_map, List.mem_filter, id]
      constructor
      · rintro ⟨_,⟨i,⟨hi,hn⟩,rfl⟩,ht⟩
        have hn' : i ≠ w := by simpa using hn
        exact ⟨cut w x i,⟨i,hi,rfl⟩,by simpa [cut,hn']⟩
      · rintro ⟨_,⟨i,hi,rfl⟩,ht⟩
        have hn : i ≠ w := by rintro rfl; simp [cut] at ht
        exact ⟨x.getD i false,⟨i,⟨hi,by simpa using hn⟩,rfl⟩,by simpa [cut,hn] using ht⟩

  have prune_spec (w : ℕ) (g : Gate) (hg : AO g) :
      AO (prune w g) ∧ (prune w g).inputs.length ≤ g.inputs.length ∧
        (∀ i ∈ (prune w g).inputs, i ∈ g.inputs ∧ i ≠ w) := by
    obtain ⟨op,is⟩ := g
    rcases hg with e | e <;> change op = _ at e <;> subst op
    · rw [pruneAnd]
      by_cases hw : w ∈ is
      · simp [hw,AO]
      · rw [if_neg hw]
        exact ⟨Or.inl rfl, le_rfl, fun i hi => ⟨hi,fun e => hw (e ▸ hi)⟩⟩
    · rw [pruneOr]
      refine ⟨Or.inr rfl, List.length_filter_le _ _, ?_⟩
      intro i hi
      simpa using List.mem_filter.mp hi

  have removeReads_spec (C : Circuit) (w n : ℕ) (mono : Monotone2 C) (back : ReadsBack n C) :
      (removeReads C w).size = C.size ∧ Monotone2 (removeReads C w) ∧
        ReadsBack n (removeReads C w) ∧ ∀ g ∈ (removeReads C w).gates, w ∉ g.inputs := by
    have gl : (removeReads C w).gates.length = C.gates.length := by simp [removeReads]
    refine ⟨gl, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.mp hg
      obtain ⟨ho,hl⟩ := mono g₀ hg₀
      have h := prune_spec w g₀ (by simpa [AO] using ho)
      exact ⟨by simpa [AO] using h.1, h.2.1.trans hl⟩
    · intro j hj i hi
      have hj₀ : j < C.gates.length := gl ▸ hj
      have he : gateAt (removeReads C w) j = prune w (gateAt C j) := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj₀]
        simp [removeReads]
      rw [he] at hi
      have h := prune_spec w (gateAt C j) (by
        have h₀ : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem _ _ hj₀]
          exact List.getElem_mem _
        simpa [AO] using (mono _ h₀).1)
      exact back j hj₀ i (h.2.2 i hi).1
    · intro g hg hw
      obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.mp hg
      exact (prune_spec w g₀ (by simpa [AO] using (mono _ hg₀).1)).2.2 w hw |>.2 rfl

  have run_prefix (gs : List Gate) (x : List Bool) :
      ∃ extra, run gs x = x ++ extra := by
    induction gs generalizing x with
    | nil => exact ⟨[], by simp [run]⟩
    | cons g gs ih =>
      obtain ⟨extra,h⟩ := ih (step x g)
      exact ⟨_, by simpa [run,step,List.append_assoc] using h⟩

  have run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
      (run gs x).getD i false = x.getD i false := by
    obtain ⟨extra,h⟩ := run_prefix gs x
    rw [h, List.getD_append _ _ _ _ hi]

  have stepEq (w : ℕ) (g : Gate) (hg : AO g) (x : List Bool) (hx : x.getD w false = false) :
      step x (prune w g) = step x g := by
    have hc : cut w x = fun i => x.getD i false := by
      funext i
      unfold cut
      split
      · rename_i e
        subst i
        exact hx.symm
      · rfl
    unfold step
    rw [prune_eval w g hg,hc]

  have run_same (w : ℕ) (gs : List Gate) (ao : ∀ g ∈ gs, AO g) (x : List Bool)
      :
      (run (gs.map (prune w)) x).getD w false = (run gs x).getD w false := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      by_cases hi : w < x.length
      · rw [run_getD _ _ _ hi,run_getD _ _ _ hi]
      · have hfalse : x.getD w false = false := List.getD_eq_default _ _ (by omega)
        change (run (gs.map (prune w)) (step x (prune w g))).getD w false =
          (run gs (step x g)).getD w false
        rw [stepEq w g (ao _ List.mem_cons_self) _ hfalse]
        exact ih (fun g hg => ao g (List.mem_cons_of_mem _ hg)) _

  have run_same_of_false (w : ℕ) (gs : List Gate) (ao : ∀ g ∈ gs, AO g) (x : List Bool)
      (hf : (run gs x).getD w false = false) : run (gs.map (prune w)) x = run gs x := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      have hx : x.getD w false = false := by
        by_cases hi : w < x.length
        · rwa [run_getD _ _ _ hi] at hf
        · exact List.getD_eq_default _ _ (by omega)
      change run (gs.map (prune w)) (step x (prune w g)) = run gs (step x g)
      rw [stepEq w g (ao _ List.mem_cons_self) _ hx]
      exact ih (fun g hg => ao g (List.mem_cons_of_mem _ hg)) _ hf

  let LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true
  have eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
      (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
      op.eval (l.map f) = true → op.eval (l.map f') = true := by
    rcases hop with rfl | rfl
    · change (l.map f).all id = true → (l.map f').all id = true
      simp only [List.all_eq_true, List.mem_map, id]
      intro H x hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact h i (H (f i) ⟨i, hi, rfl⟩)
    · change (l.map f).any id = true → (l.map f').any id = true
      simp only [List.any_eq_true, List.mem_map, id]
      rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩


  have run_le (w : ℕ) (gs : List Gate) (ao : ∀ g ∈ gs, AO g)
      (a b : List Bool) (same : a.length = b.length) (h : LeL a b) :
      LeL (run (gs.map (prune w)) a) (run gs b) := by
    induction gs generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      change LeL (run (gs.map (prune w)) (step a (prune w g))) (run gs (step b g))
      apply ih (fun g hg => ao g (List.mem_cons_of_mem _ hg))
      · simp [step, same]
      · intro i hi
        unfold step at hi ⊢
        by_cases haa : i < a.length
        · rw [List.getD_append _ _ _ _ haa] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact h i hi
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega),← same]
          by_cases es : i-a.length=0
          · rw [es] at hi ⊢
            simp only [List.getD_cons_zero] at hi ⊢
            rw [prune_eval w g (ao _ List.mem_cons_self)] at hi
            apply eval_mono g.op (ao _ List.mem_cons_self) _ _ _ ?_ hi
            intro k hk
            by_cases he : k = w
            · simp [cut,he] at hk
            · exact h k (by simpa [cut, he] using hk)
          · obtain ⟨k,hk⟩ : ∃ k, i-a.length=k+1 := ⟨i-a.length-1,by omega⟩
            rw [hk] at hi
            simp at hi

  have removeReads_values (C : Circuit) (w : ℕ) (mono : Monotone2 C) (x : List Bool) :
      (∀ i, ((removeReads C w).wires x).getD i false = true → (C.wires x).getD i false = true) ∧
      ((removeReads C w).wires x).getD w false = (C.wires x).getD w false ∧
      ((C.wires x).getD w false = false → (removeReads C w).wires x = C.wires x) := by
    have ao : ∀ g ∈ C.gates, AO g := fun g hg => by simpa [AO] using (mono g hg).1
    exact ⟨run_le w C.gates ao x x rfl (fun _ h => h),
      run_same w C.gates ao x, run_same_of_false w C.gates ao x⟩

  have combine {u v ua va ub vb : Bool}
      (ea : ua = u) (eb : vb = va) (la : va = true → v = true) (lb : ub = true → ua = true)
      (forceA : u = false → va = v) (forceB : va = false → ub = ua) :
      (ub || vb) = (u || v) ∧ (u=true → v=false → ub=true ∧ vb=false) ∧
        (v=true → u=false → vb=true ∧ ub=false) := by
    have finite : ∀ u v ua va ub vb : Bool,
        ua = u → vb = va → (va = true → v = true) → (ub = true → ua = true) →
        (u = false → va = v) → (va = false → ub = ua) →
        (ub || vb) = (u || v) ∧ (u=true → v=false → ub=true ∧ vb=false) ∧
          (v=true → u=false → vb=true ∧ ub=false) := by decide
    exact finite u v ua va ub vb ea eb la lb forceA forceB

  have removeReads_both (n : ℕ) (C : Circuit) (a b : ℕ) (m : Monotone2 C) (r : ReadsBack n C) :
      ∃ D : Circuit, D.size=C.size ∧ Monotone2 D ∧ ReadsBack n D ∧
        (∀ g ∈ D.gates, a ∉ g.inputs ∧ b ∉ g.inputs) ∧
        ∀ x : List Bool, x.length=n →
          have u := (C.wires x).getD a false
          have v := (C.wires x).getD b false
          have u' := (D.wires x).getD a false
          have v' := (D.wires x).getD b false
          (u' || v') = (u || v) ∧
          (u=true → v=false → u'=true ∧ v'=false) ∧
          (v=true → u=false → v'=true ∧ u'=false) := by
    let A := removeReads C a
    let B := removeReads A b
    obtain ⟨hs,hm,hr,hna⟩ := removeReads_spec C a n m r
    obtain ⟨ht,hmb,hrb,hnb⟩ := removeReads_spec A b n hm hr
    refine ⟨B,ht.trans hs,hmb,hrb,?_,?_⟩
    · intro g hg
      refine ⟨?_, hnb g hg⟩
      obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.mp hg
      have ao : AO g₀ := by simpa [AO] using (hm g₀ hg₀).1
      exact fun ha => hna g₀ hg₀ ((prune_spec b g₀ ao).2.2 a ha).1
    · intro x _
      dsimp only
      obtain ⟨la,ea,fa⟩ := removeReads_values C a m x
      obtain ⟨lb,eb,fb⟩ := removeReads_values A b hm x
      change (A.wires x).getD a false = (C.wires x).getD a false at ea
      change (B.wires x).getD b false = (A.wires x).getD b false at eb
      have forceA : (C.wires x).getD a false = false →
          (A.wires x).getD b false = (C.wires x).getD b false := fun h => by rw [fa h]
      have forceB : (A.wires x).getD b false = false →
          (B.wires x).getD a false = (A.wires x).getD a false := fun h => by rw [fb h]
      have la' := la b
      have lb' := lb a
      change ((A.wires x).getD b false = true → (C.wires x).getD b false = true) at la'
      change ((B.wires x).getD a false = true → (A.wires x).getD a false = true) at lb'
      exact combine ea eb la' lb' forceA forceB

  intro C a b mono back ha hb
  dsimp only
  intro accept reject leftOnly rightOnly
  obtain ⟨D,hs,hm,hr,hsink,hval⟩ := removeReads_both 26 C a b mono back
  rw [← hs]
  let S := PEqualNP.HeptadCover.singerLines3
  let X := fun (T L : Finset (Fin 13)) =>
    (List.ofFn fun q : Fin 13 => decide (q ∈ T)) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ L))
  let V := fun (F : Circuit) (r : ℕ) (x : List Bool) => (F.wires x).getD r false
  let marks : Finset (Fin 13) := {0, 1, 3, 9}
  have hInc : ∀ p l, p ∈ S l ↔ p-l ∈ marks := by decide
  have qdiff (Q : Finset (Fin 13)) (l : Fin 13) :
      Q ∩ S l = Q.filter (fun p => p-l ∈ marks) := by
    ext p
    simp [hInc]
  have missDiff (Q : Finset (Fin 13)) (l : Fin 13) :
      l ∈ PEqualNP.HeptadCover.missLines S Q ↔ ∀ p ∈ Q, p-l ∉ marks := by
    change l ∈ (Finset.univ.filter fun w => Disjoint (S w) Q) ↔ ∀ p ∈ Q, p-l ∉ marks
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.disjoint_left]
    constructor
    · intro h p hp hi
      exact h (hInc p l |>.mpr hi) hp
    · intro h p hi hp
      exact h p hp (hInc p l |>.mp hi)
  have hLen (P L : Finset (Fin 13)) : (X P L).length = 26 := by simp [X]
  have ha' : a < 26 + D.size := by simpa [hs] using ha
  have hb' : b < 26 + D.size := by simpa [hs] using hb
  have hpos : ∀ p l, p ∈ S l → V D a (X {p} {l}) = true ∨ V D b (X {p} {l}) = true := by
    intro p l hp
    have h := (hval (X {p} {l}) (hLen _ _)).1
    change (V D a (X {p} {l}) || V D b (X {p} {l})) =
      (V C a (X {p} {l}) || V C b (X {p} {l})) at h
    rw [← Bool.or_eq_true,h,Bool.or_eq_true]
    simpa only [X,V,Finset.mem_singleton] using accept p l ((hInc p l).mp hp)
  have hneg : ∀ Q, PEqualNP.HeptadCover.IsQuadrangle S Q →
      V D a (X Q (PEqualNP.HeptadCover.missLines S Q)) = false ∧
      V D b (X Q (PEqualNP.HeptadCover.missLines S Q)) = false := by
    intro Q hq
    have quad : Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p-l ∈ marks)).card ≤ 2 := by
      refine ⟨hq.1,fun l => ?_⟩
      rw [← qdiff]
      exact hq.2 l
    have hReject : V C a (X Q (PEqualNP.HeptadCover.missLines S Q)) = false ∧
        V C b (X Q (PEqualNP.HeptadCover.missLines S Q)) = false := by
      simpa only [V,X,missDiff] using reject Q quad
    have h := (hval (X Q (PEqualNP.HeptadCover.missLines S Q)) (hLen _ _)).1
    change (V D a _ || V D b _) = (V C a _ || V C b _) at h
    rw [hReject.1,hReject.2] at h
    exact Bool.or_eq_false_iff.mp h
  have hleft : ∃ p l, p ∈ S l ∧ V D a (X {p} {l}) = true ∧ V D b (X {p} {l}) = false := by
    obtain ⟨p,l,inc,ha,hb⟩ := leftOnly
    refine ⟨p,l,(hInc p l).mpr inc,?_⟩
    exact (hval (X {p} {l}) (hLen _ _)).2.1
      (by simpa only [X,Finset.mem_singleton] using ha)
      (by simpa only [X,Finset.mem_singleton] using hb)
  have hright : ∃ p l, p ∈ S l ∧ V D b (X {p} {l}) = true ∧ V D a (X {p} {l}) = false := by
    obtain ⟨p,l,inc,hb,ha⟩ := rightOnly
    refine ⟨p,l,(hInc p l).mpr inc,?_⟩
    exact (hval (X {p} {l}) (hLen _ _)).2.2
      (by simpa only [X,Finset.mem_singleton] using hb)
      (by simpa only [X,Finset.mem_singleton] using ha)
  classical
  by_cases h : ∃ p l, p ∈ S l ∧ V D a (X {p} {l}) = true ∧ V D b (X {p} {l}) = true
  · exact overlapping D a b hm hr ha' hb' hsink hpos hneg hleft hright h
  · apply disjoint D a b hm hr ha' hb' hsink hpos hneg hleft hright
    intro p l inc
    cases ea : V D a (X {p} {l})
    · exact Or.inl ea
    · cases eb : V D b (X {p} {l})
      · exact Or.inr eb
      · exact False.elim (h ⟨p,l,inc,ea,eb⟩)
