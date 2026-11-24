import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The first premise is the vertex-cover construction used in R_meta_1973_624.
set_option maxHeartbeats 900000 in
theorem PEqualNP.Outside.R_meta_1971_583
    (coverDrop : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n)) (v : Fin n),
      (∀ w ∉ A, (G.neighborSet w).ncard = 3) →
      (∀ u w, G.Adj u w → u ∉ A) → v ∉ A → v ∈ T →
      (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
      ∃ s, s + 5 ≤ A.card + G.edgeFinset.card + T.card ∧
        HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) s)
    (smaller : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let readers (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u w, G.Adj u w → u ∉ A) → (∃ u w, G.Adj u w) →
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 1 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
        ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, (readers v).length = 1) →
      (∀ T : Finset (Fin n), (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
        C.size + 1 < A.card + G.edgeFinset.card + T.card) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length ≤ (1 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  intro n G A f C degree girth unmarked edge spec fan computes minimal limits few
  classical
  let target := graphFun G A
  let active (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
  let readers (v : Fin n) := C.gates.filter fun g => (active g).contains v.val
  have same : target = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ f x = true
    rw [spec x]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have graphComputes : circuitFun n C = target := computes.trans same.symm
  have result : ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => target (Function.update x v false)) s := by
    by_cases h : ∃ T : Finset (Fin n), (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) ∧
        A.card + G.edgeFinset.card + T.card - 1 ≤ C.size
    · obtain ⟨T, covers, budget⟩ := h
      obtain ⟨a,b,hab⟩ := edge
      have pick : ∃ v ∉ A, v ∈ T := by
        rcases covers a b hab with ha | hb
        · exact ⟨a, unmarked _ _ hab, ha⟩
        · exact ⟨b, unmarked _ _ hab.symm, hb⟩
      obtain ⟨v,hv,hT⟩ := pick
      obtain ⟨s,hs,built⟩ := coverDrop n G A T v degree unmarked hv hT covers
      exact ⟨v,hv,s,by omega,built⟩
    · let step (w : List Bool) (g : Gate) :=
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have readInput (x : Fin n → Bool) (i : Fin n) :
          (List.ofFn x).getD i.val false = x i := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      have preserve (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
          (gs.foldl step w).getD i false = w.getD i false := by
        induction gs generalizing w with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons, ih (step w g)]
          · exact List.getD_append _ _ _ _ hi
          · simp only [step, List.length_append, List.length_singleton]
            omega
      have graphTrue (x : Fin n → Bool) : target x = true ↔
          (∃ a ∈ A, x a = true) ∨ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
        change (decide (∃ a ∈ A, x a = true) ||
          decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) = true ↔ _
        simp only [Bool.or_eq_true, decide_eq_true_eq]
      let lone (v : Fin n) (i : Fin n) := decide (i = v)
      have loneFalse (v : Fin n) (hv : v ∉ A) : target (lone v) ≠ true := by
        intro yes
        rcases (graphTrue _).mp yes with ⟨a,ha,hav⟩ | ⟨a,b,hab,hav,hbv⟩
        · have eq : a = v := of_decide_eq_true hav
          exact hv (eq ▸ ha)
        · have ea : a = v := of_decide_eq_true hav
          have eb : b = v := of_decide_eq_true hbv
          subst a
          subst b
          exact G.loopless.irrefl _ hab
      have used (v : Fin n) (hv : v ∉ A) : 1 ≤ (readers v).length := by
        by_contra! zero
        have noReader (g : Gate) (hg : g ∈ C.gates) : v.val ∉ active g := by
          intro hit
          have member : g ∈ readers v := List.mem_filter.mpr ⟨hg, List.contains_iff_mem.mpr hit⟩
          have positive := List.length_pos_of_mem member
          omega
        have out : C.output ≠ v.val := by
          intro eq
          apply loneFalse v hv
          rw [← graphComputes]
          change (C.gates.foldl step (List.ofFn (lone v))).getD C.output false = true
          rw [eq, preserve _ _ _ (by simp), readInput]
          exact decide_eq_true rfl
        have sameGate (g : Gate) (hg : g ∈ C.gates) (x y : List Bool)
            (agree : ∀ i ≠ v.val, x.getD i false = y.getD i false) :
            g.op.eval (g.inputs.map fun i => x.getD i false) =
              g.op.eval (g.inputs.map fun i => y.getD i false) := by
          have blocked := noReader g hg
          obtain ⟨ops, arity⟩ := fan g hg
          rcases ops with ha | ho | hn
          · change g.op = .and at ha
            have no : v.val ∉ g.inputs := by
              change v.val ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2) at blocked
              rw [ha] at blocked
              change v.val ∉ g.inputs.take 2 at blocked
              simpa only [List.take_of_length_le arity] using blocked
            rw [List.map_congr_left (fun i hi => agree i (fun e => no (e ▸ hi)))]
          · change g.op = .or at ho
            have no : v.val ∉ g.inputs := by
              change v.val ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2) at blocked
              rw [ho] at blocked
              change v.val ∉ g.inputs.take 2 at blocked
              simpa only [List.take_of_length_le arity] using blocked
            rw [List.map_congr_left (fun i hi => agree i (fun e => no (e ▸ hi)))]
          · change g.op = .not at hn
            change v.val ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2) at blocked
            rw [hn] at blocked ⊢
            change v.val ∉ g.inputs.take 1 at blocked
            cases pins : g.inputs with
            | nil => rfl
            | cons i is =>
              have ne : i ≠ v.val := fun e => blocked (by simp [pins, e])
              change (!(x.getD i false)) = (!(y.getD i false))
              rw [agree i ne]
        have foldAgree (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ C.gates)
            (x y : List Bool) (len : x.length = y.length)
            (agree : ∀ i ≠ v.val, x.getD i false = y.getD i false) :
            ∀ i ≠ v.val, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
          induction gs generalizing x y with
          | nil => exact agree
          | cons g gs ih =>
            rw [List.foldl_cons, List.foldl_cons]
            apply ih (fun a ha => sub a (List.mem_cons_of_mem _ ha))
            · simp only [step, List.length_append, List.length_singleton, len]
            · intro i hi
              change (x ++ [_]).getD i false = (y ++ [_]).getD i false
              rw [sameGate g (sub g List.mem_cons_self) x y agree]
              by_cases small : i < x.length
              · rw [List.getD_append _ _ _ _ small, List.getD_append _ _ _ _ (len ▸ small)]
                exact agree i hi
              · rw [List.getD_append_right _ _ _ _ (by omega),
                  List.getD_append_right _ _ _ _ (by omega), len]
        have vDegree : G.degree v = 3 := by
          rw [← G.ncard_neighborSet]
          exact degree v hv
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset v).card from by
          change 0 < G.degree v
          omega)
        have hvw := (G.mem_neighborFinset v w).mp hw
        let x := lone w
        let y := Function.update x v true
        have agree : ∀ i ≠ v.val, (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
          intro i hi
          by_cases small : i < n
          · let u : Fin n := ⟨i,small⟩
            change (List.ofFn x).getD u.val false = (List.ofFn y).getD u.val false
            rw [readInput, readInput]
            have ne : u ≠ v := by
              intro eq
              apply hi
              exact congrArg (fun j : Fin n => j.val) eq
            exact (Function.update_of_ne ne true x).symm
          · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt small),
                List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt small)]
        have eq : circuitFun n C x = circuitFun n C y :=
          foldAgree C.gates (fun _ ha => ha) (List.ofFn x) (List.ofFn y) (by simp) agree C.output out
        rw [graphComputes] at eq
        have yes : target y = true := (graphTrue _).mpr (Or.inr
          ⟨v,w,hvw,Function.update_self v true x,by
            have ne : w ≠ v := hvw.ne.symm
            change Function.update x v true w = true
            rw [Function.update_of_ne ne]
            exact decide_eq_true rfl⟩)
        exact loneFalse w (unmarked _ _ hvw.symm) (eq.trans yes)
      have upgraded (v : Fin n) (hv : v ∉ A) : 1 ≤ (readers v).length ∧
          (readers v).length ≤ 3 ∧ ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or) :=
        ⟨used v hv, limits v hv⟩
      obtain ⟨v,hv,hle⟩ := few
      have hle' : (readers v).length ≤ 1 := hle
      have one : (readers v).length = 1 := Nat.le_antisymm hle' (used v hv)
      have targetMinimal (s : ℕ) (hs : HasCircuitSize n target s) : C.size ≤ s :=
        minimal s (same ▸ hs)
      refine smaller n G A C degree girth unmarked edge fan graphComputes targetMinimal
        upgraded ⟨v,hv,one⟩ ?_
      intro T cov
      have bound : ¬ (A.card + G.edgeFinset.card + T.card - 1 ≤ C.size) :=
        fun hT => h ⟨T,cov,hT⟩
      omega
  rwa [same] at result
