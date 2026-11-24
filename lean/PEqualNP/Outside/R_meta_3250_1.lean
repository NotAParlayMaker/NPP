import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3250_1
    (cofactor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (marked : let f (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ (A B : Circuit) (k : ℕ), FanInTwo A → FanInTwo B → A.size + B.size ≤ 13 →
      let w (b : Bool) (x : Fin 8 → Bool) := A.wires (List.ofFn x ++ [x 1 || b])
      (∀ x, B.eval (w false x ++ [(w false x).getD k false]) = f x) →
      ∃ x, B.eval (w true x ++ [true]) ≠ (f x || x 0 || x 3)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) (x6 : Bool),   x2 ≠ (0 : Fin (9 : ℕ)) →     x2 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < x4 →               x4 ≤ (10 : ℕ) + x3.size →                 (∀ x14 ∈ List.take (x4 - (10 : ℕ)) x3.gates, ↑x2 ∉ x14.inputs) →                   (∀ (x15 : Fin (9 : ℕ) → Bool),                       have x16 : Fin (9 : ℕ) → Bool := Function.update x15 x2 Bool.false;                       x1 x16 ≠ x1 (Function.update x15 x2 Bool.true) → (x3.wires (List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))])).getD x5 Bool.false = !x6) →                     ∃ (x16 : Fin (9 : ℕ) → Bool),                       have x17 : List Bool := List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))];                       have x18 : Bool := (x3.wires x17).getD x5 Bool.false;                       x3.eval (x17.set (↑x2) (if x6 = Bool.true then x16 x2 || x18 else x16 x2 && x18)) ≠ x1 x16 := by
  dsimp only
  classical
  intro v C cut idx disj hv0 hv6 hfanC hszC hidx10 hidxlt hcutle hprior _hsens
  by_contra! hcorr
  let F : (Fin 9 → Bool) → Bool := fun x =>
    [((0 : Fin 9), (1 : Fin 9)), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
     (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)].any fun e => x e.1 && x e.2
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have evalAnd0 : GateOp.and.eval [] = true := rfl
  have evalAnd1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl
  have evalAnd2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by cases a <;> cases b <;> rfl
  have evalOr0 : GateOp.or.eval [] = false := rfl
  have evalOr1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl
  have evalOr2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by cases a <;> cases b <;> rfl
  have evalNot0 : GateOp.not.eval [] = true := rfl
  have evalNot1 (a : Bool) (l : List Bool) : GateOp.not.eval (a :: l) = !a := rfl
  have foldLen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have foldKeep : ∀ (gs : List Gate) (w : List Bool) (j : ℕ), j < w.length →
      (gs.foldl step w).getD j false = w.getD j false := by
    intro gs
    induction gs with
    | nil => intro w j _; rfl
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj
  have foldSetComm : ∀ (k : ℕ) (b : Bool) (gs : List Gate) (w : List Bool),
      (∀ g ∈ gs, k ∉ g.inputs) → k < w.length →
      gs.foldl step (w.set k b) = (gs.foldl step w).set k b := by
    intro k b gs
    induction gs with
    | nil => intro w _ _; rfl
    | cons g gs ih =>
      intro w hno hk
      have hgk : k ∉ g.inputs := hno g List.mem_cons_self
      have hmap : g.inputs.map (fun j => (w.set k b).getD j false) =
          g.inputs.map (fun j => w.getD j false) := by
        apply List.map_congr_left
        intro j hj
        have hjk : j ≠ k := fun h => hgk (h ▸ hj)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjk)]
      rw [List.foldl_cons, List.foldl_cons]
      have hstep : step (w.set k b) g = (step w g).set k b := by
        unfold step
        rw [hmap, List.set_append_left _ _ (by simpa using hk)]
      rw [hstep]
      exact ih _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [step]; omega)
  let pre := C.gates.take (cut - 10)
  let post := C.gates.drop (cut - 10)
  have hprelen : pre.length = cut - 10 := by
    have : cut - 10 ≤ C.gates.length := by change cut ≤ 10 + C.gates.length at hcutle; omega
    simp [pre, Nat.min_eq_left this]
  let gnew : Gate := ⟨if disj then GateOp.or else GateOp.and, [v.val, idx]⟩
  let rmap : ℕ → ℕ := fun w => if w = v.val then cut else if w < cut then w else w + 1
  let mapGate : (ℕ → ℕ) → Gate → Gate := fun σ g => ⟨g.op, g.inputs.map σ⟩
  let D0 : Circuit := ⟨pre ++ [gnew] ++ post.map (mapGate rmap), rmap C.output⟩
  have hfanD0 : FanInTwo D0 := by
    intro g hg
    change g ∈ pre ++ [gnew] ++ post.map (mapGate rmap) at hg
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hg
    rcases hg with (h1 | rfl) | ⟨g', hg', rfl⟩
    · exact hfanC g (List.mem_of_mem_take h1)
    · cases disj <;> simp [gnew]
    · have h := hfanC g' (List.mem_of_mem_drop hg')
      exact ⟨h.1, by simpa [mapGate] using h.2⟩
  have hszD0 : D0.size ≤ 14 := by
    change (pre ++ [gnew] ++ post.map (mapGate rmap)).length ≤ 14
    simp only [List.length_append, List.length_singleton, List.length_map]
    have hsp : pre.length + post.length = C.gates.length := by
      rw [← List.length_append, List.take_append_drop]
    change C.gates.length ≤ 13 at hszC
    omega
  have hrmapRel : ∀ (gs : List Gate) (a b : List Bool),
      cut ≤ a.length → b.length = a.length + 1 →
      (∀ u, b.getD (rmap u) false = a.getD u false) →
      ∀ u, ((gs.map (mapGate rmap)).foldl step b).getD (rmap u) false =
        (gs.foldl step a).getD u false := by
    intro gs
    induction gs with
    | nil => intro a b _ _ h u; exact h u
    | cons g gs ih =>
      intro a b hca hba h
      have hvals : (mapGate rmap g).inputs.map (fun j => b.getD j false) =
          g.inputs.map (fun j => a.getD j false) := by
        simp only [mapGate, List.map_map, Function.comp_def, h]
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      apply ih (step a g) (step b (mapGate rmap g)) (by simp [step]; omega) (by simp [step, hba])
      intro u
      have hvlt : v.val < 9 := v.isLt
      by_cases hu : u < a.length
      · have hru : rmap u < b.length := by
          unfold rmap
          split_ifs <;> omega
        unfold step
        rw [List.getD_append _ _ _ _ hru, List.getD_append _ _ _ _ hu]
        exact h u
      · by_cases hueq : u = a.length
        · subst u
          have hru : rmap a.length = b.length := by
            unfold rmap
            rw [if_neg (by omega), if_neg (by omega)]
            omega
          unfold step
          rw [hru, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
            List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          change g.op.eval ((mapGate rmap g).inputs.map fun j => b.getD j false) = _
          rw [hvals]
        · have hru : b.length + 1 ≤ rmap u := by
            unfold rmap
            rw [if_neg (by omega), if_neg (by omega)]
            omega
          rw [List.getD_eq_default _ _ (by simp [step]; omega),
            List.getD_eq_default _ _ (by simp [step]; omega)]
  have hD0eval : ∀ x : Fin 9 → Bool, D0.eval (List.ofFn x ++ [x 0 || x 6]) = F x := by
    intro x
    let xs := List.ofFn x ++ [x 0 || x 6]
    have hxslen : xs.length = 10 := by simp [xs]
    let w1 := pre.foldl step xs
    have hw1len : w1.length = cut := by
      change (pre.foldl step xs).length = cut
      rw [foldLen, hxslen, hprelen]
      omega
    have hbv : w1.getD idx false = (C.wires xs).getD idx false := by
      have hsp : pre ++ post = C.gates := List.take_append_drop _ _
      change w1.getD idx false = (C.gates.foldl step xs).getD idx false
      rw [← hsp, List.foldl_append]
      exact (foldKeep post w1 idx (by omega)).symm
    have hvv : w1.getD v.val false = x v := by
      have hvlt : v.val < 9 := v.isLt
      rw [foldKeep pre xs v.val (by omega)]
      simp only [xs]
      rw [List.getD_append _ _ _ _ (by simpa using hvlt),
        List.getD_eq_getElem _ _ (by simpa using hvlt), List.getElem_ofFn]
    let val : Bool := if disj then x v || (C.wires xs).getD idx false else x v && (C.wires xs).getD idx false
    have hgnewVal : gnew.op.eval (gnew.inputs.map fun j => w1.getD j false) = val := by
      cases disj
      · change GateOp.and.eval [w1.getD v.val false, w1.getD idx false] = (x v && (C.wires xs).getD idx false)
        rw [evalAnd2, hvv, hbv]
      · change GateOp.or.eval [w1.getD v.val false, w1.getD idx false] = (x v || (C.wires xs).getD idx false)
        rw [evalOr2, hvv, hbv]
    let w2 := w1 ++ [val]
    let w1' := pre.foldl step (xs.set v.val val)
    have hw1'eq : w1' = w1.set v.val val := foldSetComm v.val val pre xs hprior (by have := v.isLt; omega)
    have hw1'len : w1'.length = cut := by rw [hw1'eq, List.length_set, hw1len]
    have hmatch : ∀ u, w2.getD (rmap u) false = w1'.getD u false := by
      intro u
      have hvlt : v.val < 9 := v.isLt
      rw [hw1'eq]
      by_cases huv : u = v.val
      · subst u
        simp only [rmap, ite_true, w2]
        rw [← hw1len, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_self (show v.val < w1.length by omega)]
      · by_cases huc : u < cut
        · simp only [rmap, huv, ite_false, huc, ite_true, w2]
          rw [List.getD_append _ _ _ _ (by omega)]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm huv)]
        · simp only [rmap, huv, ite_false, huc, w2]
          rw [List.getD_eq_default _ _ (by simp [hw1len]; omega),
            List.getD_eq_default _ _ (by simp [hw1len]; omega)]
    have hD0w : D0.eval xs = ((post.map (mapGate rmap)).foldl step w2).getD (rmap C.output) false := by
      change ((pre ++ [gnew] ++ post.map (mapGate rmap)).foldl step xs).getD (rmap C.output) false = _
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((post.map (mapGate rmap)).foldl step (w1 ++ [gnew.op.eval (gnew.inputs.map fun j => w1.getD j false)])).getD _ _ = _
      rw [hgnewVal]
    have hCw : C.eval (xs.set v.val val) = (post.foldl step w1').getD C.output false := by
      have hsp : pre ++ post = C.gates := List.take_append_drop _ _
      change (C.gates.foldl step (xs.set v.val val)).getD C.output false = _
      rw [← hsp, List.foldl_append]
    rw [hD0w, hrmapRel post w1' w2 (by omega) (by simp [w2, hw1len, hw1'len]) hmatch C.output, ← hCw]
    exact hcorr x
  let norm : Gate → Gate := fun g => ⟨g.op, if g.op = GateOp.not then g.inputs.take 1 else g.inputs⟩
  let D : Circuit := ⟨D0.gates.map norm, D0.output⟩
  have hfanD : FanInTwo D := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have h := hfanD0 g' hg'
    refine ⟨h.1, ?_⟩
    by_cases hn : g'.op = GateOp.not <;> simp [norm, hn, h.2]
  have hnotLen : ∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
    intro g hg hn
    obtain ⟨g', _, rfl⟩ := List.mem_map.mp hg
    change g'.op = GateOp.not at hn
    simp [norm, hn]
  have hszD : D.size ≤ 14 := by
    change (D0.gates.map norm).length ≤ 14
    rw [List.length_map]
    exact hszD0
  have hnormStep : ∀ (g : Gate) (w : List Bool), step w (norm g) = step w g := by
    intro g w
    by_cases hn : g.op = GateOp.not
    · cases hgi : g.inputs with
      | nil => simp [step, norm, hn, hgi]
      | cons a l =>
        simp only [step, norm, hn, ite_true, hgi, List.take_succ_cons, List.take_zero, List.map_cons,
          List.map_nil]
        rw [evalNot1, evalNot1]
    · simp [step, norm, hn]
  have hnormFold : ∀ (gs : List Gate) (w : List Bool),
      (gs.map norm).foldl step w = gs.foldl step w := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih => intro w; rw [List.map_cons, List.foldl_cons, List.foldl_cons, hnormStep, ih]
  have hDeval : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 6]) = F x := by
    intro x
    change ((D0.gates.map norm).foldl step _).getD D0.output false = F x
    rw [hnormFold]
    exact hD0eval x
  let f : (Fin 8 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
    (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let g : (Fin 8 → Bool) → Bool := fun x => f x || x 0 || x 3
  let lift : Bool → (Fin 8 → Bool) → (Fin 9 → Bool) := fun b x =>
    ![x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3]
  let inp : Bool → (Fin 8 → Bool) → List Bool := fun b x =>
    [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
  have hinpEq : ∀ b x, List.ofFn (lift b x) ++ [lift b x 0 || lift b x 6] = inp b x := fun _ _ => rfl
  have hFtruth : ∀ b x, F (lift b x) = if b then g x else f x := by
    intro b x
    have htab : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
        F (lift b ![b0, b1, b2, b3, b4, b5, b6, b7]) =
          if b then g ![b0, b1, b2, b3, b4, b5, b6, b7] else f ![b0, b1, b2, b3, b4, b5, b6, b7] := by
      cases b <;> decide
    have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      funext i; fin_cases i <;> rfl
    rw [hx]; exact htab _ _ _ _ _ _ _ _
  have hDfg : ∀ b x, D.eval (inp b x) = if b then g x else f x := by
    intro b x
    rw [← hinpEq b x, hDeval (lift b x), hFtruth b x]
  let simpG : GateOp → ℕ → List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ := fun op m ins =>
    GateOp.casesOn op
      (List.casesOn ins (none, Sum.inl true) fun a t1 =>
        List.casesOn t1 (none, a) fun b t2 =>
          List.casesOn t2
            (Sum.casesOn a
              (fun ca => Bool.casesOn ca (none, Sum.inl false) (none, b))
              (fun ia => Sum.casesOn b
                (fun cb => Bool.casesOn cb (none, Sum.inl false) (none, Sum.inr ia))
                (fun ib => (some ⟨GateOp.and, [ia, ib]⟩, Sum.inr m))))
            (fun _ _ => (none, Sum.inl false)))
      (List.casesOn ins (none, Sum.inl false) fun a t1 =>
        List.casesOn t1 (none, a) fun b t2 =>
          List.casesOn t2
            (Sum.casesOn a
              (fun ca => Bool.casesOn ca (none, b) (none, Sum.inl true))
              (fun ia => Sum.casesOn b
                (fun cb => Bool.casesOn cb (none, Sum.inr ia) (none, Sum.inl true))
                (fun ib => (some ⟨GateOp.or, [ia, ib]⟩, Sum.inr m))))
            (fun _ _ => (none, Sum.inl false)))
      (List.casesOn ins (none, Sum.inl true) fun a _ =>
        Sum.casesOn a
          (fun ca => (none, Sum.inl (!ca)))
          (fun ia => (some ⟨GateOp.not, [ia]⟩, Sum.inr m)))
      (fun _ => (none, Sum.inl false))
      (none, Sum.inl false)
  let sVal : List Bool → Sum Bool ℕ → Bool := fun w s =>
    Sum.casesOn s (fun c => c) (fun j => w.getD j false)
  let sValid : ℕ → Sum Bool ℕ → Prop := fun m s =>
    Sum.casesOn s (fun _ => True) (fun j => j < m)
  let elimStep : List (Sum Bool ℕ) × List Gate → Gate → List (Sum Bool ℕ) × List Gate :=
    fun acc g =>
      let r := simpG g.op (8 + acc.2.length) (g.inputs.map fun j => acc.1.getD j (Sum.inl false))
      (acc.1 ++ [r.2], acc.2 ++ r.1.toList)
  have hSimpOk : ∀ op m ins g', g' ∈ (simpG op m ins).1.toList →
      g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
    intro op m ins g' hg'
    cases op with
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · simp [simpG] at hg'
      · simp [simpG] at hg'
      · cases a with
        | inl x => cases x <;> (cases b with | inl y => cases y <;> simp [simpG] at hg' | inr j => simp [simpG] at hg')
        | inr i => cases b with | inl y => cases y <;> simp [simpG] at hg' | inr j => simp [simpG] at hg'; subst hg'; simp
      · simp [simpG] at hg'
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · simp [simpG] at hg'
      · simp [simpG] at hg'
      · cases a with
        | inl x => cases x <;> (cases b with | inl y => cases y <;> simp [simpG] at hg' | inr j => simp [simpG] at hg')
        | inr i => cases b with | inl y => cases y <;> simp [simpG] at hg' | inr j => simp [simpG] at hg'; subst hg'; simp
      · simp [simpG] at hg'
    | not =>
      rcases ins with _ | ⟨a, l⟩
      · simp [simpG] at hg'
      · cases a with
        | inl x => simp [simpG] at hg'
        | inr i => simp [simpG] at hg'; subst hg'; simp
    | mod _ => simp [simpG] at hg'
    | maj => simp [simpG] at hg'
  have hSimpSound : ∀ (op : GateOp) (w : List Bool) (ins : List (Sum Bool ℕ)),
      op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → ins.length ≤ 2 →
      (∀ s ∈ ins, sValid w.length s) →
      sValid (w.length + (simpG op w.length ins).1.toList.length) (simpG op w.length ins).2 ∧
      sVal ((simpG op w.length ins).1.toList.foldl step w) (simpG op w.length ins).2 =
        op.eval (ins.map (sVal w)) := by
    intro op w ins hop hlen hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · have ha := hv a List.mem_cons_self
        cases a with
        | inl c => exact ⟨trivial, (evalAnd1 c).symm⟩
        | inr j => exact ⟨by simpa [simpG, sValid] using ha, (evalAnd1 _).symm⟩
      · have ha := hv a List.mem_cons_self
        have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
        cases a with
        | inl c =>
          cases c with
          | false => exact ⟨trivial, by simp [simpG, sVal, evalAnd2]⟩
          | true =>
            cases b with
            | inl d => cases d <;> exact ⟨trivial, by simp [simpG, sVal, evalAnd2]⟩
            | inr j => exact ⟨by simpa [simpG, sValid] using hb, by simp [simpG, sVal, evalAnd2]⟩
        | inr i =>
          cases b with
          | inl d =>
            cases d with
            | false => exact ⟨trivial, by simp [simpG, sVal, evalAnd2]⟩
            | true => exact ⟨by simpa [simpG, sValid] using ha, by simp [simpG, sVal, evalAnd2]⟩
          | inr j =>
            refine ⟨by simp [simpG, sValid], ?_⟩
            simp only [simpG, Option.toList_some, List.foldl_cons, List.foldl_nil, step, sVal,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
              List.map_cons, List.map_nil, evalAnd2]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · have ha := hv a List.mem_cons_self
        cases a with
        | inl c => exact ⟨trivial, (evalOr1 c).symm⟩
        | inr j => exact ⟨by simpa [simpG, sValid] using ha, (evalOr1 _).symm⟩
      · have ha := hv a List.mem_cons_self
        have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
        cases a with
        | inl c =>
          cases c with
          | false =>
            cases b with
            | inl d => cases d <;> exact ⟨trivial, by simp [simpG, sVal, evalOr2]⟩
            | inr j => exact ⟨by simpa [simpG, sValid] using hb, by simp [simpG, sVal, evalOr2]⟩
          | true => exact ⟨trivial, by simp [simpG, sVal, evalOr2]⟩
        | inr i =>
          cases b with
          | inl d =>
            cases d with
            | false => exact ⟨by simpa [simpG, sValid] using ha, by simp [simpG, sVal, evalOr2]⟩
            | true => exact ⟨trivial, by simp [simpG, sVal, evalOr2]⟩
          | inr j =>
            refine ⟨by simp [simpG, sValid], ?_⟩
            simp only [simpG, Option.toList_some, List.foldl_cons, List.foldl_nil, step, sVal,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
              List.map_cons, List.map_nil, evalOr2]
      · simp at hlen
    · rcases ins with _ | ⟨a, l⟩
      · exact ⟨trivial, rfl⟩
      · cases a with
        | inl c => exact ⟨trivial, by simp [simpG, sVal, evalNot1]⟩
        | inr j =>
          refine ⟨by simp [simpG, sValid], ?_⟩
          simp only [simpG, Option.toList_some, List.foldl_cons, List.foldl_nil, step, sVal,
            List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
            List.map_cons, List.map_nil, evalNot1]
  have hSimpDropConst : ∀ (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) (c : Bool),
      (op = GateOp.not → ins.length ≤ 1) → Sum.inl c ∈ ins → (simpG op m ins).1 = none := by
    intro op m ins c hn hmem
    cases op with
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp at hmem
      · rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · cases c <;> (cases b with | inl y => cases y <;> rfl | inr j => rfl)
        · cases c <;> (cases a with | inl y => cases y <;> rfl | inr i => rfl)
      · rfl
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp at hmem
      · rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · cases c <;> (cases b with | inl y => cases y <;> rfl | inr j => rfl)
        · cases c <;> (cases a with | inl y => cases y <;> rfl | inr i => rfl)
      · rfl
    | not =>
      have h1 := hn rfl
      rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
      · simp at hmem
      · simp only [List.mem_singleton] at hmem; subst a; rfl
      · simp at h1
    | mod _ => rfl
    | maj => rfl
  let Inv : (Fin 8 → Bool) → List Bool → List (Sum Bool ℕ) × List Gate → Prop := fun x w acc =>
    acc.1.length = w.length ∧
    ∀ j, sValid (8 + acc.2.length) (acc.1.getD j (Sum.inl false)) ∧
      sVal (acc.2.foldl step (List.ofFn x)) (acc.1.getD j (Sum.inl false)) = w.getD j false
  have hElimInv : ∀ (x : Fin 8 → Bool) (gs : List Gate) (w : List Bool)
      (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      Inv x w acc → Inv x (gs.foldl step w) (gs.foldl elimStep acc) := by
    intro x gs
    induction gs with
    | nil => intro w acc _ h; exact h
    | cons g gs ih =>
      intro w acc hok hinv
      rw [List.foldl_cons, List.foldl_cons]
      apply ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      obtain ⟨hlen, hget⟩ := hinv
      have hg := hok g List.mem_cons_self
      let w' := acc.2.foldl step (List.ofFn x)
      have hw'len : w'.length = 8 + acc.2.length := by
        change (acc.2.foldl step (List.ofFn x)).length = _
        rw [foldLen, List.length_ofFn]
      let ins := g.inputs.map fun j => acc.1.getD j (Sum.inl false)
      have hss := hSimpSound g.op w' ins hg.1 (by simpa [ins] using hg.2) (by
        intro s hs
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
        rw [hw'len]; exact (hget j).1)
      rw [hw'len] at hss
      let r := simpG g.op (8 + acc.2.length) ins
      have hvals : ins.map (sVal w') = g.inputs.map fun j => w.getD j false := by
        rw [List.map_map]
        exact List.map_congr_left fun j _ => (hget j).2
      refine ⟨by simp [elimStep, step, hlen], ?_⟩
      intro j
      change sValid (8 + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD j (Sum.inl false)) ∧
        sVal ((acc.2 ++ r.1.toList).foldl step (List.ofFn x)) ((acc.1 ++ [r.2]).getD j (Sum.inl false)) =
          (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).getD j false
      rw [List.foldl_append, List.length_append, ← Nat.add_assoc]
      by_cases hj : j < acc.1.length
      · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (by omega)]
        have hv0 := (hget j).1
        have heq0 := (hget j).2
        cases hs : acc.1.getD j (Sum.inl false) with
        | inl c =>
          rw [hs] at hv0 heq0
          exact ⟨trivial, heq0⟩
        | inr q =>
          rw [hs] at hv0 heq0
          simp only [sValid, sVal] at hv0 heq0 ⊢
          refine ⟨by omega, ?_⟩
          rw [foldKeep r.1.toList w' q (by omega)]
          exact heq0
      · by_cases hje : j = acc.1.length
        · subst j
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
            hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact ⟨hss.1, by rw [hss.2, hvals]⟩
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          exact ⟨trivial, rfl⟩
  have hElimFan : ∀ (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ acc.2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ g ∈ (gs.foldl elimStep acc).2,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    intro gs
    induction gs with
    | nil => intro acc h; exact h
    | cons g gs ih =>
      intro acc h
      rw [List.foldl_cons]
      apply ih
      intro g' hg'
      rcases List.mem_append.mp hg' with h1 | h1
      · exact h g' h1
      · exact hSimpOk _ _ _ g' h1
  have hElimKeep : ∀ (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) (j : ℕ),
      j < acc.1.length → (gs.foldl elimStep acc).1.getD j (Sum.inl false) = acc.1.getD j (Sum.inl false) := by
    intro gs
    induction gs with
    | nil => intro acc j _; rfl
    | cons g gs ih =>
      intro acc j hj
      rw [List.foldl_cons, ih _ _ (by simp [elimStep]; omega)]
      exact List.getD_append _ _ _ _ hj
  have hElimLenLe : ∀ (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate),
      (gs.foldl elimStep acc).2.length ≤ acc.2.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro acc; simp
    | cons g gs ih =>
      intro acc
      rw [List.foldl_cons]
      have h1 := ih (elimStep acc g)
      have h2 : (simpG g.op (8 + acc.2.length) (g.inputs.map fun j => acc.1.getD j (Sum.inl false))).1.toList.length ≤ 1 := by
        cases (simpG g.op (8 + acc.2.length) (g.inputs.map fun j => acc.1.getD j (Sum.inl false))).1 <;> simp
      simp only [elimStep, List.length_append, List.length_cons] at h1 ⊢
      omega
  have hElimDropCount : ∀ (k : ℕ) (c : Bool) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate),
      k < acc.1.length → acc.1.getD k (Sum.inl false) = Sum.inl c →
      (∀ g ∈ gs, g.op = GateOp.not → g.inputs.length ≤ 1) →
      (gs.foldl elimStep acc).2.length + gs.countP (fun g => g.inputs.contains k) ≤
        acc.2.length + gs.length := by
    intro k c gs
    induction gs with
    | nil => intro acc _ _ _; simp
    | cons g gs ih =>
      intro acc hk hkc hnot
      rw [List.foldl_cons]
      have htail := ih (elimStep acc g) (by simp [elimStep]; omega)
        (by rw [List.getD_append _ _ _ _ hk]; exact hkc)
        (fun g' hg' => hnot g' (List.mem_cons_of_mem _ hg'))
      simp only [List.countP_cons, List.length_cons]
      by_cases hmem : g.inputs.contains k = true
      · have hkin : k ∈ g.inputs := List.contains_iff_mem.mp hmem
        have hin : Sum.inl c ∈ g.inputs.map (fun j => acc.1.getD j (Sum.inl false)) :=
          List.mem_map.mpr ⟨k, hkin, hkc⟩
        have hnone := hSimpDropConst g.op (8 + acc.2.length) _ c (fun h => by simpa using hnot g List.mem_cons_self h) hin
        have hstepLen : (elimStep acc g).2.length = acc.2.length := by
          simp only [elimStep, hnone, Option.toList_none, List.append_nil]
        rw [hstepLen] at htail
        simp only [hmem, ite_true]
        omega
      · have hstepLen : (elimStep acc g).2.length ≤ acc.2.length + 1 := by
          have h2 : (simpG g.op (8 + acc.2.length) (g.inputs.map fun j => acc.1.getD j (Sum.inl false))).1.toList.length ≤ 1 := by
            cases (simpG g.op (8 + acc.2.length) (g.inputs.map fun j => acc.1.getD j (Sum.inl false))).1 <;> simp
          simp only [elimStep, List.length_append]
          omega
        have hmf : g.inputs.contains k = false := Bool.eq_false_iff.mpr hmem
        simp only [hmf, Bool.false_eq_true, ite_false]
        omega
  let M0 : List (Sum Bool ℕ) :=
    [Sum.inr 1, Sum.inr 0, Sum.inr 4, Sum.inr 7, Sum.inr 5, Sum.inr 2,
     Sum.inl false, Sum.inr 6, Sum.inr 3, Sum.inr 1]
  have hInv0 : ∀ x : Fin 8 → Bool, Inv x (inp false x) (M0, []) := by
    intro x
    refine ⟨rfl, ?_⟩
    intro j
    by_cases hj : j < 10
    · interval_cases j <;> simp [M0, inp, sValid, sVal, List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default M0 _ (by simp [M0]; omega),
        List.getD_eq_default (inp false x) _ (by simp [inp]; omega)]
      exact ⟨trivial, rfl⟩
  have hNoSize12 : ∀ acc : List (Sum Bool ℕ) × List Gate,
      acc = D.gates.foldl elimStep (M0, []) → acc.2.length ≤ 12 → False := by
    intro acc hacc hle
    have hfanAcc : FanInTwo ⟨acc.2, 0⟩ := by
      rw [hacc]
      exact hElimFan D.gates (M0, []) (by simp)
    cases ho : acc.1.getD D.output (Sum.inl false) with
    | inl c =>
      have h0 := ((hElimInv (fun _ => false) D.gates (inp false (fun _ => false)) (M0, []) hfanD (hInv0 _)).2 D.output).2
      have h1 := ((hElimInv (fun _ => true) D.gates (inp false (fun _ => true)) (M0, []) hfanD (hInv0 _)).2 D.output).2
      rw [← hacc, ho] at h0 h1
      change c = D.eval (inp false (fun _ => false)) at h0
      change c = D.eval (inp false (fun _ => true)) at h1
      rw [hDfg false (fun _ => false)] at h0
      rw [hDfg false (fun _ => true)] at h1
      simp only [Bool.false_eq_true, ite_false] at h0 h1
      have hf0 : f (fun _ => false) = false := by decide
      have hf1 : f (fun _ => true) = true := by decide
      rw [hf0] at h0; rw [hf1] at h1
      exact Bool.false_ne_true (h0.symm.trans h1)
    | inr out' =>
      apply cofactor
      refine ⟨⟨acc.2, out'⟩, hfanAcc, hle, ?_⟩
      intro x
      have hx := ((hElimInv x D.gates (inp false x) (M0, []) hfanD (hInv0 x)).2 D.output).2
      rw [← hacc, ho] at hx
      change (⟨acc.2, out'⟩ : Circuit).eval (List.ofFn x) = D.eval (inp false x) at hx
      rw [hDfg false] at hx
      exact hx
  let cnt6 := D.gates.countP (fun g => g.inputs.contains 6)
  have hDiff6 : ∀ x : Fin 8 → Bool, x 1 = true → inp false x = (inp true x).set 6 false := by
    intro x hx1
    simp [inp, hx1]
  have hWitness : ∃ x : Fin 8 → Bool, x 1 = true ∧ f x = false ∧ g x = true :=
    ⟨![false, true, false, true, false, false, false, false], by decide +kernel⟩
  by_cases hcnt0 : cnt6 = 0
  · have hno6 : ∀ g' ∈ D.gates, 6 ∉ g'.inputs := by
      intro g' hg' hmem
      have hpos : 0 < cnt6 := List.countP_pos_iff.mpr ⟨g', hg', List.contains_iff_mem.mpr hmem⟩
      omega
    obtain ⟨xw, hxw1, hfw, hgw⟩ := hWitness
    by_cases hout6 : D.output = 6
    · have h1 := hDfg false (fun _ => true)
      change (D.gates.foldl step (inp false (fun _ => true))).getD D.output false = f (fun _ => true) at h1
      rw [hout6, foldKeep _ _ 6 (by simp [inp])] at h1
      have hf1 : f (fun _ => true) = true := by decide
      rw [hf1] at h1
      exact Bool.false_ne_true h1
    · have heq := foldSetComm 6 false D.gates (inp true xw) hno6 (by simp [inp])
      rw [← hDiff6 xw hxw1] at heq
      have hout : D.eval (inp false xw) = D.eval (inp true xw) := by
        change (D.gates.foldl step (inp false xw)).getD D.output false =
          (D.gates.foldl step (inp true xw)).getD D.output false
        rw [heq]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hout6)]
      rw [hDfg false, hDfg true] at hout
      simp only [Bool.false_eq_true, ite_false, ite_true, hfw, hgw] at hout
  by_cases hcnt2 : 2 ≤ cnt6
  · have hdrop := hElimDropCount 6 false D.gates (M0, []) (by simp [M0]) rfl hnotLen
    apply hNoSize12 (D.gates.foldl elimStep (M0, [])) rfl
    change _ + cnt6 ≤ 0 + D.gates.length at hdrop
    change D.gates.length ≤ 14 at hszD
    omega
  have hcnt1 : cnt6 = 1 := by omega
  have hsplit1 : ∀ (gs : List Gate), gs.countP (fun g => g.inputs.contains 6) = 1 →
      ∃ (a b : List Gate) (h : Gate), gs = a ++ [h] ++ b ∧
        (∀ g' ∈ a, 6 ∉ g'.inputs) ∧ (6 ∈ h.inputs) ∧ (∀ g' ∈ b, 6 ∉ g'.inputs) := by
    intro gs
    induction gs with
    | nil => intro hc; simp at hc
    | cons x xs ih =>
      intro hc
      simp only [List.countP_cons] at hc
      by_cases hx : x.inputs.contains 6 = true
      · simp only [hx, ite_true] at hc
        have hzero : xs.countP (fun g => g.inputs.contains 6) = 0 := by omega
        refine ⟨[], xs, x, rfl, by simp, List.contains_iff_mem.mp hx, ?_⟩
        intro g' hg' hmem
        have : 0 < xs.countP (fun g => g.inputs.contains 6) :=
          List.countP_pos_iff.mpr ⟨g', hg', List.contains_iff_mem.mpr hmem⟩
        omega
      · simp only [hx, ite_false] at hc
        obtain ⟨a, b, h, heq, ha, hh, hb⟩ := ih hc
        refine ⟨x :: a, b, h, by rw [heq]; rfl, ?_, hh, hb⟩
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · intro hmem; exact hx (List.contains_iff_mem.mpr hmem)
        · exact ha g' hg'
  obtain ⟨gsA, gsB, hgate, hDsplit, hnoA, h6in, hnoB⟩ := hsplit1 D.gates hcnt1
  have hfanA : ∀ g' ∈ gsA, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => hfanD g' (by rw [hDsplit]; simp [hg'])
  have hfanB : ∀ g' ∈ gsB, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => hfanD g' (by rw [hDsplit]; simp [hg'])
  have hfanH := hfanD hgate (by rw [hDsplit]; simp)
  have hnotB : ∀ g' ∈ gsB, g'.op = GateOp.not → g'.inputs.length ≤ 1 :=
    fun g' hg' => hnotLen g' (by rw [hDsplit]; simp [hg'])
  have hnotH : hgate.op = GateOp.not → hgate.inputs.length ≤ 1 :=
    hnotLen hgate (by rw [hDsplit]; simp)
  let accA := gsA.foldl elimStep (M0, [])
  let accH := elimStep accA hgate
  have hAccALen : accA.1.length = 10 + gsA.length := by
    have h1 := (hElimInv (fun _ => false) gsA (inp false (fun _ => false)) (M0, []) hfanA (hInv0 _)).1
    rw [foldLen] at h1
    simpa [inp] using h1
  have hHDrop : accH.2.length = accA.2.length := by
    have h6val : accA.1.getD 6 (Sum.inl false) = Sum.inl false :=
      hElimKeep gsA (M0, []) 6 (by simp [M0])
    have hin : Sum.inl false ∈ hgate.inputs.map (fun j => accA.1.getD j (Sum.inl false)) :=
      List.mem_map.mpr ⟨6, h6in, h6val⟩
    have hnone := hSimpDropConst hgate.op (8 + accA.2.length) _ false (fun h => by simpa using hnotH h) hin
    simp only [accH, elimStep, hnone, Option.toList_none, List.append_nil]
  have hAccALenLe : accA.2.length ≤ gsA.length := by
    have := hElimLenLe gsA (M0, [])
    simpa using this
  let hwire := 10 + gsA.length
  cases hr2 : accH.1.getD hwire (Sum.inl false) with
  | inl c =>
    by_cases hused : 1 ≤ gsB.countP (fun g => g.inputs.contains hwire)
    · have hdropB := hElimDropCount hwire c gsB accH
        (by simp [accH, elimStep, hAccALen, hwire]) hr2 hnotB
      apply hNoSize12 (D.gates.foldl elimStep (M0, [])) rfl
      have hfoldEq : D.gates.foldl elimStep (M0, []) = gsB.foldl elimStep accH := by
        rw [hDsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hfoldEq]
      have hlenD : gsA.length + 1 + gsB.length ≤ 14 := by
        change D.gates.length ≤ 14 at hszD
        rw [hDsplit] at hszD
        simp only [List.length_append, List.length_singleton] at hszD
        omega
      omega
    · have hnoH : ∀ g' ∈ gsB, hwire ∉ g'.inputs := by
        intro g' hg' hmem
        have : 0 < gsB.countP (fun g => g.inputs.contains hwire) :=
          List.countP_pos_iff.mpr ⟨g', hg', List.contains_iff_mem.mpr hmem⟩
        omega
      by_cases houtH : D.output = hwire
      · have h0 := ((hElimInv (fun _ => false) (gsA ++ [hgate]) (inp false (fun _ => false)) (M0, [])
            (fun g' hg' => by rcases List.mem_append.mp hg' with h | h; exact hfanA g' h; exact (List.mem_singleton.mp h) ▸ hfanH) (hInv0 _)).2 hwire).2
        have h1 := ((hElimInv (fun _ => true) (gsA ++ [hgate]) (inp false (fun _ => true)) (M0, [])
            (fun g' hg' => by rcases List.mem_append.mp hg' with h | h; exact hfanA g' h; exact (List.mem_singleton.mp h) ▸ hfanH) (hInv0 _)).2 hwire).2
        have haccEq : (gsA ++ [hgate]).foldl elimStep (M0, []) = accH := by
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [haccEq, hr2] at h0 h1
        have hkeep0 : D.eval (inp false (fun _ => false)) = ((gsA ++ [hgate]).foldl step (inp false (fun _ => false))).getD hwire false := by
          change (D.gates.foldl step _).getD D.output false = _
          rw [hDsplit, List.foldl_append, houtH]
          exact foldKeep gsB _ hwire (by rw [foldLen]; simp [inp, hwire])
        have hkeep1 : D.eval (inp false (fun _ => true)) = ((gsA ++ [hgate]).foldl step (inp false (fun _ => true))).getD hwire false := by
          change (D.gates.foldl step _).getD D.output false = _
          rw [hDsplit, List.foldl_append, houtH]
          exact foldKeep gsB _ hwire (by rw [foldLen]; simp [inp, hwire])
        rw [← hkeep0, hDfg false (fun _ => false)] at h0
        rw [← hkeep1, hDfg false (fun _ => true)] at h1
        simp only [Bool.false_eq_true, ite_false] at h0 h1
        have hf0 : f (fun _ => false) = false := by decide
        have hf1 : f (fun _ => true) = true := by decide
        rw [hf0] at h0; rw [hf1] at h1
        exact Bool.false_ne_true (h0.symm.trans h1)
      · obtain ⟨xw, hxw1, hfw, hgw⟩ := hWitness
        by_cases hout6 : D.output = 6
        · have h1 := hDfg false (fun _ => true)
          change (D.gates.foldl step (inp false (fun _ => true))).getD D.output false = f (fun _ => true) at h1
          rw [hout6, foldKeep _ _ 6 (by simp [inp])] at h1
          have hf1 : f (fun _ => true) = true := by decide
          rw [hf1] at h1
          exact Bool.false_ne_true h1
        · let wAf := gsA.foldl step (inp false xw)
          let wAt := gsA.foldl step (inp true xw)
          have hwAeq : wAf = wAt.set 6 false := by
            have := foldSetComm 6 false gsA (inp true xw) hnoA (by simp [inp])
            rwa [← hDiff6 xw hxw1] at this
          let wHf := step wAf hgate
          let wHt := step wAt hgate
          have hwAtlen : wAt.length = hwire := by simp [wAt, foldLen, inp, hwire]
          have hwAflen : wAf.length = hwire := by simp [wAf, foldLen, inp, hwire]
          have hwHeq : wHf = (wHt.set 6 false).set hwire (hgate.op.eval (hgate.inputs.map fun j => wAf.getD j false)) := by
            apply List.ext_getElem?
            intro j
            by_cases hjh : j = hwire
            · subst j
              have hl : hwire < (wHt.set 6 false).length := by simp [wHt, step, hwAtlen]
              rw [List.getElem?_set_self hl]
              simp only [wHf, step, List.getElem?_append_right (show wAf.length ≤ hwire by omega), hwAflen, Nat.sub_self, List.getElem?_cons_zero]
            · rw [List.getElem?_set_ne (Ne.symm hjh)]
              by_cases hj6 : j = 6
              · subst j
                have h6lt : 6 < wHt.length := by simp [wHt, step, hwAtlen, hwire]; omega
                rw [List.getElem?_set_self h6lt]
                have h6a : 6 < wAf.length := by omega
                have h6b : 6 < wAt.length := by omega
                change (wAf ++ [_])[6]? = some false
                rw [List.getElem?_append_left h6a, hwAeq, List.getElem?_set_self h6b]
              · rw [List.getElem?_set_ne (Ne.symm hj6)]
                by_cases hjlt : j < hwire
                · have hja : j < wAf.length := by omega
                  have hjb : j < wAt.length := by omega
                  change (wAf ++ [_])[j]? = (wAt ++ [_])[j]?
                  rw [List.getElem?_append_left hja, List.getElem?_append_left hjb, hwAeq,
                    List.getElem?_set_ne (Ne.symm hj6)]
                · rw [List.getElem?_eq_none (by simp [wHf, step, hwAflen]; omega),
                    List.getElem?_eq_none (by simp [wHt, step, hwAtlen]; omega)]
          have hB1 := foldSetComm hwire (hgate.op.eval (hgate.inputs.map fun j => wAf.getD j false)) gsB (wHt.set 6 false) hnoH (by simp [wHt, step, hwAtlen])
          have hB2 := foldSetComm 6 false gsB wHt hnoB (by simp [wHt, step, hwAtlen, hwire]; omega)
          have hBout : D.eval (inp false xw) = D.eval (inp true xw) := by
            change (D.gates.foldl step (inp false xw)).getD D.output false =
              (D.gates.foldl step (inp true xw)).getD D.output false
            rw [hDsplit, List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append,
              List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
            change (gsB.foldl step wHf).getD D.output false = (gsB.foldl step wHt).getD D.output false
            rw [hwHeq, hB1, hB2]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm houtH),
              List.getElem?_set_ne (Ne.symm hout6)]
          rw [hDfg false, hDfg true] at hBout
          simp only [Bool.false_eq_true, ite_false, ite_true, hfw, hgw] at hBout
  | inr q =>
    have h6val : accA.1.getD 6 (Sum.inl false) = Sum.inl false :=
      hElimKeep gsA (M0, []) 6 (by simp [M0])
    have hr2eq : (simpG hgate.op (8 + accA.2.length) (hgate.inputs.map fun j => accA.1.getD j (Sum.inl false))).2 = Sum.inr q := by
      have : accH.1.getD hwire (Sum.inl false) = (simpG hgate.op (8 + accA.2.length) (hgate.inputs.map fun j => accA.1.getD j (Sum.inl false))).2 := by
        simp [accH, elimStep, hwire, ← hAccALen]
      exact this.symm.trans hr2
    have hOrPair : hgate.op = GateOp.or ∧ ∃ k, k ≠ 6 ∧ (hgate.inputs = [6, k] ∨ hgate.inputs = [k, 6]) := by
      have hop := hfanH.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · exfalso
        have hlen := hfanH.2
        rcases hgi : hgate.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [hgi] at h6in
        · simp [hgi] at h6in; subst a
          rw [hop, hgi] at hr2eq
          simp only [List.map_cons, List.map_nil, h6val, simpG] at hr2eq
          cases hr2eq
        · simp [hgi] at h6in
          rw [hop, hgi] at hr2eq
          rcases h6in with rfl | rfl
          · simp only [List.map_cons, List.map_nil, h6val, simpG] at hr2eq
            cases hr2eq
          · simp only [List.map_cons, List.map_nil, h6val] at hr2eq
            cases h : accA.1.getD a (Sum.inl false) with
            | inl c => cases c <;> (rw [h] at hr2eq; simp only [simpG] at hr2eq; cases hr2eq)
            | inr r => rw [h] at hr2eq; simp only [simpG] at hr2eq; cases hr2eq
        · simp [hgi] at hlen
      · refine ⟨hop, ?_⟩
        have hlen := hfanH.2
        rcases hgi : hgate.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · simp [hgi] at h6in
        · simp [hgi] at h6in; subst a
          rw [hop, hgi] at hr2eq
          simp only [List.map_cons, List.map_nil, h6val, simpG] at hr2eq
          cases hr2eq
        · simp [hgi] at h6in
          rw [hop, hgi] at hr2eq
          rcases h6in with rfl | rfl
          · refine ⟨b, ?_, Or.inl rfl⟩
            intro hb; subst b
            simp only [List.map_cons, List.map_nil, h6val, simpG] at hr2eq
            cases hr2eq
          · refine ⟨a, ?_, Or.inr rfl⟩
            intro ha; subst a
            simp only [List.map_cons, List.map_nil, h6val, simpG] at hr2eq
            cases hr2eq
        · simp [hgi] at hlen
      · exfalso
        have h1 := hnotH hop
        rcases hgi : hgate.inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
        · simp [hgi] at h6in
        · simp [hgi] at h6in; subst a
          rw [hop, hgi] at hr2eq
          simp only [List.map_cons, List.map_nil, h6val, simpG] at hr2eq
          cases hr2eq
        · simp [hgi] at h1
    obtain ⟨hopOr, k, hk6, hkins⟩ := hOrPair
    let σ : ℕ → ℕ := fun j =>
      if j < 10 then [1, 0, 4, 7, 5, 2, 0, 6, 3, 8].getD j 0 else j - 1
    let A : Circuit := ⟨gsA.map (mapGate σ), 0⟩
    let B : Circuit := ⟨gsB.map (mapGate σ), σ D.output⟩
    have hfanA' : FanInTwo A := by
      intro g' hg'
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
      have h := hfanA g0 hg0
      exact ⟨h.1, by simpa [mapGate] using h.2⟩
    have hfanB' : FanInTwo B := by
      intro g' hg'
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
      have h := hfanB g0 hg0
      exact ⟨h.1, by simpa [mapGate] using h.2⟩
    have hszAB : A.size + B.size ≤ 13 := by
      change (gsA.map (mapGate σ)).length + (gsB.map (mapGate σ)).length ≤ 13
      simp only [List.length_map]
      change D.gates.length ≤ 14 at hszD
      rw [hDsplit] at hszD
      simp only [List.length_append, List.length_singleton] at hszD
      omega
    have hSigmaRel : ∀ (gs : List Gate) (a b : List Bool),
        (∀ g' ∈ gs, 6 ∉ g'.inputs) →
        10 ≤ a.length → a.length = b.length + 1 →
        (∀ j, j ≠ 6 → b.getD (σ j) false = a.getD j false) →
        ∀ j, j ≠ 6 → ((gs.map (mapGate σ)).foldl step b).getD (σ j) false =
          (gs.foldl step a).getD j false := by
      intro gs
      induction gs with
      | nil => intro a b _ _ _ h j hj; exact h j hj
      | cons g' gs ih =>
        intro a b hno ha hlen h
        have hg6 : 6 ∉ g'.inputs := hno g' List.mem_cons_self
        have hvals : (mapGate σ g').inputs.map (fun j => b.getD j false) =
            g'.inputs.map (fun j => a.getD j false) := by
          rw [List.map_map]
          exact List.map_congr_left fun j hj => h j (fun he => hg6 (he ▸ hj))
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        apply ih (step a g') (step b (mapGate σ g'))
          (fun g'' hg'' => hno g'' (List.mem_cons_of_mem _ hg''))
          (by simp [step]; omega) (by simp [step, hlen])
        intro j hj
        by_cases hjlt : j < a.length
        · have hsj : σ j < b.length := by
            by_cases h10 : j < 10
            · interval_cases j <;> simp [σ] <;> omega
            · obtain ⟨m, rfl⟩ : ∃ m, j = m + 10 := ⟨j - 10, by omega⟩
              simp [σ]; omega
          unfold step
          rw [List.getD_append _ _ _ _ hsj, List.getD_append _ _ _ _ hjlt]
          exact h j hj
        · by_cases hje : j = a.length
          · subst j
            obtain ⟨m, hm⟩ : ∃ m, a.length = m + 10 := ⟨a.length - 10, by omega⟩
            have hsj : σ a.length = b.length := by rw [hm]; simp [σ]; omega
            unfold step
            rw [hsj, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
            change g'.op.eval ((mapGate σ g').inputs.map fun j => b.getD j false) = _
            rw [hvals]
          · obtain ⟨m, hm⟩ : ∃ m, j = m + 10 := ⟨j - 10, by omega⟩
            have hsj : b.length + 1 ≤ σ j := by rw [hm]; simp [σ]; omega
            rw [List.getD_eq_default _ _ (by simp [step]; omega),
              List.getD_eq_default _ _ (by simp [step]; omega)]
    have hBaseMatch : ∀ (b : Bool) (x : Fin 8 → Bool) (j : ℕ), j ≠ 6 →
        (List.ofFn x ++ [x 1 || b]).getD (σ j) false = (inp b x).getD j false := by
      intro b x j hj
      by_cases h10 : j < 10
      · interval_cases j
        all_goals first | exact (hj rfl).elim | simp [σ, inp, List.getD_eq_getElem?_getD]
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 10 := ⟨j - 10, by omega⟩
        rw [List.getD_eq_default _ _ (by simp [σ]),
          List.getD_eq_default _ _ (by simp [inp])]
    have houtNe6 : D.output ≠ 6 := by
      intro hout6
      have h1 := hDfg false (fun _ => true)
      change (D.gates.foldl step (inp false (fun _ => true))).getD D.output false = f (fun _ => true) at h1
      rw [hout6, foldKeep _ _ 6 (by simp [inp])] at h1
      have hf1 : f (fun _ => true) = true := by decide
      rw [hf1] at h1
      exact Bool.false_ne_true h1
    have hABeval : ∀ (b : Bool) (x : Fin 8 → Bool),
        let wb := A.wires (List.ofFn x ++ [x 1 || b])
        B.eval (wb ++ [if b then true else wb.getD (σ k) false]) = if b then g x else f x := by
      intro b x
      dsimp only
      let wa := gsA.foldl step (inp b x)
      let wb := A.wires (List.ofFn x ++ [x 1 || b])
      have hwaLen : wa.length = 10 + gsA.length := by simp [wa, foldLen, inp]
      have hwbLen : wb.length = 9 + gsA.length := by
        change ((gsA.map (mapGate σ)).foldl step (List.ofFn x ++ [x 1 || b])).length = _
        rw [foldLen, List.length_append, List.length_ofFn, List.length_singleton, List.length_map]
      have hArel : ∀ j, j ≠ 6 → wb.getD (σ j) false = wa.getD j false :=
        hSigmaRel gsA (inp b x) (List.ofFn x ++ [x 1 || b]) hnoA (by simp [inp]) (by simp [inp]) (hBaseMatch b x)
      have h6wa : wa.getD 6 false = b := by
        rw [foldKeep gsA (inp b x) 6 (by simp [inp])]
        rfl
      have hgateVal : hgate.op.eval (hgate.inputs.map fun j => wa.getD j false) =
          if b then true else wb.getD (σ k) false := by
        rw [hopOr]
        rcases hkins with hk1 | hk2
        · rw [hk1, List.map_cons, List.map_cons, List.map_nil, evalOr2, h6wa, ← hArel k hk6]
          cases b <;> simp
        · rw [hk2, List.map_cons, List.map_cons, List.map_nil, evalOr2, h6wa, ← hArel k hk6]
          cases b <;> simp
      have hstepRel : ∀ j, j ≠ 6 →
          (wb ++ [if b then true else wb.getD (σ k) false]).getD (σ j) false =
            (step wa hgate).getD j false := by
        intro j hj
        by_cases hjlt : j < wa.length
        · have hsj : σ j < wb.length := by
            by_cases h10 : j < 10
            · interval_cases j <;> simp [σ] <;> omega
            · obtain ⟨m, rfl⟩ : ∃ m, j = m + 10 := ⟨j - 10, by omega⟩
              simp [σ]; omega
          unfold step
          rw [List.getD_append _ _ _ _ hsj, List.getD_append _ _ _ _ hjlt]
          exact hArel j hj
        · by_cases hje : j = wa.length
          · subst j
            have hsj : σ wa.length = wb.length := by
              rw [hwaLen, Nat.add_comm 10, hwbLen]; simp [σ]; omega
            unfold step
            rw [hsj, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
              List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero, hgateVal]
          · obtain ⟨m, hm⟩ : ∃ m, j = m + 10 := ⟨j - 10, by omega⟩
            have hsj : wb.length + 1 ≤ σ j := by rw [hm]; simp [σ]; omega
            rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp [step]; omega)]
      have hBrel := hSigmaRel gsB (step wa hgate) (wb ++ [if b then true else wb.getD (σ k) false])
        hnoB (by simp [step, hwaLen]; omega) (by simp [step, hwaLen, hwbLen]; omega) hstepRel D.output houtNe6
      have hDcomb : (gsB.foldl step (step wa hgate)).getD D.output false = D.eval (inp b x) := by
        change _ = (D.gates.foldl step (inp b x)).getD D.output false
        rw [hDsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact hBrel.trans (hDcomb.trans (hDfg b x))
    obtain ⟨xm, hxm⟩ := marked A B (σ k) hfanA' hfanB' hszAB (fun x => by simpa using hABeval false x)
    exact hxm (by simpa using hABeval true xm)
