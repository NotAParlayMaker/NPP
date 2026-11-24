import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4936_317
    (cofactor : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (sparse : ∀ (C : Circuit) (b : Bool), FanInTwo C → C.size ≤ 18 →
      (∀ (v : Fin 2) (K : Finset (Fin C.gates.length)),
        (∀ i ∈ K, let g := C.gates.get i
          let W : List ℕ := GateOp.casesOn g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
          v.val ∈ W ∨ (b = true ∧ 10 ∈ W)) → K.card ≤ 2) →
      ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1]) =
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun k => x (Fin.ofNat 10 (k / 10)) && x (Fin.ofNat 10 (k % 10)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.output ≤ (29 : ℕ) → (∀ x6 ∈ x1.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7 := by
  have pin (n : ℕ) (S : List (Bool ⊕ ℕ)) (C : Circuit)
      (K : Finset (Fin C.gates.length)) (hC : FanInTwo C)
      (hS : ∀ s ∈ S, ∀ k, s = Sum.inr k → k < n)
      (F : (Fin n → Bool) → Bool) (hne : ∃ x y, F x ≠ F y)
      (hF : ∀ x, C.eval (S.map (fun s => Sum.elim id (fun k => (List.ofFn x).getD k false) s)) = F x)
      (hK : letI := NestedCover.gateOpDecEq
        ∀ i ∈ K, ∃ w < S.length, ∃ c : Bool, S.getD w (Sum.inl false) = Sum.inl c ∧
          w ∈ (if (C.gates.get i).op = .not then (C.gates.get i).inputs.take 1 else (C.gates.get i).inputs)) :
      ∃ D : Circuit, FanInTwo D ∧ D.size + K.card ≤ C.size ∧
        ∀ x, D.eval (List.ofFn x) = F x := by
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    let active (g : Gate) : List ℕ :=
      GateOp.casesOn g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
    have active_of_ne_not (g : Gate) (h : g.op ≠ GateOp.not) :
        active g = g.inputs := by
      cases hop : g.op with
      | and => dsimp only [active]; rw [hop]
      | or => dsimp only [active]; rw [hop]
      | not => exact False.elim (h hop)
      | mod _ => dsimp only [active]; rw [hop]
      | maj => dsimp only [active]; rw [hop]
    have active_of_not (g : Gate) (h : g.op = GateOp.not) :
        active g = g.inputs.take 1 := by
      dsimp only [active]; rw [h]
    let evalSym (s : Bool ⊕ ℕ) (w : List Bool) : Bool :=
      Sum.elim id (fun k => w.getD k false) s
    let elimNot (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
      List.casesOn vs (Sum.inl (Sum.inl true)) (fun v _ =>
        Sum.elim (fun b => Sum.inl (Sum.inl (!b))) (fun k => Sum.inr ⟨GateOp.not, [k]⟩) v)
    let elimAnd (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
      List.casesOn vs (Sum.inl (Sum.inl true)) (fun v1 t1 =>
        List.casesOn t1 (Sum.inl v1) (fun v2 t2 =>
          List.casesOn t2
            (Sum.elim
              (fun b1 => Bool.casesOn b1 (Sum.inl (Sum.inl false)) (Sum.inl v2))
              (fun k1 => Sum.elim
                (fun b2 => Bool.casesOn b2 (Sum.inl (Sum.inl false)) (Sum.inl (Sum.inr k1)))
                (fun k2 => if k1 = k2 then Sum.inl (Sum.inr k1) else Sum.inr ⟨GateOp.and, [k1, k2]⟩)
                v2)
              v1)
            (fun _ _ => Sum.inl (Sum.inl false))))
    let elimOr (vs : List (Bool ⊕ ℕ)) : (Bool ⊕ ℕ) ⊕ Gate :=
      List.casesOn vs (Sum.inl (Sum.inl false)) (fun v1 t1 =>
        List.casesOn t1 (Sum.inl v1) (fun v2 t2 =>
          List.casesOn t2
            (Sum.elim
              (fun b1 => Bool.casesOn b1 (Sum.inl v2) (Sum.inl (Sum.inl true)))
              (fun k1 => Sum.elim
                (fun b2 => Bool.casesOn b2 (Sum.inl (Sum.inr k1)) (Sum.inl (Sum.inl true)))
                (fun k2 => if k1 = k2 then Sum.inl (Sum.inr k1) else Sum.inr ⟨GateOp.or, [k1, k2]⟩)
                v2)
              v1)
            (fun _ _ => Sum.inl (Sum.inl false))))
    let elimGate (op : GateOp) (vs : List (Bool ⊕ ℕ)) :
        (Bool ⊕ ℕ) ⊕ Gate :=
      GateOp.casesOn op
        (elimAnd vs) (elimOr vs) (elimNot vs) (fun _ => Sum.inl (Sum.inl false)) (Sum.inl (Sum.inl false))
    let elimStep (n' : ℕ)
        (acc : List (Bool ⊕ ℕ) × List Gate × List Bool)
        (g : Gate) :
        List (Bool ⊕ ℕ) × List Gate × List Bool :=
      let st := acc.1
      let ngs := acc.2.1
      let fl := acc.2.2
      let vs := g.inputs.map fun i => st.getD i (Sum.inl false)
      Sum.elim
        (fun sym => (st ++ [sym], ngs, fl ++ [true]))
        (fun ng => (st ++ [Sum.inr (n' + ngs.length)], ngs ++ [ng], fl ++ [false]))
        (elimGate g.op vs)
    have wires_start (gs : List Gate) (w : List Bool) :
        ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
      induction gs generalizing w with
      | nil => exact ⟨[], by simp, rfl⟩
      | cons g gs ih =>
        rw [List.foldl_cons]
        obtain ⟨t, ht, hlen⟩ := ih (step w g)
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hlen]⟩
        rw [ht]; simp [step]
    have wires_len (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      obtain ⟨t, ht, hlen⟩ := wires_start gs w
      rw [ht, List.length_append, hlen]
    have getD_snoc_end {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
      simp [List.getD_eq_getElem?_getD]
    have elimGate_ok (op : GateOp)
        (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
        (vs : List (Bool ⊕ ℕ)) (hlen : vs.length ≤ 2) (w : List Bool) :
        (∀ sym, elimGate op vs = Sum.inl sym →
          evalSym sym w = op.eval (vs.map fun s => evalSym s w) ∧
          (∀ k, sym = Sum.inr k → Sum.inr k ∈ vs)) ∧
        (∀ ng, elimGate op vs = Sum.inr ng →
          ng.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          ng.inputs.length ≤ 2 ∧
          ng.op.eval (ng.inputs.map fun i => w.getD i false) = op.eval (vs.map fun s => evalSym s w)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl | rfl
      · cases vs with
        | nil =>
          exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
        | cons v1 t1 =>
          cases t1 with
          | nil =>
            exact ⟨fun sym hs => by cases hs; exact ⟨by simp [eval_and], fun k hk => by subst hk; exact List.mem_singleton_self _⟩, fun ng hng => by cases hng⟩
          | cons v2 t2 =>
            cases t2 with
            | cons _ _ => simp at hlen
            | nil =>
              cases v1 with
              | inl b1 =>
                cases v2 with
                | inl b2 =>
                  cases b1 <;> cases b2 <;>
                    exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
                | inr k2 =>
                  cases b1 with
                  | false =>
                    exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
                  | true =>
                    exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_and], fun k hk => by cases hk; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩, fun ng hng => by cases hng⟩
              | inr k1 =>
                cases v2 with
                | inl b2 =>
                  cases b2 with
                  | false =>
                    exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_and], fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
                  | true =>
                    exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_and], fun k hk => by cases hk; exact List.mem_cons_self ..⟩, fun ng hng => by cases hng⟩
                | inr k2 =>
                  by_cases hk : k1 = k2
                  · subst hk
                    refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                    · simp only [elimGate, elimAnd, Sum.elim_inr, ↓reduceIte] at hs; cases hs
                      exact ⟨by simp [evalSym, eval_and], fun k hk' => by cases hk'; exact List.mem_cons_self ..⟩
                    · simp only [elimGate, elimAnd, Sum.elim_inr, ↓reduceIte] at hng; cases hng
                  · refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                    · simp only [elimGate, elimAnd, Sum.elim_inr, hk, ↓reduceIte] at hs; cases hs
                    · simp only [elimGate, elimAnd, Sum.elim_inr, hk, ↓reduceIte] at hng; cases hng
                      exact ⟨Set.mem_insert _ _, le_refl 2, by simp [evalSym, eval_and]⟩
      · cases vs with
        | nil =>
          exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
        | cons v1 t1 =>
          cases t1 with
          | nil =>
            exact ⟨fun sym hs => by cases hs; exact ⟨by simp [eval_or], fun k hk => by subst hk; exact List.mem_singleton_self _⟩, fun ng hng => by cases hng⟩
          | cons v2 t2 =>
            cases t2 with
            | cons _ _ => simp at hlen
            | nil =>
              cases v1 with
              | inl b1 =>
                cases v2 with
                | inl b2 =>
                  cases b1 <;> cases b2 <;>
                    exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
                | inr k2 =>
                  cases b1 with
                  | false =>
                    exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_or], fun k hk => by cases hk; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩, fun ng hng => by cases hng⟩
                  | true =>
                    exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
              | inr k1 =>
                cases v2 with
                | inl b2 =>
                  cases b2 with
                  | false =>
                    exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_or], fun k hk => by cases hk; exact List.mem_cons_self ..⟩, fun ng hng => by cases hng⟩
                  | true =>
                    exact ⟨fun sym hs => by cases hs; exact ⟨by simp [evalSym, eval_or], fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
                | inr k2 =>
                  by_cases hk : k1 = k2
                  · subst hk
                    refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                    · simp only [elimGate, elimOr, Sum.elim_inr, ↓reduceIte] at hs; cases hs
                      exact ⟨by simp [evalSym, eval_or], fun k hk' => by cases hk'; exact List.mem_cons_self ..⟩
                    · simp only [elimGate, elimOr, Sum.elim_inr, ↓reduceIte] at hng; cases hng
                  · refine ⟨fun sym hs => ?_, fun ng hng => ?_⟩
                    · simp only [elimGate, elimOr, Sum.elim_inr, hk, ↓reduceIte] at hs; cases hs
                    · simp only [elimGate, elimOr, Sum.elim_inr, hk, ↓reduceIte] at hng; cases hng
                      exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), le_refl 2, by simp [evalSym, eval_or]⟩
      · cases vs with
        | nil =>
          exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
        | cons v1 t1 =>
          cases v1 with
          | inl b1 =>
            exact ⟨fun sym hs => by cases hs; exact ⟨rfl, fun k hk => by cases hk⟩, fun ng hng => by cases hng⟩
          | inr k1 =>
            exact ⟨(fun sym hs => by cases hs), (fun ng hng => by cases hng; exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)), Nat.le_succ 1, rfl⟩)⟩
    have elimGate_of_const (op : GateOp)
        (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
        (vs : List (Bool ⊕ ℕ)) (hlen : vs.length ≤ 2) (c : Bool)
        (hnot_in : op = GateOp.not → vs.head? = some (Sum.inl c))
        (hbin_in : op ≠ GateOp.not → Sum.inl c ∈ vs) :
        ∃ sym, elimGate op vs = Sum.inl sym := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl | rfl
      · have hmem := hbin_in (by intro h; cases h)
        cases vs with
        | nil => cases hmem
        | cons v1 t1 =>
          cases t1 with
          | nil =>
            simp only [List.mem_singleton] at hmem; subst hmem
            exact ⟨_, rfl⟩
          | cons v2 t2 =>
            cases t2 with
            | cons _ _ => simp at hlen
            | nil =>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
              rcases hmem with rfl | rfl
              · cases v2 with
                | inl b2 => cases c <;> cases b2 <;> exact ⟨_, rfl⟩
                | inr k2 => cases c <;> exact ⟨_, rfl⟩
              · cases v1 with
                | inl b1 => cases c <;> cases b1 <;> exact ⟨_, rfl⟩
                | inr k1 => cases c <;> exact ⟨_, rfl⟩
      · have hmem := hbin_in (by intro h; cases h)
        cases vs with
        | nil => cases hmem
        | cons v1 t1 =>
          cases t1 with
          | nil =>
            simp only [List.mem_singleton] at hmem; subst hmem
            exact ⟨_, rfl⟩
          | cons v2 t2 =>
            cases t2 with
            | cons _ _ => simp at hlen
            | nil =>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
              rcases hmem with rfl | rfl
              · cases v2 with
                | inl b2 => cases c <;> cases b2 <;> exact ⟨_, rfl⟩
                | inr k2 => cases c <;> exact ⟨_, rfl⟩
              · cases v1 with
                | inl b1 => cases c <;> cases b1 <;> exact ⟨_, rfl⟩
                | inr k1 => cases c <;> exact ⟨_, rfl⟩
      · have hhd := hnot_in rfl
        cases vs with
        | nil => cases hhd
        | cons v1 t1 =>
          simp only [List.head?_cons, Option.some.injEq] at hhd; subst hhd
          exact ⟨_, rfl⟩
    have elimRun_inv (n' : ℕ) (gs : List Gate)
        (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (st0 : List (Bool ⊕ ℕ)) (ngs0 : List Gate) (fl0 : List Bool)
        (hfan0 : ∀ g ∈ ngs0, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (hbd0 : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < n' + ngs0.length) :
        let res := gs.foldl (elimStep n') (st0, ngs0, fl0)
        (∃ stT ngsT flT, res.1 = st0 ++ stT ∧ res.2.1 = ngs0 ++ ngsT ∧ res.2.2 = fl0 ++ flT ∧
          stT.length = gs.length ∧ flT.length = gs.length) ∧
        res.2.1.length + res.2.2.count true = ngs0.length + fl0.count true + gs.length ∧
        (∀ g ∈ res.2.1, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (∀ s ∈ res.1, ∀ k, s = Sum.inr k → k < n' + res.2.1.length) ∧
        (∀ (wIn w0 : List Bool), wIn.length = n' → w0.length = st0.length →
          (∀ i < st0.length, evalSym (st0.getD i (Sum.inl false)) (ngs0.foldl step wIn) = w0.getD i false) →
          ∀ i < res.1.length, evalSym (res.1.getD i (Sum.inl false)) (res.2.1.foldl step wIn) = (gs.foldl step w0).getD i false) := by
      induction gs generalizing st0 ngs0 fl0 with
      | nil =>
        refine ⟨⟨[], [], [], by simp, by simp, by simp, rfl, rfl⟩, by simp, hfan0, hbd0, ?_⟩
        intro wIn w0 _ _ hagree i hi
        exact hagree i hi
      | cons g gs ih =>
        have hg := hfan g (List.mem_cons_self ..)
        have hgs : ∀ a ∈ gs, a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ a.inputs.length ≤ 2 :=
          fun a ha => hfan a (List.mem_cons_of_mem g ha)
        let vs := g.inputs.map fun i => st0.getD i (Sum.inl false)
        have hvs_len : vs.length ≤ 2 := by simp [vs, hg.2]
        have hvs_bd : ∀ s ∈ vs, ∀ k, s = Sum.inr k → k < n' + ngs0.length := by
          intro s hs k hk
          simp only [vs, List.mem_map] at hs
          obtain ⟨idx, _, rfl⟩ := hs
          by_cases hi : idx < st0.length
          · have hmem : st0.getD idx (Sum.inl false) ∈ st0 := by
              rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
            exact hbd0 _ hmem k hk
          · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at hk; cases hk
        cases heg : elimGate g.op vs with
        | inl sym =>
          have hstep : elimStep n' (st0, ngs0, fl0) g = (st0 ++ [sym], ngs0, fl0 ++ [true]) := by
            dsimp only [elimStep]
            change Sum.elim
              (fun s => (st0 ++ [s], ngs0, fl0 ++ [true]))
              (fun ng => (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng], fl0 ++ [false]))
              (elimGate g.op vs) = _
            rw [heg]; rfl
          have hbd1 : ∀ s ∈ st0 ++ [sym], ∀ k, s = Sum.inr k → k < n' + ngs0.length := by
            intro s hs k hk
            rcases List.mem_append.mp hs with h1 | h1
            · exact hbd0 s h1 k hk
            · simp only [List.mem_singleton] at h1; rw [h1] at hk
              have hmem := (elimGate_ok g.op hg.1 vs hvs_len []).1 sym heg |>.2 k hk
              exact hvs_bd (Sum.inr k) hmem k rfl
          have hrec := ih hgs (st0 ++ [sym]) ngs0 (fl0 ++ [true]) hfan0 hbd1
          rw [List.foldl_cons, hstep]
          obtain ⟨⟨stT, ngsT, flT, hst, hngs, hfl, hsl, hfl_len⟩, hcnt, hfan', hbd', hsem⟩ := hrec
          refine ⟨⟨sym :: stT, ngsT, true :: flT, ?_, hngs, ?_, by simp [hsl], by simp [hfl_len]⟩, ?_, hfan', hbd', ?_⟩
          · rw [hst]; simp
          · rw [hfl]; simp
          · simp only [List.count_append, List.count_cons, beq_self_eq_true, ↓reduceIte, List.count_nil,
              List.length_cons] at hcnt ⊢
            omega
          · intro wIn w0 hwIn hw0 hagree
            rw [List.foldl_cons]
            apply hsem wIn (step w0 g) hwIn (by simp [step, hw0])
            intro i hi
            simp only [List.length_append, List.length_cons, List.length_nil] at hi
            by_cases hilt : i < st0.length
            · rw [List.getD_append _ _ _ _ hilt, List.getD_append _ _ _ _ (by omega : i < w0.length)]
              exact hagree i hilt
            · have hieq : i = st0.length := by omega
              subst hieq
              rw [getD_snoc_end]
              have hval := (elimGate_ok g.op hg.1 vs hvs_len (ngs0.foldl step wIn)).1 sym heg |>.1
              rw [hval]
              simp only [step]
              rw [← hw0, getD_snoc_end]
              congr 1
              rw [List.map_map]
              apply List.map_congr_left
              intro idx _
              change evalSym (st0.getD idx (Sum.inl false)) (ngs0.foldl step wIn) = w0.getD idx false
              by_cases hidx : idx < st0.length
              · exact hagree idx hidx
              · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hidx),
                  List.getD_eq_default _ _ (by omega : w0.length ≤ idx)]
                rfl
        | inr ng =>
          have hstep : elimStep n' (st0, ngs0, fl0) g =
              (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng], fl0 ++ [false]) := by
            dsimp only [elimStep]
            change Sum.elim
              (fun s => (st0 ++ [s], ngs0, fl0 ++ [true]))
              (fun ng' => (st0 ++ [Sum.inr (n' + ngs0.length)], ngs0 ++ [ng'], fl0 ++ [false]))
              (elimGate g.op vs) = _
            rw [heg]; rfl
          have hng_ok := (elimGate_ok g.op hg.1 vs hvs_len []).2 ng heg
          have hfan1 : ∀ a ∈ ngs0 ++ [ng], a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ a.inputs.length ≤ 2 := by
            intro a ha
            rcases List.mem_append.mp ha with h1 | h1
            · exact hfan0 a h1
            · simp only [List.mem_singleton] at h1; rw [h1]; exact ⟨hng_ok.1, hng_ok.2.1⟩
          have hbd1 : ∀ s ∈ st0 ++ [Sum.inr (n' + ngs0.length)], ∀ k, s = Sum.inr k → k < n' + (ngs0 ++ [ng]).length := by
            intro s hs k hk
            rcases List.mem_append.mp hs with h1 | h1
            · have := hbd0 s h1 k hk; simp; omega
            · simp only [List.mem_singleton] at h1; rw [h1] at hk; cases hk; simp
          have hrec := ih hgs (st0 ++ [Sum.inr (n' + ngs0.length)]) (ngs0 ++ [ng]) (fl0 ++ [false]) hfan1 hbd1
          rw [List.foldl_cons, hstep]
          obtain ⟨⟨stT, ngsT, flT, hst, hngs, hfl, hsl, hfl_len⟩, hcnt, hfan', hbd', hsem⟩ := hrec
          refine ⟨⟨Sum.inr (n' + ngs0.length) :: stT, ng :: ngsT, false :: flT, ?_, ?_, ?_, by simp [hsl], by simp [hfl_len]⟩, ?_, hfan', hbd', ?_⟩
          · rw [hst]; simp
          · rw [hngs]; simp
          · rw [hfl]; simp
          · have hcf : [false].count true = 0 := rfl
            simp only [List.length_append, List.length_cons, List.length_nil, List.count_append, hcf] at hcnt ⊢
            omega
          · intro wIn w0 hwIn hw0 hagree
            rw [List.foldl_cons]
            apply hsem wIn (step w0 g) hwIn (by simp [step, hw0])
            intro i hi
            simp only [List.length_append, List.length_cons, List.length_nil] at hi
            have hfold : (ngs0 ++ [ng]).foldl step wIn = step (ngs0.foldl step wIn) ng := by
              rw [List.foldl_append]; rfl
            rw [hfold]
            by_cases hilt : i < st0.length
            · rw [List.getD_append _ _ _ _ hilt, List.getD_append _ _ _ _ (by omega : i < w0.length)]
              have hprev := hagree i hilt
              have hmem : st0.getD i (Sum.inl false) ∈ st0 := by
                rw [List.getD_eq_getElem _ _ hilt]; exact List.getElem_mem hilt
              cases hs : st0.getD i (Sum.inl false) with
              | inl b => rw [hs] at hprev; exact hprev
              | inr k =>
                have hk : k < (ngs0.foldl step wIn).length := by
                  rw [wires_len, hwIn]; exact hbd0 _ hmem k hs
                simp only [evalSym, Sum.elim_inr, step]
                rw [List.getD_append _ _ _ _ hk]
                rw [hs] at hprev; exact hprev
            · have hieq : i = st0.length := by omega
              subst hieq
              rw [getD_snoc_end]
              simp only [evalSym, Sum.elim_inr, step]
              have hlen_w : (ngs0.foldl step wIn).length = n' + ngs0.length := by
                rw [wires_len, hwIn]
              rw [← hlen_w, getD_snoc_end]
              have hval := (elimGate_ok g.op hg.1 vs hvs_len (ngs0.foldl step wIn)).2 ng heg |>.2.2
              rw [hval, ← hw0, getD_snoc_end]
              congr 1
              rw [List.map_map]
              apply List.map_congr_left
              intro idx _
              change evalSym (st0.getD idx (Sum.inl false)) (ngs0.foldl step wIn) = w0.getD idx false
              by_cases hidx : idx < st0.length
              · exact hagree idx hidx
              · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hidx),
                  List.getD_eq_default _ _ (by omega : w0.length ≤ idx)]
                rfl
    have elimRun_at_gate (n' : ℕ) (gs : List Gate)
        (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (st0 : List (Bool ⊕ ℕ))
        (hbd0 : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < n')
        (j : ℕ) (hj : j < gs.length) :
        let res := gs.foldl (elimStep n') (st0, [], [])
        let pre := (gs.take j).foldl (elimStep n') (st0, [], [])
        let vs := (gs[j]).inputs.map fun i => pre.1.getD i (Sum.inl false)
        pre.1.length = st0.length + j ∧
        (∀ i < st0.length + j, res.1.getD i (Sum.inl false) = pre.1.getD i (Sum.inl false)) ∧
        (∀ sym, elimGate (gs[j]).op vs = Sum.inl sym →
          res.1.getD (st0.length + j) (Sum.inl false) = sym ∧ res.2.2.getD j false = true) := by
      have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
        have h1 := (List.take_append_drop j gs).symm
        rw [List.drop_eq_getElem_cons hj] at h1; exact h1
      have hfan_take : ∀ g ∈ gs.take j, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
        fun g hg => hfan g (List.mem_of_mem_take hg)
      have hfan_drop : ∀ g ∈ gs.drop (j + 1), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
        fun g hg => hfan g (List.mem_of_mem_drop hg)
      have hpre := elimRun_inv n' (gs.take j) hfan_take st0 [] [] (by simp) (by simpa using hbd0)
      obtain ⟨⟨stP, ngsP, flP, hstP, hngsP, hflP, hslP, hflP_len⟩, _, hfanP, hbdP, _⟩ := hpre
      have hlen_take : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
      have hpre_st_len : ((gs.take j).foldl (elimStep n') (st0, [], [])).1.length = st0.length + j := by
        rw [hstP, List.length_append, hslP, hlen_take]
      have hpre_fl_len : ((gs.take j).foldl (elimStep n') (st0, [], [])).2.2.length = j := by
        rw [hflP, List.nil_append, hflP_len, hlen_take]
      have hres_eq : gs.foldl (elimStep n') (st0, [], []) =
          (gs.drop (j + 1)).foldl (elimStep n')
            (elimStep n' ((gs.take j).foldl (elimStep n') (st0, [], [])) gs[j]) := by
        have hf := congrArg (fun l => l.foldl (elimStep n') (st0, [], [])) hsplit
        rw [hf, List.foldl_append, List.foldl_cons]
      have hpost := elimRun_inv n' (gs[j] :: gs.drop (j + 1))
        (fun g hg => by
          rcases List.mem_cons.mp hg with rfl | hg'
          · exact hfan _ (List.getElem_mem hj)
          · exact hfan_drop g hg')
        ((gs.take j).foldl (elimStep n') (st0, [], [])).1
        ((gs.take j).foldl (elimStep n') (st0, [], [])).2.1
        ((gs.take j).foldl (elimStep n') (st0, [], [])).2.2
        hfanP hbdP
      obtain ⟨⟨stT, _, _, hstT, _, _, _, _⟩, _, _, _, _⟩ := hpost
      have hres_eq2 : gs.foldl (elimStep n') (st0, [], []) =
          (gs[j] :: gs.drop (j + 1)).foldl (elimStep n') ((gs.take j).foldl (elimStep n') (st0, [], [])) := by
        have hf := congrArg (fun l => l.foldl (elimStep n') (st0, [], [])) hsplit
        rw [hf, List.foldl_append]
      refine ⟨hpre_st_len, ?_, ?_⟩
      · intro i hi
        rw [hres_eq2, hstT, List.getD_append _ _ _ _ (by omega)]
      · intro sym hsym
        set pre := (gs.take j).foldl (elimStep n') (st0, [], [])
        have hstep_j : elimStep n' pre gs[j] = (pre.1 ++ [sym], pre.2.1, pre.2.2 ++ [true]) := by
          dsimp only [elimStep]
          change Sum.elim
            (fun s => (pre.1 ++ [s], pre.2.1, pre.2.2 ++ [true]))
            (fun ng => (pre.1 ++ [Sum.inr (n' + pre.2.1.length)], pre.2.1 ++ [ng], pre.2.2 ++ [false]))
            (elimGate gs[j].op (gs[j].inputs.map fun i => pre.1.getD i (Sum.inl false))) = _
          rw [hsym]; rfl
        have hgj := hfan gs[j] (List.getElem_mem hj)
        have hvs_len : (gs[j].inputs.map fun i => pre.1.getD i (Sum.inl false)).length ≤ 2 := by simp [hgj.2]
        have hbd_next : ∀ s ∈ pre.1 ++ [sym], ∀ k, s = Sum.inr k → k < n' + pre.2.1.length := by
          intro s hs k hk
          rcases List.mem_append.mp hs with h1 | h1
          · exact hbdP s h1 k hk
          · simp only [List.mem_singleton] at h1; rw [h1] at hk
            have hmem := (elimGate_ok gs[j].op hgj.1 _ hvs_len []).1 sym hsym |>.2 k hk
            simp only [List.mem_map] at hmem
            obtain ⟨idx, _, hidx⟩ := hmem
            by_cases hlt : idx < pre.1.length
            · have hmem_pre : pre.1.getD idx (Sum.inl false) ∈ pre.1 := by
                rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
              exact hbdP _ hmem_pre k hidx
            · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)] at hidx; cases hidx
        have hdrop := elimRun_inv n' (gs.drop (j + 1)) hfan_drop (pre.1 ++ [sym]) pre.2.1 (pre.2.2 ++ [true]) hfanP hbd_next
        obtain ⟨⟨stD, _, flD, hstD, _, hflD, _, _⟩, _, _, _, _⟩ := hdrop
        rw [hres_eq, hstep_j]
        refine ⟨?_, ?_⟩
        · rw [hstD, List.getD_append _ _ _ _ (by simp; omega), ← hpre_st_len, getD_snoc_end]
        · rw [hflD, List.getD_append _ _ _ _ (by simp; omega), ← hpre_fl_len, getD_snoc_end]
    have hinv := elimRun_inv n C.gates hC S [] [] (by simp) (by simpa using hS)
    obtain ⟨⟨stT, _, flT, hst, _, hfl, hsl, hfl_len⟩, hcnt, hfan_new, _, hsem⟩ := hinv
    set res := C.gates.foldl (elimStep n) (S, [], [])
    have hmarked (j : Fin C.gates.length) (hj : j ∈ K) : res.2.2.getD j.val false = true := by
      obtain ⟨w, hw, c, hc, hact⟩ := hK j hj
      have hactive : w ∈ active (C.gates.get j) := by
        by_cases hnot : (C.gates.get j).op = .not
        · rwa [ite_eq_left hnot, ← active_of_not _ hnot] at hact
        · rwa [ite_eq_right hnot, ← active_of_ne_not _ hnot] at hact
      obtain ⟨_, _, hgate_j⟩ := elimRun_at_gate n C.gates hC S hS j.val j.isLt
      let pre := (C.gates.take j.val).foldl (elimStep n) (S, [], [])
      have hp := elimRun_inv n (C.gates.take j.val) (fun g hg => hC g (List.mem_of_mem_take hg))
        S [] [] (by simp) (by simpa using hS)
      obtain ⟨⟨preS, _, _, hpS, _, _, _, _⟩, _, _, _, _⟩ := hp
      have hpre_w : pre.1.getD w (Sum.inl false) = Sum.inl c := by
        rw [show pre.1 = S ++ preS from hpS, List.getD_append _ _ _ _ hw, hc]
      have hgj_fan := hC C.gates[j.val] (List.getElem_mem j.isLt)
      change w ∈ active C.gates[j.val] at hactive
      let vs := C.gates[j.val].inputs.map fun i => pre.1.getD i (Sum.inl false)
      have hvs_len : vs.length ≤ 2 := by simp [vs, hgj_fan.2]
      have hnot_in : C.gates[j.val].op = .not → vs.head? = some (Sum.inl c) := by
        intro hnot
        rw [active_of_not _ hnot] at hactive
        cases hin : C.gates[j.val].inputs with
        | nil => rw [hin] at hactive; simp at hactive
        | cons a rest =>
          rw [hin] at hactive
          simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hactive
          subst hactive
          simp only [vs, hin, List.map_cons, List.head?_cons, hpre_w]
      have hbin_in : C.gates[j.val].op ≠ .not → Sum.inl c ∈ vs := by
        intro hnot
        exact List.mem_map.mpr ⟨w, by rwa [active_of_ne_not _ hnot] at hactive, hpre_w⟩
      obtain ⟨sym, hsym⟩ := elimGate_of_const C.gates[j.val].op hgj_fan.1 vs hvs_len c hnot_in hbin_in
      exact (hgate_j sym hsym).2
    have hlen_fl : res.2.2.length = C.gates.length := by rw [hfl, List.nil_append, hfl_len]
    have hcard_count (l : List Bool) :
        (Finset.univ.filter (fun i : Fin l.length => l.get i = true)).card = l.count true := by
      rw [Finset.card_filter]
      induction l with
      | nil => simp
      | cons x xs ih =>
        rw [List.count_cons]
        change (∑ i : Fin (xs.length + 1), if (x :: xs).get i = true then 1 else 0) = _
        rw [Fin.sum_univ_succ]
        have htail : (∑ i : Fin xs.length, if (x :: xs).get i.succ = true then 1 else 0) = xs.count true := ih
        rw [htail]
        cases x <;> simp [Nat.add_comm]
    have hK_count : K.card ≤ res.2.2.count true := by
      let f : Fin C.gates.length ↪ Fin res.2.2.length :=
        ⟨fun j => ⟨j.val, by rw [hlen_fl]; exact j.isLt⟩, fun _ _ h => Fin.ext (congrArg (fun z : Fin res.2.2.length => z.val) h)⟩
      rw [← hcard_count, ← Finset.card_map f]
      apply Finset.card_le_card
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      have he := hmarked j hj
      change res.2.2.getD (f j).val false = true at he
      rw [List.getD_eq_getElem _ _ (f j).isLt] at he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact he
    have hsem_x (x : Fin n → Bool) :
        evalSym (res.1.getD C.output (Sum.inl false)) (res.2.1.foldl step (List.ofFn x)) = F x := by
      rw [← hF x]
      let w0 := S.map fun s => evalSym s (List.ofFn x)
      have hw0_len : w0.length = S.length := by simp [w0]
      have hagree0 : ∀ i < S.length, evalSym (S.getD i (Sum.inl false)) (List.ofFn x) = w0.getD i false := by
        intro i hi
        rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega : i < w0.length)]
        simp [w0]
      by_cases hout : C.output < res.1.length
      · exact hsem (List.ofFn x) w0 (List.length_ofFn) hw0_len hagree0 C.output hout
      · have hlen_res : res.1.length = S.length + C.gates.length := by rw [hst, List.length_append, hsl]
        have hlen_w : (C.gates.foldl step w0).length = S.length + C.gates.length := by rw [wires_len, hw0_len]
        change evalSym (res.1.getD C.output (Sum.inl false)) _ = (C.gates.foldl step w0).getD C.output false
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hout),
          List.getD_eq_default _ _ (by omega : (C.gates.foldl step w0).length ≤ C.output)]
        rfl
    cases hout_sym : res.1.getD C.output (Sum.inl false) with
    | inl b =>
      obtain ⟨x, y, hxy⟩ := hne
      have h1 := hsem_x x
      have h2 := hsem_x y
      rw [hout_sym] at h1 h2
      exact (hxy (h1.symm.trans h2)).elim
    | inr k =>
      refine ⟨⟨res.2.1, k⟩, hfan_new, ?_, fun x => ?_⟩
      · change res.2.1.length + K.card ≤ C.gates.length
        simp only [List.length_nil, List.count_nil, zero_add] at hcnt
        omega
      · have hx := hsem_x x
        rw [hout_sym] at hx
        exact hx
  intro C b hf hs _ _
  by_contra he
  push Not at he
  let P9 := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let P10 := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let S (v : Fin 2) (b : Bool) : List (Bool ⊕ ℕ) :=
    (if v = 0 then [(.inl false), (.inr 4), (.inr 0), (.inr 1), (.inr 6), (.inr 7), (.inr 3), (.inr 5), (.inr 2), (.inr 8)] else [(.inr 4), (.inl false), (.inr 6), (.inr 1), (.inr 0), (.inr 3), (.inr 7), (.inr 8), (.inr 2), (.inr 5)]) ++ [if b then .inl false else .inr 4]
  let X (v : Fin 2) (y : Fin 9 → Bool) (i : Fin 10) : Bool :=
    Sum.elim id (fun k => (List.ofFn y).getD k false) ((S v b).getD i.val (.inl false))
  have hbound : ∀ (v : Fin 2) (s : Bool ⊕ ℕ), s ∈ S v b → ∀ k, s = .inr k → k < 9 := by
    intro v s hm k hsk
    subst s
    fin_cases v <;> cases b <;> simp [S] at hm <;> omega
  have hpin : ∀ v : Fin 2, (S v b).getD v.val (.inl false) = .inl false := by
    intro v
    fin_cases v <;> rfl
  have hh : b = true → ∀ v : Fin 2, (S v b).getD 10 (.inl false) = .inl false := by
    rintro rfl v
    fin_cases v <;> rfl
  have hlen : ∀ v : Fin 2, (S v b).length = 11 := by intro v; fin_cases v <;> rfl
  have hp9 : ∀ v y, P10 (X v y) = P9 y := by
    have get (y : Fin 9 → Bool) (k : ℕ) (h : k < 9) : (List.ofFn y).getD k false = y ⟨k,h⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    intro v y
    fin_cases v
    · change ((false && ((List.ofFn y).getD 4 false)) || (((List.ofFn y).getD 4 false) && ((List.ofFn y).getD 0 false)) || (((List.ofFn y).getD 0 false) && ((List.ofFn y).getD 1 false)) || (((List.ofFn y).getD 1 false) && ((List.ofFn y).getD 6 false)) || (((List.ofFn y).getD 6 false) && false) || (false && ((List.ofFn y).getD 7 false)) || (((List.ofFn y).getD 4 false) && ((List.ofFn y).getD 3 false)) || (((List.ofFn y).getD 0 false) && ((List.ofFn y).getD 5 false)) || (((List.ofFn y).getD 1 false) && ((List.ofFn y).getD 2 false)) || (((List.ofFn y).getD 6 false) && ((List.ofFn y).getD 8 false)) || (((List.ofFn y).getD 7 false) && ((List.ofFn y).getD 5 false)) || (((List.ofFn y).getD 5 false) && ((List.ofFn y).getD 8 false)) || (((List.ofFn y).getD 8 false) && ((List.ofFn y).getD 3 false)) || (((List.ofFn y).getD 3 false) && ((List.ofFn y).getD 2 false)) || (((List.ofFn y).getD 2 false) && ((List.ofFn y).getD 7 false))) = _
      simp only [get _ _ (by decide : 0 < 9), get _ _ (by decide : 1 < 9), get _ _ (by decide : 2 < 9),
        get _ _ (by decide : 3 < 9), get _ _ (by decide : 4 < 9), get _ _ (by decide : 5 < 9),
        get _ _ (by decide : 6 < 9), get _ _ (by decide : 7 < 9), get _ _ (by decide : 8 < 9), P9]
      simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm, Bool.and_comm]
      rw [Bool.and_comm (y 1) (y 0)]
    · change ((((List.ofFn y).getD 4 false) && false) || (false && ((List.ofFn y).getD 6 false)) || (((List.ofFn y).getD 6 false) && ((List.ofFn y).getD 1 false)) || (((List.ofFn y).getD 1 false) && ((List.ofFn y).getD 0 false)) || (((List.ofFn y).getD 0 false) && ((List.ofFn y).getD 4 false)) || (((List.ofFn y).getD 4 false) && ((List.ofFn y).getD 3 false)) || (false && ((List.ofFn y).getD 7 false)) || (((List.ofFn y).getD 6 false) && ((List.ofFn y).getD 8 false)) || (((List.ofFn y).getD 1 false) && ((List.ofFn y).getD 2 false)) || (((List.ofFn y).getD 0 false) && ((List.ofFn y).getD 5 false)) || (((List.ofFn y).getD 3 false) && ((List.ofFn y).getD 8 false)) || (((List.ofFn y).getD 8 false) && ((List.ofFn y).getD 5 false)) || (((List.ofFn y).getD 5 false) && ((List.ofFn y).getD 7 false)) || (((List.ofFn y).getD 7 false) && ((List.ofFn y).getD 2 false)) || (((List.ofFn y).getD 2 false) && ((List.ofFn y).getD 3 false))) = _
      simp only [get _ _ (by decide : 0 < 9), get _ _ (by decide : 1 < 9), get _ _ (by decide : 2 < 9),
        get _ _ (by decide : 3 < 9), get _ _ (by decide : 4 < 9), get _ _ (by decide : 5 < 9),
        get _ _ (by decide : 6 < 9), get _ _ (by decide : 7 < 9), get _ _ (by decide : 8 < 9), P9]
      simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm, Bool.and_comm]
      rw [Bool.and_comm (y 1) (y 0)]
  have hin : ∀ (v : Fin 2) (y : Fin 9 → Bool),
      (S v b).map (fun s => Sum.elim id (fun k => (List.ofFn y).getD k false) s) =
      List.ofFn (X v y) ++ [if b then X v y 0 && X v y 1 else X v y 0 || X v y 1] := by
    intro v y
    fin_cases v <;> cases b
    · change [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8] ++ [y 4] = [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8] ++ [false || y 4]
      simp
    · change [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8] ++ [false] = [false, y 4, y 0, y 1, y 6, y 7, y 3, y 5, y 2, y 8] ++ [false && y 4]
      simp
    · change [y 4, false, y 6, y 1, y 0, y 3, y 7, y 8, y 2, y 5] ++ [y 4] = [y 4, false, y 6, y 1, y 0, y 3, y 7, y 8, y 2, y 5] ++ [y 4 || false]
      simp
    · change [y 4, false, y 6, y 1, y 0, y 3, y 7, y 8, y 2, y 5] ++ [false] = [y 4, false, y 6, y 1, y 0, y 3, y 7, y 8, y 2, y 5] ++ [y 4 && false]
      simp
  have guard (g : Gate) :
      (letI := NestedCover.gateOpDecEq; if g.op = .not then g.inputs.take 1 else g.inputs) =
      GateOp.casesOn g.op g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs := by
    cases g with | mk op ins => cases op <;> rfl
  apply sparse C b hf hs
  · intro v K hK
    obtain ⟨D,hfan,hsize,hD⟩ := pin 9 (S v b) C K hf (hbound v) P9
      ⟨fun _ => false, fun _ => true, by decide⟩
      (fun y => (congrArg C.eval (hin v y)).trans ((he (X v y)).trans (hp9 v y))) (by
        intro i hi
        change ∃ w < (S v b).length, ∃ c : Bool, (S v b).getD w (.inl false) = .inl c ∧ w ∈ _
        rw [guard]
        rcases hK i hi with hv | ⟨hb,hw⟩
        · exact ⟨v.val, by rw [hlen]; omega, false, hpin v, hv⟩
        · exact ⟨10, by rw [hlen]; decide, false, hh hb v, hw⟩)
    by_contra hn
    exact cofactor ⟨D, hfan, by omega, hD⟩
  · intro x
    rw [he x]
    change P10 x = _
    change P10 x = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) || ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || (false))))))))))))))))
    simp [P10, Bool.or_assoc]
