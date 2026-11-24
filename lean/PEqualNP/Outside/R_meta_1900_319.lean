import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BicliqueBlockCost PEqualNP.Library.Peel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1900_319
    (cleanPairs : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ u v, G.Adj u v) → (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) → Monotone2 C → ¬ (∃ (j : Fin C.gates.length) (u v : Fin n), (C.gates.get j).op = .and ∧ ¬G.Adj u v ∧
        PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = true) → HasBlockCost G C.size)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit), let dirt (D : Circuit) := Set.ncard (Set.ofPred (fun t : Fin D.gates.length × Fin n × Fin n =>
      (D.gates.get t.1).op = .and ∧ ¬G.Adj t.2.1 t.2.2 ∧
      PEqualNP.EdgeOwnership.gateVal n D t.1 (PEqualNP.EdgeOwnership.pairInput t.2.1 t.2.2)  = true))
      (∃ u v, G.Adj u v) → (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) → IsMinimalMonoCircuit n C → (∀ D : Circuit, Monotone2 D → circuitFun n D = circuitFun n C → D.size = C.size → dirt C ≤ dirt D) → (∃ (j : Fin C.gates.length) (u v : Fin n), (C.gates.get j).op = .and ∧ ¬G.Adj u v ∧
        PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = true) → (∀ (v : Fin n) (K : Finset (Fin C.gates.length)), let W (x : Fin n → Bool) (w : ℕ) := (C.wires (List.ofFn (Function.update x v false))).getD w false
      (∀ j ∈ K, (∃ b : Bool, ∀ x, W x (n+j.val) = b) ∨
        ∃ w < n+j.val, ∀ x, W x (n+j.val) = W x w) → K.card ≤ (G.neighborSet v).ncard) → HasBlockCost G C.size) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size := by
  classical
  have absorb (n : ℕ) (S : List (Bool ⊕ ℕ)) (C : Circuit)
      (K : Finset (Fin C.gates.length)) (hC : Monotone2 C)
      (hS : ∀ s ∈ S, ∀ k, s = Sum.inr k → k < n)
      (F : (Fin n → Bool) → Bool) (hne : ∃ x y, F x ≠ F y)
      (hF : ∀ x, C.eval (S.map (fun s => Sum.elim id (fun k => (List.ofFn x).getD k false) s)) = F x)
      (hK : ∀ i ∈ K, (C.gates.get i).inputs = [] ∨
        ((C.gates.get i).op = .or ∧ ∃ w, (C.gates.get i).inputs = [w])) :
      ∃ D : Circuit, Monotone2 D ∧ D.size + K.card ≤ C.size ∧
        ∀ x, D.eval (List.ofFn x) = F x := by
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have eval_or (l : List Bool) : GateOp.or.eval l = l.any id := rfl
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
        (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
        (vs : List (Bool ⊕ ℕ)) (hlen : vs.length ≤ 2) (w : List Bool) :
        (∀ sym, elimGate op vs = Sum.inl sym →
          evalSym sym w = op.eval (vs.map fun s => evalSym s w) ∧
          (∀ k, sym = Sum.inr k → Sum.inr k ∈ vs)) ∧
        (∀ ng, elimGate op vs = Sum.inr ng →
          ng.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
          ng.inputs.length ≤ 2 ∧
          ng.op.eval (ng.inputs.map fun i => w.getD i false) = op.eval (vs.map fun s => evalSym s w)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl
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
                      exact ⟨Set.mem_insert_of_mem _ (Set.mem_singleton _), le_refl 2, by simp [evalSym, eval_or]⟩
    have elimRun_inv (n' : ℕ) (gs : List Gate)
        (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (st0 : List (Bool ⊕ ℕ)) (ngs0 : List Gate) (fl0 : List Bool)
        (hfan0 : ∀ g ∈ ngs0, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (hbd0 : ∀ s ∈ st0, ∀ k, s = Sum.inr k → k < n' + ngs0.length) :
        let res := gs.foldl (elimStep n') (st0, ngs0, fl0)
        (∃ stT ngsT flT, res.1 = st0 ++ stT ∧ res.2.1 = ngs0 ++ ngsT ∧ res.2.2 = fl0 ++ flT ∧
          stT.length = gs.length ∧ flT.length = gs.length) ∧
        res.2.1.length + res.2.2.count true = ngs0.length + fl0.count true + gs.length ∧
        (∀ g ∈ res.2.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
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
        have hgs : ∀ a ∈ gs, a.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ a.inputs.length ≤ 2 :=
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
          have hfan1 : ∀ a ∈ ngs0 ++ [ng], a.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ a.inputs.length ≤ 2 := by
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
        (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
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
      have hfan_take : ∀ g ∈ gs.take j, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
        fun g hg => hfan g (List.mem_of_mem_take hg)
      have hfan_drop : ∀ g ∈ gs.drop (j + 1), g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
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
      obtain ⟨_, _, hgate⟩ := elimRun_at_gate n C.gates hC S hS j.val j.isLt
      let pre := (C.gates.take j.val).foldl (elimStep n) (S, [], [])
      have erased : ∃ symbol, elimGate C.gates[j.val].op
          (C.gates[j.val].inputs.map fun i => pre.1.getD i (Sum.inl false)) = Sum.inl symbol := by
        rcases hK j hj with h | ⟨hop,w,h⟩
        · change C.gates[j.val].inputs = [] at h
          rw [h, List.map_nil]
          cases C.gates[j.val].op <;> exact ⟨_, rfl⟩
        · change C.gates[j.val].inputs = [w] at h
          change C.gates[j.val].op = .or at hop
          rw [h, hop]
          exact ⟨_,rfl⟩
      obtain ⟨sym,hs⟩ := erased
      exact (hgate sym hs).2
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

  let ev (s : Bool ⊕ ℕ) (xs : List Bool) : Bool := Sum.elim id (fun w => xs.getD w false) s
  let value (n : ℕ) (S : List (Bool ⊕ ℕ)) (C : Circuit) (x : Fin n → Bool) (j : ℕ) : Bool :=
    (C.wires (S.map fun s => ev s (List.ofFn x))).getD j false
  let step (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have extends_w (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp,rfl⟩
    | cons g gs ih =>
      obtain ⟨t,ht,hl⟩ := ih (step w g)
      exact ⟨_ :: t,by simpa [step] using ht,by simp [hl]⟩
  have len_w (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    obtain ⟨t,h,ht⟩ := extends_w gs w
    rw [h,List.length_append,ht]

  have pref (C : Circuit) (A : List Bool) (j : ℕ) (hj : j ≤ C.gates.length) (u : ℕ)
      (hu : u < A.length + j) :
      (C.wires A).getD u false = ((C.gates.take j).foldl step A).getD u false := by
    change (C.gates.foldl step A).getD u false = _
    conv_lhs => rw [←List.take_append_drop j C.gates,List.foldl_append]
    obtain ⟨t,ht,_⟩ := extends_w (C.gates.drop j) ((C.gates.take j).foldl step A)
    rw [ht, List.getD_append _ _ _ _ (by rwa [len_w, List.length_take_of_le hj])]

  have current (C : Circuit) (A : List Bool) (j : Fin C.gates.length) :
      (C.wires A).getD (A.length+j.val) false = (C.gates.get j).op.eval
        ((C.gates.get j).inputs.map fun i => ((C.gates.take j.val).foldl step A).getD i false) := by
    rw [pref C A (j.val+1) j.isLt _ (by omega), List.take_succ_eq_append_getElem j.isLt, List.foldl_append]
    change (((C.gates.take j.val).foldl step A) ++ [_]).getD _ false = _
    rw [show A.length+j.val = ((C.gates.take j.val).foldl step A).length by
        rw [len_w,List.length_take_of_le (Nat.le_of_lt j.isLt)]]
    simp [List.getD_eq_getElem?_getD]

  have save (n : ℕ) (S : List (Bool ⊕ ℕ)) (C : Circuit) (K : Finset (Fin C.gates.length))
      (hC : Monotone2 C) (bd : ∀ s ∈ S, ∀ k, s = Sum.inr k → k < n)
      (nonc : ∃ x y, value n S C x C.output ≠ value n S C y C.output)
      (red : ∀ j ∈ K, (∃ b : Bool, ∀ x, value n S C x (S.length+j.val) = b) ∨
        (∃ w < S.length+j.val, ∀ x, value n S C x (S.length+j.val) = value n S C x w)) :
      ∃ D : Circuit, Monotone2 D ∧ D.size+K.card ≤ C.size ∧
        ∀ x, D.eval (List.ofFn x) = value n S C x C.output := by
    classical
    let out (s : Bool ⊕ ℕ) : Gate := Sum.elim (fun b => if b then ⟨.and,[]⟩ else ⟨.or,[]⟩) (fun w => ⟨.or,[w]⟩) s
    let A (x : Fin n → Bool) := S.map fun s => ev s (List.ofFn x)
    have al (x : Fin n → Bool) : (A x).length = S.length := by simp [A]
    have opts (j : Fin C.gates.length) (hj : j ∈ K) : ∃ s : Bool ⊕ ℕ, ∀ x,
        let w := (C.gates.take j.val).foldl step (A x)
        (out s).op.eval ((out s).inputs.map fun i => w.getD i false) = value n S C x (S.length+j.val) := by
      rcases red j hj with ⟨b,hb⟩ | ⟨u,hu,hw⟩
      · refine ⟨.inl b, fun x => ?_⟩
        rw [hb x]
        cases b <;> rfl
      · refine ⟨.inr u,fun x => ?_⟩
        rw [hw x]
        change (((C.gates.take j.val).foldl step (A x)).getD u false || false) = _
        rw [Bool.or_false]
        exact (pref C (A x) j.val j.isLt.le u (by rwa [al])).symm
    let g (j : Fin C.gates.length) : Gate := if h : j ∈ K then out (opts j h).choose else C.gates.get j
    let D : Circuit := ⟨List.ofFn g,C.output⟩
    have lenD : D.gates.length = C.gates.length := List.length_ofFn
    let em : Fin C.gates.length ↪ Fin D.gates.length :=
      ⟨Fin.cast lenD.symm,fun _ _ h => Fin.ext (congrArg (fun z : Fin D.gates.length => z.val) h)⟩
    have getD (j : Fin C.gates.length) : D.gates.get (em j) = g j := List.getElem_ofFn ..
    have hfD : Monotone2 D := by
      intro e he
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
      by_cases h : j ∈ K
      · rw [show g j = out (opts j h).choose by simp [g,h]]
        cases (opts j h).choose with
        | inl b => cases b <;> simp [out]
        | inr w => simp [out]
      · rw [show g j = C.gates.get j by simp [g,h]]
        exact hC _ (List.get_mem _ _)
    have eqp (x : Fin n → Bool) (k : ℕ) (hk : k ≤ C.gates.length) :
        (D.gates.take k).foldl step (A x) = (C.gates.take k).foldl step (A x) := by
      induction k with
      | zero => rfl
      | succ k ih =>
        have hk' : k < C.gates.length := hk
        let j : Fin C.gates.length := ⟨k,hk'⟩
        rw [List.take_succ_eq_append_getElem (show k < D.gates.length by omega), List.take_succ_eq_append_getElem hk',
          List.foldl_append,List.foldl_append,List.foldl_cons,List.foldl_cons,List.foldl_nil,List.foldl_nil,
          ih hk'.le]
        change step _ (D.gates.get (em j)) = step _ (C.gates.get j)
        rw [getD]
        by_cases h : j ∈ K
        · rw [show g j = out (opts j h).choose by simp [g,h]]
          dsimp only [step]
          congr 2
          have hh := (opts j h).choose_spec x
          calc
            _ = value n S C x (S.length+j.val) := hh
            _ = _ := by rw [← al x]; exact current C (A x) j
        · simp [g,h]
    have hsem (x : Fin n → Bool) : D.eval (A x) = value n S C x C.output := by
      have z := eqp x C.gates.length le_rfl
      rw [←lenD,List.take_length,lenD,List.take_length] at z
      exact congrArg (fun w : List Bool => w.getD C.output false) z
    have hk' : ∀ j ∈ K.map em, (D.gates.get j).inputs = [] ∨
        ((D.gates.get j).op = .or ∧ ∃ w, (D.gates.get j).inputs = [w]) := by
      intro i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
      rw [getD, show g j = out (opts j hj).choose by simp [g,hj]]
      cases (opts j hj).choose with
      | inl b => cases b <;> exact .inl rfl
      | inr w => exact .inr ⟨rfl,w,rfl⟩
    obtain ⟨E,hE,hs,he⟩ := absorb n S D (K.map em) hfD bd _ nonc hsem hk'
    exact ⟨E,hE,by change E.gates.length + K.card ≤ C.gates.length; change E.gates.length + (K.map em).card ≤ D.gates.length at hs; simpa only [Finset.card_map, lenD] using hs, he⟩

  let values {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) := (C.wires (List.ofFn x)).getD w false

  let base (n : ℕ) (pin : Option (Fin n)) : List (Bool ⊕ ℕ) :=
    List.ofFn (fun i : Fin n => if pin = some i then .inl false else .inr i.val)

  have base_length (n : ℕ) (pin : Option (Fin n)) : (base n pin).length = n := List.length_ofFn

  have base_valid {n : ℕ} (pin : Option (Fin n)) :
      ∀ s ∈ base n pin, ∀ k, s = Sum.inr k → k < n := by
    intro s hs k he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
    split at he <;> rename_i hi
    · cases he
    · obtain rfl := Sum.inr.inj he
      exact i.isLt

  let atPin {n : ℕ} (pin : Option (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
    pin.elim x (fun i => Function.update x i false)

  have base_eval {n : ℕ} (pin : Option (Fin n)) (x : Fin n → Bool) :
      (base n pin).map (fun s => ev s (List.ofFn x)) = List.ofFn (atPin pin x) := by
    dsimp only [base]
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    cases pin with
    | none => simp [ev, atPin, i.isLt]
    | some j =>
      by_cases h : i = j
      · subst i
        simp [ev, atPin]
      · simp [ev, atPin, h, Ne.symm h, i.isLt]

  have same_value {n : ℕ} (pin : Option (Fin n)) (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
      value n (base n pin) C x w = values C (atPin pin x) w := by
    dsimp only [value, values]
    rw [base_eval]

  have cfun (n : ℕ) (D : Circuit) (x : Fin n → Bool) : circuitFun n D x = (D.wires (List.ofFn x)).getD D.output false := rfl

  have savePin {n : ℕ} (pin : Option (Fin n)) (C : Circuit)
      (K : Finset (Fin C.gates.length)) (hC : Monotone2 C)
      (hnc : ∃ x y, circuitFun n C (atPin pin x) ≠ circuitFun n C (atPin pin y))
      (hr : ∀ j ∈ K, (∃ b : Bool, ∀ x, values C (atPin pin x) (n+j.val) = b) ∨
        ∃ w < n+j.val, ∀ x, values C (atPin pin x) (n+j.val) = values C (atPin pin x) w) :
      ∃ D, Monotone2 D ∧ D.size + K.card ≤ C.size ∧
        ∀ x, D.eval (List.ofFn x) = circuitFun n C (atPin pin x) := by
    have hin : ∃ x y, value n (base n pin) C x C.output ≠
        value n (base n pin) C y C.output := by
      obtain ⟨x,y,hxy⟩ := hnc
      exact ⟨x,y,by simpa only [same_value, values, cfun] using hxy⟩
    have hRed := save n (base n pin) C K hC (base_valid pin) hin
      (by simpa only [same_value, base_length] using hr)
    simpa only [same_value, values, cfun] using hRed


  have prune : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (K : Finset (Fin C.gates.length)), let W (x : Fin n → Bool) (w : ℕ) := (C.wires (List.ofFn (Function.update x v false))).getD w false
        Monotone2 C → (∃ x y, W x C.output ≠ W y C.output) → (∀ j ∈ K, (∃ b : Bool, ∀ x, W x (n+j.val) = b) ∨
          ∃ w < n+j.val, ∀ x, W x (n+j.val) = W x w) →
          ∃ D : Circuit, Monotone2 D ∧ D.size + K.card ≤ C.size ∧ ∀ x, D.eval (List.ofFn x) = W x C.output := by
    intro n C v K W hm hn hr
    exact savePin (some v) C K hm hn hr

  have extend {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (c : ℕ)
      (hc : HasBlockCost (delVerts G {v}) c) :
      HasBlockCost G (c + (G.neighborSet v).ncard + 1) := by
    obtain ⟨F,hF,hcost⟩ := hc
    let N := (G.neighborSet v).toFinset
    let B : Block n := ({v}, N)
    have cardN : N.card = (G.neighborSet v).ncard := (Set.ncard_eq_toFinset_card' _).symm
    have liftB (b : Block n) (hb : IsBlock (delVerts G {v}) b) : IsBlock G b :=
      ⟨hb.1,hb.2.1,hb.2.2.1,fun a ha w hw => (hb.2.2.2 a ha w hw).1⟩
    by_cases ne : N.Nonempty
    · have hB : IsBlock G B := by
        refine ⟨Finset.disjoint_singleton_left.mpr ?_,Finset.singleton_nonempty v,ne,?_⟩
        · change v ∉ (G.neighborSet v).toFinset
          simp
        · rintro a ha b hb
          have e : a = v := Finset.mem_singleton.mp ha
          subst a
          exact Set.mem_toFinset.mp hb
      refine ⟨insert B F, ⟨?_,?_⟩,?_⟩
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hB
        · exact liftB b (hF.1 b hb)
      · intro a b hab
        by_cases ha : a = v
        · subst a
          exact ⟨B,Finset.mem_insert_self _ _,Or.inl ⟨Finset.mem_singleton_self _, Set.mem_toFinset.mpr hab⟩⟩
        by_cases hb : b = v
        · subst b
          exact ⟨B,Finset.mem_insert_self _ _,Or.inr ⟨Finset.mem_singleton_self _, Set.mem_toFinset.mpr hab.symm⟩⟩
        obtain ⟨t,ht,htab⟩ := hF.2 a b ⟨hab,by simpa using ha,by simpa using hb⟩
        exact ⟨t, Finset.mem_insert_of_mem ht, htab⟩
      · by_cases hmem : B ∈ F
        · rw [Finset.insert_eq_of_mem hmem]; omega
        have cb : blockCost B = N.card := by change ({v} : Finset (Fin n)).card + N.card - 1 = _; simp
        change (∑ b ∈ insert B F, blockCost b) + ((insert B F).card - 1) ≤ _
        change (∑ b ∈ F, blockCost b) + (F.card - 1) ≤ c at hcost
        rw [Finset.sum_insert hmem, Finset.card_insert_of_notMem hmem, cb]
        omega
    · refine ⟨F,⟨fun b hb => liftB b (hF.1 b hb),?_⟩,by omega⟩
      intro a b hab
      apply hF.2
      refine ⟨hab,?_,?_⟩
      · intro ha
        have hv : a = v := Finset.mem_singleton.mp ha
        exact ne ⟨b,Set.mem_toFinset.mpr (hv ▸ hab)⟩
      · intro hb
        have hv : b = v := Finset.mem_singleton.mp hb
        exact ne ⟨a,Set.mem_toFinset.mpr (hv ▸ hab.symm)⟩
  intro n G C hE h4 hM he
  have cycle : (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) := by
    intro a b c d h1 h2 h3 h4'
    by_contra! hn
    exact h4 a b c d h1.ne hn.1 h4'.ne.symm h2.ne hn.2 h3.ne h1 h2 h3 h4'
  clear h4
  generalize hsize : C.size = k
  induction k using Nat.strong_induction_on generalizing n G C with
  | ind k ih =>
    let dirt (D : Circuit) := Set.ncard (Set.ofPred (fun t : Fin D.gates.length × Fin n × Fin n =>
      (D.gates.get t.1).op = .and ∧ ¬G.Adj t.2.1 t.2.2 ∧
      PEqualNP.EdgeOwnership.gateVal n D t.1 (PEqualNP.EdgeOwnership.pairInput t.2.1 t.2.2)  = true))
    suffices aux : ∀ (m : ℕ) (D : Circuit), D.size = k → dirt D = m → Monotone2 D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) → HasBlockCost G k by
      exact aux (dirt C) C hsize rfl hM he
    intro m
    induction m using Nat.strong_induction_on with
    | ind m sec =>
      intro C hsize hm hM he
      by_cases optimal : ∀ D : Circuit, Monotone2 D → circuitFun n D = circuitFun n C → D.size = C.size → dirt C ≤ dirt D
      ·
        rw [←hsize]
        by_cases mn : IsMinimalMonoCircuit n C
        · by_cases b : (∃ (j : Fin C.gates.length) (u v : Fin n), (C.gates.get j).op = .and ∧ ¬G.Adj u v ∧
            PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = true)
          · by_cases cap : (∀ (v : Fin n) (K : Finset (Fin C.gates.length)), let W (x : Fin n → Bool) (w : ℕ) := (C.wires (List.ofFn (Function.update x v false))).getD w false
          (∀ j ∈ K, (∃ b : Bool, ∀ x, W x (n+j.val) = b) ∨
            ∃ w < n+j.val, ∀ x, W x (n+j.val) = W x w) → K.card ≤ (G.neighborSet v).ncard)
            · exact residual n G C hE cycle he mn optimal b cap
            push Not at cap
            obtain ⟨v,K,ne⟩ := cap
            dsimp only at ne
            push Not at ne
            obtain ⟨hr,high⟩ := ne
            let H := delVerts G {v}
            have ee : ∀ x, C.eval (List.ofFn (Function.update x v false)) = true ↔
                ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true := by
              intro x
              rw [he]
              constructor
              · rintro ⟨a,b,hab,ha,hb⟩
                have av : a ≠ v := by rintro rfl; simp at ha
                have bv : b ≠ v := by rintro rfl; simp at hb
                exact ⟨a,b,⟨hab,by simpa using av,by simpa using bv⟩,by simpa [Function.update,av] using ha,
                  by simpa [Function.update,bv] using hb⟩
              · rintro ⟨a,b,hab,ha,hb⟩
                exact ⟨a,b,hab.1,by simpa [Function.update, show a ≠ v by simpa using hab.2.1] using ha,
                  by simpa [Function.update, show b ≠ v by simpa using hab.2.2] using hb⟩
            by_cases eH : ∃ a b, H.Adj a b
            · have nonc : ∃ x y, C.eval (List.ofFn (Function.update x v false)) ≠
                  C.eval (List.ofFn (Function.update y v false)) := by
                obtain ⟨a,b,hab⟩ := eH
                refine ⟨fun _ => false,fun _ => true,?_⟩
                have ht := (ee (fun _ => true)).mpr ⟨a,b,hab,rfl,rfl⟩
                rw [ht]; intro h
                obtain ⟨u,w,_,huw,_⟩ := (ee _).mp h
                contradiction
              obtain ⟨D,md,sz,evalD⟩ := prune n C v K hM nonc hr
              have works : ∀ x, D.eval (List.ofFn x) = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true := by
                intro x; rw [evalD x]; exact ee x
              have cy : ∀ a b c d, H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a → a = c ∨ b = d :=
                fun a b c d ab bc cd da => cycle a b c d ab.1 bc.1 cd.1 da.1
              have hsmall := ih D.size (by omega) n H D eH md works cy rfl
              obtain ⟨F,hF,hs⟩ := extend G v D.size hsmall
              exact ⟨F,hF,by omega⟩
            · have empty : HasBlockCost H 0 := by
                refine ⟨∅,⟨by simp,?_⟩,by change (∑ b ∈ (∅ : Finset (Block n)), blockCost b) + ((∅ : Finset (Block n)).card - 1) ≤ 0; simp⟩
                intro a b ab; exact (eH ⟨a,b,ab⟩).elim
              obtain ⟨F,hF,hs⟩ := extend G v 0 empty
              have hK := Finset.card_le_univ K
              simp only [Fintype.card_fin] at hK
              change K.card ≤ C.size at hK
              exact ⟨F,hF,by omega⟩
          · exact cleanPairs n G C hE cycle he hM b
        · have hm : ¬∀ D : Circuit, Monotone2 D → circuitFun n D = circuitFun n C → C.size ≤ D.size := by
            intro hm; exact mn ⟨hM,hm⟩
          push Not at hm
          obtain ⟨D,hd,eqd,less⟩ := hm
          have ed : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
            intro x; rw [show D.eval (List.ofFn x) = C.eval (List.ofFn x) from congrFun eqd x]; exact he x
          obtain ⟨F,hF,hs⟩ := ih D.size (by omega) n G D hE hd ed cycle rfl
          exact ⟨F,hF,by omega⟩
      · push Not at optimal
        obtain ⟨D,dm,eqd,sz,improves⟩ := optimal
        have ed : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
          intro x; rw [show D.eval (List.ofFn x) = C.eval (List.ofFn x) from congrFun eqd x]; exact he x
        exact sec (dirt D) (by omega) D (by omega) rfl dm ed
