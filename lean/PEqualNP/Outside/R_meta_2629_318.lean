import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2629_318
  (localElim : ∀ (n : ℕ) (C : Circuit) (v : Fin n),
    let f := circuitFun n C
    let rd := C.gates.filter fun g => g.inputs.contains v.val
    IsMinimalCircuit n C → (∀ pre g post, C.gates = pre ++ g :: post →
      (g.op = .not ∧ ∃ a < n + pre.length, g.inputs = [a]) ∨
        ((g.op = .and ∨ g.op = .or) ∧ ∃ a < n + pre.length,
          ∃ b < n + pre.length, a ≠ b ∧ g.inputs = [a,b])) →
    (∃ x y, f (Function.update x v false) ≠ f (Function.update y v false)) →
    rd.length = 2 → (∃ g ∈ rd, g.op = .not) →
    (∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) ∨ (∃ p : Fin C.gates.length, (C.gates.get p).op = .not ∧ (C.gates.get p).inputs = [v.val] ∧
        (∃ g ∈ C.gates, g.op = .or ∧ v.val ∈ g.inputs) ∧
        ∃ r : Fin C.gates.length, (C.gates.get r).op = .and ∧ n + p.val ∈ (C.gates.get r).inputs ∧
        ∀ t : Fin C.gates.length, n + p.val ∈ (C.gates.get t).inputs → t = r))
  (mixed : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (C : Circuit) (v : Fin n), let f := NestedCover.graphFun G A
    let rd (z : Fin n) := C.gates.filter fun g => g.inputs.contains z.val
    (∀ z ∉ A, (G.neighborSet z).ncard = 3) →
    (∀ (z : Fin n) (p : G.Walk z z), p.IsCycle → 7 ≤ p.length) →
    (∀ a b, G.Adj a b → a ∉ A) → circuitFun n C = f → IsMinimalCircuit n C →
    (∀ z ∉ A, 2 ≤ (rd z).length ∧ (rd z).length ≤ 3 ∧
       ((rd z).length = 3 → ∀ g ∈ rd z, g.op = .or)) →
    2 * (G.indepNum - A.card + (Aᶜ.filter (fun z => (rd z).length = 3)).card +
       (C.gates.filter fun g => g.op.eval [false]).length) < Aᶜ.card →
    v ∉ A → (rd v).length = 2 → (∃ p : Fin C.gates.length, (C.gates.get p).op = .not ∧ (C.gates.get p).inputs = [v.val] ∧
        (∃ g ∈ C.gates, g.op = .or ∧ v.val ∈ g.inputs) ∧
        ∃ r : Fin C.gates.length, (C.gates.get r).op = .and ∧ n + p.val ∈ (C.gates.get r).inputs ∧
        ∀ t : Fin C.gates.length, n + p.val ∈ (C.gates.get t).inputs → t = r) →
    ∃ w ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x w false)) s) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  have normalise : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
    (∃ x y, circuitFun n C x ≠ circuitFun n C y) →
    ∃ D : Circuit,
      D.gates = C.gates.map (fun g => ⟨g.op,g.inputs.take (bif g.op.eval [false] then 1 else 2)⟩) ∧
      D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
      (∀ pre g post, D.gates = pre ++ g :: post →
        (g.op = .not ∧ ∃ a < n + pre.length, g.inputs = [a]) ∨
        ((g.op = .and ∨ g.op = .or) ∧ ∃ a < n + pre.length,
          ∃ b < n + pre.length, a ≠ b ∧ g.inputs = [a,b])) := by
    intro n C hmin hne
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
    let trim (g : Gate) : Gate := ⟨g.op, g.inputs.take (bif g.op.eval [false] then 1 else 2)⟩

    let Good (m : ℕ) (g : Gate) : Prop :=
      (g.op = .not ∧ ∃ a < m, g.inputs = [a]) ∨
      ((g.op = .and ∨ g.op = .or) ∧ ∃ a < m, ∃ b < m, a ≠ b ∧ g.inputs = [a,b])

    have kept {g : Gate} {st : List (Bool ⊕ ℕ)} {ng : Gate}
        (fan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (hk : elimGate g.op (g.inputs.map fun i => st.getD i (Sum.inl false)) = Sum.inr ng) :
        Good st.length (trim g) := by
      have bound (i j : ℕ) (h : st.getD i (.inl false) = .inr j) : i < st.length := by
        by_contra! hh
        rw [List.getD_eq_default _ _ hh] at h
        cases h
      obtain ⟨op,ins⟩ := g
      have hr : op = .and ∨ op = .or ∨ op = .not := fan.1
      have hl : ins.length ≤ 2 := fan.2
      change elimGate op (ins.map fun i => st.getD i (.inl false)) = .inr ng at hk
      rcases hr with rfl | rfl | rfl
      · cases ins with
        | nil => cases hk
        | cons a us =>
          cases us with
          | nil => cases hk
          | cons b rest =>
            have er : rest = [] := by
              apply List.eq_nil_of_length_eq_zero
              simp only [List.length_cons] at hl
              omega
            subst rest
            cases ea : st.getD a (.inl false) with
            | inl x =>
              cases x <;> simp [elimGate,elimAnd,ea,-List.getD_eq_getElem?_getD] at hk
            | inr i =>
              cases eb : st.getD b (.inl false) with
              | inl y =>
                cases y <;> simp [elimGate,elimAnd,ea,eb,-List.getD_eq_getElem?_getD] at hk
              | inr j =>
                have hab : a ≠ b := by
                  rintro rfl
                  have eqij := ea.symm.trans eb
                  cases eqij
                  simp [elimGate,elimAnd,ea,-List.getD_eq_getElem?_getD] at hk
                exact Or.inr ⟨by simp [trim],a,bound a i ea,b,bound b j eb,hab,rfl⟩
      · cases ins with
        | nil => cases hk
        | cons a us =>
          cases us with
          | nil => cases hk
          | cons b rest =>
            have er : rest = [] := by
              apply List.eq_nil_of_length_eq_zero
              simp only [List.length_cons] at hl
              omega
            subst rest
            cases ea : st.getD a (.inl false) with
            | inl x =>
              cases x <;> simp [elimGate,elimOr,ea,-List.getD_eq_getElem?_getD] at hk
            | inr i =>
              cases eb : st.getD b (.inl false) with
              | inl y =>
                cases y <;> simp [elimGate,elimOr,ea,eb,-List.getD_eq_getElem?_getD] at hk
              | inr j =>
                have hab : a ≠ b := by
                  rintro rfl
                  have eqij := ea.symm.trans eb
                  cases eqij
                  simp [elimGate,elimOr,ea,-List.getD_eq_getElem?_getD] at hk
                exact Or.inr ⟨by simp [trim],a,bound a i ea,b,bound b j eb,hab,rfl⟩
      · cases ins with
        | nil => cases hk
        | cons a rest =>
          cases ea : st.getD a (.inl false) with
          | inl x =>
            cases x <;> simp [elimGate,elimNot,ea,-List.getD_eq_getElem?_getD] at hk
          | inr i => exact Or.inl ⟨rfl,a,bound a i ea,rfl⟩

    have trim_step (g : Gate)
        (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (w : List Bool) : step w (trim g) = step w g := by
      cases g with
      | mk op ins =>
        have hop : op = .and ∨ op = .or ∨ op = .not := h.1
        have hl : ins.length ≤ 2 := h.2
        rcases hop with rfl | rfl | rfl
        · change _ ++ [GateOp.and.eval ((ins.take 2).map _)] = _
          rw [List.take_of_length_le hl]
        · change _ ++ [GateOp.or.eval ((ins.take 2).map _)] = _
          rw [List.take_of_length_le hl]
        · cases ins <;> rfl

    have trim_fold (gs : List Gate)
        (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (w : List Bool) : (gs.map trim).foldl step w = gs.foldl step w := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [trim_step g (h g List.mem_cons_self), ih (fun k hk => h k (List.mem_cons_of_mem g hk)) _]
    have hC := hmin.1
    let S : List (Bool ⊕ ℕ) := (List.range n).map Sum.inr
    have hslen : S.length = n := by simp [S]
    have hS : ∀ s ∈ S, ∀ k, s = Sum.inr k → k < n := by
      intro s hs k hk
      obtain ⟨i, hi, hi'⟩ := List.mem_map.mp hs
      subst s
      cases hi'
      exact List.mem_range.mp hi
    have base (x : Fin n → Bool) :
        S.map (fun s => evalSym s (List.ofFn x)) = List.ofFn x := by
      apply List.ext_getElem
      · simp [S]
      · intro j hj hj'
        simp [S,evalSym,List.getD_eq_getElem _ _ hj', -List.getD_eq_getElem?_getD]
    have hinv := elimRun_inv n C.gates hC S [] [] (by simp) (by simpa using hS)
    obtain ⟨⟨stT, _, flT, hst, _, hfl, hsl, hfl_len⟩, hcnt, hfan, _, hsem⟩ := hinv
    let res := C.gates.foldl (elimStep n) (S, [], [])
    have hval (x : Fin n → Bool) :
        evalSym (res.1.getD C.output (Sum.inl false)) (res.2.1.foldl step (List.ofFn x)) = circuitFun n C x := by
      have agree (i : ℕ) (hi : i < S.length) :
          evalSym (S.getD i (Sum.inl false)) (List.ofFn x) = (List.ofFn x).getD i false := by
        have hmap := congrArg (fun l : List Bool => l.getD i false) (base x)
        rw [List.getD_eq_getElem _ _ hi]
        simpa only [List.getD_eq_getElem _ _ (show i < (S.map _).length by simpa using hi), List.getElem_map] using hmap
      by_cases hout : C.output < res.1.length
      · exact hsem (List.ofFn x) (List.ofFn x) (List.length_ofFn) (by simp [hslen]) agree C.output hout
      · have hlen : res.1.length = n + C.gates.length := by rw [show res.1 = _ from hst, List.length_append, hsl, hslen]
        have hwire := wires_len C.gates (List.ofFn x)
        change evalSym (res.1.getD C.output (Sum.inl false)) _ = (C.gates.foldl step (List.ofFn x)).getD C.output false
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hout), List.getD_eq_default _ _ (by simp only [List.length_ofFn] at hwire; omega : (C.gates.foldl step (List.ofFn x)).length ≤ C.output)]
        rfl
    have zero : res.2.2.count true = 0 := by
      cases ho : res.1.getD C.output (.inl false) with
      | inl b =>
        obtain ⟨x,y,hxy⟩ := hne
        have hx := hval x
        have hy := hval y
        rw [ho] at hx hy
        exact (hxy (hx.symm.trans hy)).elim
      | inr k =>
        have hcompute : circuitFun n ⟨res.2.1,k⟩ = circuitFun n C := by
          funext x
          have hv := hval x
          rw [ho] at hv
          exact hv
        have hsize := hmin.2 ⟨res.2.1,k⟩ hfan hcompute
        change C.gates.length ≤ res.2.1.length at hsize
        change res.2.1.length + res.2.2.count true = _ at hcnt
        simp only [List.length_nil, List.count_nil, Nat.zero_add] at hcnt
        omega
    have shape (j : ℕ) (hj : j < C.gates.length) : Good (n+j) (trim C.gates[j]) := by
      let pre := (C.gates.take j).foldl (elimStep n) (S, [], [])
      let vs := C.gates[j].inputs.map fun i => pre.1.getD i (Sum.inl false)
      obtain ⟨hlen,_,hmark⟩ := elimRun_at_gate n C.gates hC S hS j hj
      cases hs : elimGate C.gates[j].op vs with
      | inr ng =>
        have hgood := kept (st := pre.1) (hC _ (List.getElem_mem hj)) hs
        change pre.1.length = S.length + j at hlen
        rwa [hlen,hslen] at hgood
      | inl sym =>
        have hm := (hmark sym hs).2
        have hflen : res.2.2.length = C.gates.length := by rw [show res.2.2 = _ from hfl,List.nil_append,hfl_len]
        have hj' : j < res.2.2.length := by rwa [hflen]
        change res.2.2.getD j false = true at hm
        rw [List.getD_eq_getElem _ _ hj'] at hm
        have hpos : true ∈ res.2.2 := hm ▸ List.getElem_mem hj'
        exact (List.count_eq_zero.mp zero hpos).elim
    refine ⟨⟨C.gates.map trim,C.output⟩,rfl,by exact List.length_map trim,?_,?_⟩
    · funext x
      change (((C.gates.map trim).foldl step (List.ofFn x)).getD C.output false) = _
      rw [trim_fold _ hC]
      rfl
    · intro pre g post h
      change C.gates.map trim = pre ++ g :: post at h
      have hj : pre.length < C.gates.length := by have hh := congrArg List.length h; simp at hh; omega
      have he : (C.gates.map trim)[pre.length]? = some g := by rw [h]; simp
      rw [List.getElem?_eq_getElem (by simpa using hj),List.getElem_map,Option.some.injEq] at he
      exact he ▸ shape pre.length hj

  let portRD (g : Gate) : List ℕ := List.take (bif g.op.eval [false] then 1 else 2) g.inputs

  have indepBranch {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit)
      (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
      (unmarked : ∀ v w, G.Adj v w → v ∉ A) (edge : ∃ v w, G.Adj v w)
      (fan : FanInTwo C) (computes : circuitFun n C = NestedCover.graphFun G A)
      (minimal : ∀ s, HasCircuitSize n (NestedCover.graphFun G A) s → C.size ≤ s)
      (reads : Fin n → ℕ)
      (hr : reads = fun a => (C.gates.filter fun g => (portRD g).contains a.val).length)
      (hread : ∀ a ∉ A, 2 ≤ reads a ∧ reads a ≤ 3)
      (I : Finset (Fin n)) (hsub : I ⊆ Aᶜ) (hind : ∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v)
      (budget : Aᶜ.card ≤ 2*(I.card + (Aᶜ.filter (fun v => reads v = 3)).card +
        (C.gates.filter fun g => g.op.eval [false]).length)) :
      ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧
        HasCircuitSize n (fun x => NestedCover.graphFun G A (Function.update x v false)) s := by
    classical
    have evAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have evOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have evNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
    have evSize (K : Circuit) : K.size = K.gates.length := rfl
    have evCirc (K : Circuit) (w : List Bool) : K.eval w = (K.wires w).getD K.output false := rfl
    have evGraph {m : ℕ} (K : SimpleGraph (Fin m)) [DecidableRel K.Adj] (M : Finset (Fin m))
        (x : Fin m → Bool) : NestedCover.graphFun K M x =
          (decide (∃ a ∈ M, x a = true) || decide (∃ a b, K.Adj a b ∧ x a = true ∧ x b = true)) := rfl
    let F (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

    have wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

    let OkGate (g : Gate) : Prop :=
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

    have ok_of_fan (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) (g : Gate) (hg : g ∈ C.gates) :
        OkGate g := by
      obtain ⟨h1, h2⟩ := h g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      exact ⟨h1, h2⟩

    have evalRd (g : Gate) (hg : OkGate g) (f f' : ℕ → Bool) (h : ∀ i ∈ portRD g, f i = f' i) :
        g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
      obtain ⟨hop, hl⟩ := hg
      rcases hop with hop | hop | hop
      · have : portRD g = g.inputs := by
          simp only [portRD, hop, evAnd,evOr,evNot]
          exact List.take_of_length_le (by simpa using hl)
        rw [this] at h
        rw [List.map_congr_left h]
      · have : portRD g = g.inputs := by
          simp only [portRD, hop, evAnd,evOr,evNot]
          exact List.take_of_length_le (by simpa using hl)
        rw [this] at h
        rw [List.map_congr_left h]
      · rw [hop]
        simp only [portRD, hop, evAnd,evOr,evNot] at h
        cases hin : g.inputs with
        | nil => simp
        | cons a t =>
          rw [hin] at h
          simp only [List.map_cons]
          rw [h a (by simp)]
          simp [evAnd,evOr,evNot]

    have fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        simp only [List.foldl_cons]
        rw [ih]
        simp only [F, List.length_append, List.length_cons, List.length_nil]
        omega

    let dl (w i : ℕ) : ℕ := if i < w then i else i - 1

    let rg (w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (dl w)⟩

    have F_rg (Q Q' : List Bool) (w : ℕ) (g : Gate) (hg : OkGate g)
        (h : ∀ i ∈ portRD g, Q'.getD (dl w i) false = Q.getD i false) :
        (rg w g).op.eval ((rg w g).inputs.map fun i => Q'.getD i false)
          = g.op.eval (g.inputs.map fun i => Q.getD i false) := by
      simp only [rg, List.map_map]
      exact evalRd g hg _ _ h

    have stageA (w : ℕ) (A : List Gate) (hA : ∀ g ∈ A, OkGate g ∧ w ∉ portRD g) :
        ∀ Q : List Bool, Q.length + A.length ≤ w → (A.map (rg w)).foldl F Q = A.foldl F Q := by
      induction A with
      | nil => intro Q _; rfl
      | cons g A ih =>
        intro Q hQ
        simp only [List.map_cons, List.foldl_cons]
        have hg := hA g (by simp)
        have hF : F Q (rg w g) = F Q g := by
          unfold F
          rw [F_rg Q Q w g hg.1]
          intro i hi
          have hne : i ≠ w := fun h => hg.2 (h ▸ hi)
          simp only [List.length_cons] at hQ
          by_cases hiw : i < w
          · simp [dl, hiw]
          · simp only [dl, hiw, ite_false]
            rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        rw [hF]
        apply ih (fun g' hg' => hA g' (by simp [hg']))
        simp only [F, List.length_append, List.length_cons, List.length_nil, List.length_cons] at hQ ⊢
        omega

    have key (P M : List Bool) (v : Bool) (w : ℕ) (hP : P.length = w) (i : ℕ) (hi : i ≠ w) :
        (P ++ M).getD (dl w i) false = (P ++ v :: M).getD i false := by
      by_cases hiw : i < w
      · simp only [dl, hiw, ite_true]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      · simp only [dl, hiw, ite_false]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hP]
        obtain ⟨k, hk⟩ : ∃ k, i - w = k + 1 := ⟨i - w - 1, by omega⟩
        rw [hk, List.getD_cons_succ]
        congr 1
        omega

    have stageB (w : ℕ) (P : List Bool) (v : Bool) (hP : P.length = w) (B : List Gate)
        (hB : ∀ g ∈ B, OkGate g ∧ w ∉ portRD g) :
        ∀ M : List Bool, ∀ i, i ≠ w →
          ((B.map (rg w)).foldl F (P ++ M)).getD (dl w i) false = (B.foldl F (P ++ v :: M)).getD i false := by
      induction B with
      | nil => intro M i hi; exact key P M v w hP i hi
      | cons g B ih =>
        intro M i hi
        simp only [List.map_cons, List.foldl_cons]
        have hg := hB g (by simp)
        have h1 : F (P ++ M) (rg w g) = P ++ (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
          unfold F
          rw [F_rg (P ++ v :: M) (P ++ M) w g hg.1, List.append_assoc]
          intro i hi
          exact key P M v w hP i (fun h => hg.2 (h ▸ hi))
        have h2 : F (P ++ v :: M) g = P ++ v :: (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
          unfold F
          simp
        rw [h1, h2]
        exact ih (fun g' hg' => hB g' (by simp [hg'])) _ i hi

    have del_getD (n j : ℕ) (gs : List Gate) (hj : j < gs.length)
        (hok : ∀ g ∈ gs, OkGate g) (hw : ∀ g ∈ gs, n + j ∉ portRD g) (x : List Bool) (hx : x.length = n)
        (i : ℕ) (hi : i ≠ n + j) :
        (((gs.eraseIdx j).map (rg (n + j))).foldl F x).getD (dl (n + j) i) false
          = (gs.foldl F x).getD i false := by
      have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
        conv_lhs => rw [← List.take_append_drop j gs]
        rw [List.drop_eq_getElem_cons hj]
      have herase : gs.eraseIdx j = gs.take j ++ gs.drop (j + 1) := List.eraseIdx_eq_take_drop_succ gs j
      have hAll : ∀ g ∈ gs, OkGate g ∧ n + j ∉ portRD g := fun g hg => ⟨hok g hg, hw g hg⟩
      rw [herase, List.map_append, List.foldl_append]
      conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
      rw [stageA (n + j) (gs.take j) (fun g hg => hAll g (List.mem_of_mem_take hg)) x
        (by rw [hx, List.length_take]; omega)]
      have hP : (List.foldl F x (gs.take j)).length = n + j := by
        rw [fold_len, hx, List.length_take]; omega
      have := stageB (n + j) (List.foldl F x (gs.take j))
        (gs[j].op.eval (gs[j].inputs.map fun i => (List.foldl F x (gs.take j)).getD i false)) hP
        (gs.drop (j + 1)) (fun g hg => hAll g (List.mem_of_mem_drop hg)) [] i hi
      simpa [F] using this

    have indep (k : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, OkGate g) (hk : ∀ g ∈ gs, k ∉ portRD g) :
        ∀ Q Q' : List Bool, Q.length = Q'.length → (∀ i, i ≠ k → Q.getD i false = Q'.getD i false) →
          ∀ i, i ≠ k → (gs.foldl F Q).getD i false = (gs.foldl F Q').getD i false := by
      induction gs with
      | nil => intro Q Q' _ h i hi; exact h i hi
      | cons g gs ih =>
        intro Q Q' hl h i hi
        simp only [List.foldl_cons]
        apply ih (fun g' hg' => hok g' (by simp [hg'])) (fun g' hg' => hk g' (by simp [hg']))
        · simp [F, hl]
        · intro i' hi'
          have hv : g.op.eval (g.inputs.map fun i => Q.getD i false)
              = g.op.eval (g.inputs.map fun i => Q'.getD i false) := by
            apply evalRd g (hok g (by simp))
            intro j hj
            exact h j (fun e => hk g (by simp) (e ▸ hj))
          unfold F
          rw [hv]
          by_cases hlt : i' < Q.length
          · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
            exact h i' hi'
          · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
        · exact hi

    have count (gs : List Gate) (hok : ∀ g ∈ gs, OkGate g) :
        (gs.flatMap portRD).length + (gs.filter fun g => g.op.eval [false]).length ≤ 2 * gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        have ih' := ih (fun g' hg' => hok g' (by simp [hg']))
        have hg : (portRD g).length + (if g.op.eval [false] = true then 1 else 0) ≤ 2 := by
          rcases (hok g (by simp)).1 with h | h | h <;> simp [portRD, h, evAnd,evOr,evNot]
        rw [List.flatMap_cons, List.filter_cons, List.length_append]
        split_ifs at hg ⊢ with hc
        · simp only [List.length_cons]
          omega
        · simp only [List.length_cons]
          omega



    have countBound (xs : List ℕ) (S : Finset ℕ) :
        ∑ i ∈ S, xs.count i ≤ xs.length := by
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
        by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

    have readcount (gs : List Gate) (a : ℕ) :
        (gs.filter (fun g => (portRD g).contains a)).length ≤ (gs.flatMap portRD).count a := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        simp only [List.filter_cons,List.flatMap_cons,List.count_append]
        split
        next h =>
          have := List.count_pos_iff.mpr (List.contains_iff_mem.mp h)
          simp only [List.length_cons]
          omega
        next => omega




    have portLemma : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x8 → x5.size ≤ x8) → x4.card + ∑ x9 ∈ x4ᶜ, (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x10.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x10.inputs).contains ↑x9) x5.gates).length + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x9.op.eval [Bool.false]) x5.gates).length ≤ x5.size + (1 : ℕ) := by
      classical
      intro n G inst A C fan computes minimal
      let xs := C.output :: C.gates.flatMap portRD
      let cnt := fun i => xs.count i
      have hok := ok_of_fan C fan
      have marked (a : Fin n) (ha : a ∈ A) : 1 ≤ cnt a := by
        apply List.count_pos_iff.mpr
        by_contra h
        have hout : C.output ≠ a.val := by intro he; exact h (by simp [xs,he])
        have noRead : ∀ g ∈ C.gates, a.val ∉ portRD g :=
          fun g hg hi => h (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g,hg,hi⟩))
        let z : Fin n → Bool := fun _ => false
        let y : Fin n → Bool := fun i => decide (i = a)
        have hb : circuitFun n C z = circuitFun n C y := by
          apply indep a.val C.gates hok noRead _ _ (by simp) _ C.output hout
          intro i hi
          by_cases hin : i < n
          · simp [List.getD_eq_getElem?_getD,hin,z,y,show (⟨i,hin⟩ : Fin n) ≠ a from fun he => hi (congrArg Fin.val he)]
          · simp [List.getD_eq_getElem?_getD,hin]
        rw [computes] at hb
        have hzy : (NestedCover.graphFun G A z) = false := by rw [evGraph]; simp [z]
        have hyy : (NestedCover.graphFun G A y) = true := by
          rw [evGraph]
          simp only [Bool.or_eq_true,decide_eq_true_eq]
          exact Or.inl ⟨a,ha,by simp [y]⟩
        exact Bool.false_ne_true (hzy.symm.trans (hb.trans hyy))
      have intern (j : ℕ) (hj : j ∈ Finset.range C.gates.length) : 1 ≤ cnt (n+j) := by
        apply List.count_pos_iff.mpr
        by_contra h
        have hout : C.output ≠ n+j := by intro he; exact h (by simp [xs,he])
        have noRead : ∀ g ∈ C.gates, n+j ∉ portRD g :=
          fun g hg hi => h (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g,hg,hi⟩))
        let K : Circuit := ⟨(C.gates.eraseIdx j).map (rg (n+j)), dl (n+j) C.output⟩
        have hj' := Finset.mem_range.mp hj
        have hfun : circuitFun n K = circuitFun n C := by
          funext x
          exact del_getD n j C.gates hj' hok noRead (List.ofFn x) (by simp) C.output hout
        have hfan : FanInTwo K := by
          intro g hg
          obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
          simpa [rg] using fan g0 (List.mem_of_mem_eraseIdx hg0)
        have b := minimal K.size ⟨K,hfan,le_rfl,fun x => congrFun (hfun.trans computes) x⟩
        simp only [K,evSize,List.length_map,List.length_eraseIdx_of_lt hj'] at b
        omega
      have primary (a : Fin n) (_ : a ∈ Aᶜ) :
          (C.gates.filter (fun g => (portRD g).contains a.val)).length ≤ cnt a := by
        have h := readcount C.gates a.val
        simp only [cnt,xs,List.count_cons]
        omega
      have hA := Finset.sum_le_sum marked
      have hP := Finset.sum_le_sum primary
      have hI := Finset.sum_le_sum intern
      simp only [Finset.sum_const,smul_eq_mul,mul_one,Finset.card_range] at hA hI
      have hin := A.sum_add_sum_compl (fun a => cnt a.val)
      rw [Fin.sum_univ_eq_sum_range] at hin
      have ht := countBound xs (Finset.range (n+C.gates.length))
      change ∑ i ∈ Finset.range (n+C.gates.length), cnt i ≤ xs.length at ht
      rw [Finset.sum_range_add] at ht
      have hb := count C.gates hok
      simp only [xs,List.length_cons] at ht
      change A.card + (∑ a ∈ Aᶜ, (C.gates.filter (fun g => (portRD g).contains a.val)).length) + _ ≤ C.gates.length+1
      omega


    let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

    have buildWiresEq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

    have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
        wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
      simp [wiresFrom, List.foldl_append]

    have wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
        ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
      induction gs with
      | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
        have : wiresFrom (g :: gs) w
            = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
        rw [this, ht]; simp

    have length_wiresFrom (gs : List Gate) (w : List Bool) :
        (wiresFrom gs w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
      rw [ht]; simp [hl]

    have getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
        (wiresFrom gs w).getD i false = w.getD i false := by
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
      rw [ht, List.getD_append _ _ _ _ h]

    let Ok (g : Gate) : Prop :=
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


    have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
      simp


    have getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
        (List.ofFn x).getD (i : ℕ) false = x i := by simp


    let Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
      ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
        out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
          (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

    have bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
        Bld n F s' := by
      intro m hm
      obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
      exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

    have bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
        (e : ∀ x, F x = H x) : Bld n H s := by
      intro m hm
      obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
      exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

    have bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
      intro m hm
      refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
      intro w _
      simp [wiresFrom]

    have bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
        (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
        {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
        Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
      intro m hm
      obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
      obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
      refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with (hg | hg) | hg
        · exact ok1 g hg
        · exact ok2 g hg
        · subst hg; rcases hop with h | h <;> simp [Ok, h]
      · simp; omega
      · simp; omega
      · intro w hw
        rw [wiresFrom_append, wiresFrom_append]
        set v := wiresFrom gs1 w with hv
        have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
        set u := wiresFrom gs2 v with hu
        have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
        have step : wiresFrom [⟨op, [o1, o2]⟩] u
            = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
        rw [step, ← lu, getD_snoc_eq]
        simp only [List.map_cons, List.map_nil, hc]
        have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
          rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
        have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
          rw [hu, ev2 v lv]
          congr 1
          funext i
          rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
        rw [e1, e2]

    have bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
        (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
      bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [evAnd,evOr,evNot]) h1 h2

    have bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
        (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
      bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [evAnd,evOr,evNot]) h1 h2

    have bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
        HasCircuitSize n F s := by
      obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
      refine ⟨⟨gs, out⟩, ok, len, ?_⟩
      intro x
      have e := ev (List.ofFn x) (by simp)
      simp only [evCirc, buildWiresEq, e]
      congr 1
      funext i
      exact getD_ofFn x i

    clear_value Bld

    have bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
        Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
      induction vs with
      | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
      | cons w ws ih =>
        intro v
        have := bld_or (bld_var v) (ih w)
        refine bld_congr (bld_mono this (by simp)) ?_
        intro x
        simp

    have bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
        Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
      obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
        cases h : S.toList with
        | nil => simp at h; exact absurd h hS.ne_empty
        | cons v vs => exact ⟨v, vs, rfl⟩
      have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
      refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
      simp



    have bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
        (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
        Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
      induction T using Finset.induction_on with
      | empty =>
        intro E hE hc
        obtain ⟨e, he⟩ := hE
        obtain ⟨t, ht, _⟩ := hc e he
        simp at ht
      | @insert t T0 htT ih =>
        intro E hE hc
        set E1 := E.filter (fun e => t ∈ e) with hE1
        set E2 := E.filter (fun e => t ∉ e) with hE2
        have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
        have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
        have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
          intro e he
          rw [hE2, Finset.mem_filter] at he
          obtain ⟨t', ht', hte⟩ := hc e he.1
          rcases Finset.mem_insert.1 ht' with h | h
          · subst h; exact absurd hte he.2
          · exact ⟨t', h, hte⟩

        set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
        have hSc : S.card ≤ E1.card := by
          refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
          · intro v hv
            simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
            exact hv
          · intro a _ b _ hab
            exact Sym2.congr_right.1 hab
        have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
            E1.card := by
          intro h1
          have hSne : S.Nonempty := by
            obtain ⟨e, he⟩ := h1
            have he' := he
            rw [hE1, Finset.mem_filter] at he'
            obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
            exact ⟨b, by simp [hS, ← hb, he]⟩
          have := bld_and (bld_var t) (bld_anyFinset S hSne)
          have hpos := hSne.card_pos
          refine bld_congr (bld_mono this (by omega)) ?_
          intro x
          rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
          constructor
          · rintro ⟨ht, v, hv, hxv⟩
            refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
            intro u hu
            rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
          · rintro ⟨e, he, hall⟩
            have he' := he
            rw [hE1, Finset.mem_filter] at he'
            obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
            subst hb
            exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
              hall b (Sym2.mem_mk_right _ _)⟩
        have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
            = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
          intro x
          rw [Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
          constructor
          · rintro ⟨e, he, h⟩
            by_cases hte : t ∈ e
            · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
            · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
          · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
        rw [hcard]
        by_cases h1 : E1.Nonempty
        · by_cases h2 : E2.Nonempty
          · have := bld_or (star h1) (ih E2 h2 c2)
            have hp := h2.card_pos
            refine bld_congr (bld_mono this (by omega)) ?_
            intro x
            rw [key]
          · rw [Finset.not_nonempty_iff_eq_empty] at h2
            refine bld_congr (bld_mono (star h1) (by omega)) ?_
            intro x
            rw [key, h2]
            simp
        · rw [Finset.not_nonempty_iff_eq_empty] at h1
          have h2 : E2.Nonempty := by
            by_contra h2
            rw [Finset.not_nonempty_iff_eq_empty] at h2
            have := hE.card_pos
            rw [h1, h2] at hsplit
            simp at hsplit
            omega
          refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
          intro x
          rw [key, h1]
          simp

    have edgeBuilder : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → Bld n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) := by
      intro n G _ T hE hc
      obtain ⟨i0, j0, h0⟩ := hE
      have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
      have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
        intro e
        refine Sym2.ind (fun a b => ?_) e
        intro he
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        rcases hc a b he with h | h
        · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
        · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
      refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
      intro x
      rw [decide_eq_decide]
      constructor
      · rintro ⟨e, he, h⟩
        revert he h
        refine Sym2.ind (fun a b => ?_) e
        intro he h
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        refine ⟨s(i, j), by simpa using hij, ?_⟩
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption




    have markedUpper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A T : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
        (hE : ∃ i j, G.Adj i j) (cover : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T)
        (hf : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) :
        HasCircuitSize n f (A.card + G.edgeFinset.card + T.card - 1) := by
      classical
      have b := edgeBuilder n G T hE cover
      obtain ⟨i,j,hij⟩ := hE
      have epos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(i,j),by simpa using hij⟩
      apply bld_hasCircuitSize
      by_cases ha : A.Nonempty
      · have ap := ha.card_pos
        apply bld_congr (bld_mono (bld_or (bld_anyFinset A ha) b) (by omega))
        intro x
        rw [Bool.eq_iff_iff, hf]
        simp
      · have he := Finset.not_nonempty_iff_eq_empty.mp ha
        apply bld_congr (bld_mono b (by simp [he]))
        intro x
        rw [Bool.eq_iff_iff, hf]
        simp [he]





    have dropLemma : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 x5 : Finset (Fin x1)) (x6 : Fin x1), (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → x5 ⊆ x4ᶜ → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x5 ∨ x11 ∈ x5) → x6 ∈ x5 → ∃ (x12 : ℕ), x12 + (5 : ℕ) ≤ x4.card + x2.edgeFinset.card + x5.card ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x13 x6 Bool.false)) x12 := by
      classical
      intro n G inst A T v deg unmarked sub cover hv
      let H := G.deleteIncidenceSet v
      have huv : v ∉ A := Finset.mem_compl.mp (sub hv)
      have hd : G.degree v = 3 := by rw [← G.ncard_neighborSet]; exact deg v huv
      have hedge : ∃ i j, H.Adj i j := by
        have hpos : 0 < (G.neighborFinset v).card := by simpa using hd ▸ (show 0 < 3 by decide)
        obtain ⟨w,hw⟩ := Finset.card_pos.mp hpos
        have hvw := (G.mem_neighborFinset v w).mp hw
        have hwv := hvw.symm
        have hdw : G.degree w = 3 := by rw [← G.ncard_neighborSet]; exact deg w (unmarked w v hwv)
        by_contra! h
        have hsub : G.neighborFinset w ⊆ {v} := by
          intro t ht
          obtain hwt := (G.mem_neighborFinset w t).mp ht
          by_contra hn
          have hne : t ≠ v := by simpa using hn
          exact h w t (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hwt,hwv.ne,hne⟩)
        have hb := Finset.card_le_card hsub
        simp [hdw] at hb
      have cov (i j : Fin n) (h : H.Adj i j) : i ∈ T.erase v ∨ j ∈ T.erase v := by
        obtain ⟨h',hi,hj⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
        exact (cover i j h').imp (fun h => Finset.mem_erase.mpr ⟨hi,h⟩)
          (fun h => Finset.mem_erase.mpr ⟨hj,h⟩)
      let f := fun x : Fin n → Bool => NestedCover.graphFun G A (Function.update x v false)
      have spec (x : Fin n → Bool) :
          f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ i j, H.Adj i j ∧ x i = true ∧ x j = true := by
        change NestedCover.graphFun G A (Function.update x v false) = true ↔ _
        rw [evGraph]
        simp only [Bool.or_eq_true,decide_eq_true_eq]
        constructor
        · rintro (⟨a,ha,hx⟩|⟨i,j,hij,hi,hj⟩)
          · exact Or.inl ⟨a,ha,by simpa [Function.update_of_ne (show a ≠ v from fun he => huv (he ▸ ha))] using hx⟩
          · have hiv : i ≠ v := by rintro rfl; simp at hi
            have hjv : j ≠ v := by rintro rfl; simp at hj
            exact Or.inr ⟨i,j,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hij,hiv,hjv⟩,
              by simpa [Function.update_of_ne hiv] using hi,by simpa [Function.update_of_ne hjv] using hj⟩
        · rintro (⟨a,ha,hx⟩|⟨i,j,hij,hi,hj⟩)
          · exact Or.inl ⟨a,ha,by simpa [Function.update_of_ne (show a ≠ v from fun he => huv (he ▸ ha))] using hx⟩
          · obtain ⟨hed,hiv,hjv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hij
            exact Or.inr ⟨i,j,hed,by simpa [Function.update_of_ne hiv] using hi,
              by simpa [Function.update_of_ne hjv] using hj⟩
      have hbuild := markedUpper H A (T.erase v) f hedge cov spec
      have hcard : H.edgeFinset.card = G.edgeFinset.card - 3 := by
        simp only [H,SimpleGraph.card_edgeFinset_deleteIncidenceSet,hd]
      obtain ⟨i,j,hij⟩ := hedge
      have pos := (Finset.card_pos.mpr (show H.edgeFinset.Nonempty from ⟨s(i,j),by simpa using hij⟩))
      have hT := Finset.card_erase_add_one hv
      exact ⟨_,by omega,hbuild⟩
    classical
    let T := Aᶜ \ I
    have ts : T ⊆ Aᶜ := Finset.sdiff_subset
    have cov (u v : Fin n) (h : G.Adj u v) : u ∈ T ∨ v ∈ T := by
      by_cases hu : u ∈ I
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (unmarked _ _ h.symm),
          fun hv => hind u hu v hv h⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (unmarked _ _ h),hu⟩)
    obtain ⟨a,b,hab⟩ := edge
    obtain ⟨v,hv⟩ : T.Nonempty := (cov a b hab).elim (fun h => ⟨a,h⟩) (fun h => ⟨b,h⟩)
    obtain ⟨s,hs,hbuild⟩ := dropLemma n G A T v deg unmarked ts cov hv
    refine ⟨v,Finset.mem_compl.mp (ts hv),s,?_,hbuild⟩
    have ports := portLemma n G A C fan computes minimal
    change A.card + (∑ a ∈ Aᶜ, (C.gates.filter fun g => (portRD g).contains a.val).length) + _ ≤ _ at ports
    rw [← hr] at ports
    have dA (a : Fin n) (ha : a ∈ A) : G.degree a = 0 :=
      (G.degree_eq_zero a).mpr (fun j h => unmarked a j h ha)
    have dU (a : Fin n) (ha : a ∈ Aᶜ) : G.degree a = 3 := by
      rw [← G.ncard_neighborSet]
      exact deg a (Finset.mem_compl.mp ha)
    have degreeSum := G.sum_degrees_eq_twice_card_edges
    rw [← A.sum_add_sum_compl,Finset.sum_congr rfl dA,Finset.sum_congr rfl dU] at degreeSum
    simp only [Finset.sum_const_zero,zero_add,Finset.sum_const,smul_eq_mul] at degreeSum
    have hR (a : Fin n) (ha : a ∈ Aᶜ) : reads a = 2 + (if reads a = 3 then 1 else 0) := by
      obtain ⟨lo,hi⟩ := hread a (Finset.mem_compl.mp ha)
      split_ifs <;> omega
    have sumR := Finset.sum_congr rfl hR
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.sum_boole,smul_eq_mul,Nat.cast_id] at sumR
    have hT : T.card = Aᶜ.card-I.card := Finset.card_sdiff_of_subset hsub
    have hI := Finset.card_le_card hsub
    omega

  intro n G dec A C f readers hdeg hgirth hmarked hedge hfan heval hmin hreads hnot
  have hm : IsMinimalCircuit n C := by
    refine ⟨hfan,?_⟩
    intro E hE he
    exact hmin E.size ⟨E,hE,le_rfl,fun x => congrFun (he.trans heval) x⟩
  have hnc : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y := by
    obtain ⟨u,v,huv⟩ := hedge
    refine ⟨fun _ => false,fun _ => true,?_⟩
    rw [heval]
    change PEqualNP.MetaComplexity.NestedCover.graphFun G A (fun _ => false) ≠
      PEqualNP.MetaComplexity.NestedCover.graphFun G A (fun _ => true)
    change (decide (∃ a ∈ A, (false : Bool) = true) ||
      decide (∃ a b, G.Adj a b ∧ (false : Bool) = true ∧ (false : Bool) = true)) ≠
      (decide (∃ a ∈ A, (true : Bool) = true) ||
      decide (∃ a b, G.Adj a b ∧ (true : Bool) = true ∧ (true : Bool) = true))
    simp [show ∃ a b, G.Adj a b from ⟨u,v,huv⟩]
  obtain ⟨D,hmap,hsize,he,hshape⟩ := normalise n C hm hnc
  let cut : Gate → Gate := fun g => ⟨g.op,g.inputs.take (bif g.op.eval [false] then 1 else 2)⟩
  let rd (v : Fin n) := D.gates.filter fun g => g.inputs.contains v.val
  have hrd (v : Fin n) : (rd v).map Gate.op = (readers v).map Gate.op := by
    change (List.filter _ D.gates).map Gate.op = _
    rw [hmap,List.filter_map,List.map_map]
    rfl
  have hlen (v : Fin n) : (rd v).length = (readers v).length := by
    simpa only [List.length_map] using congrArg List.length (hrd v)
  have hlegal : FanInTwo D := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (hmap ▸ hg)
    have hf := hfan a ha
    refine ⟨hf.1,?_⟩
    simp only [List.length_take]
    exact (Nat.min_le_right _ _).trans hf.2
  have hmD : IsMinimalCircuit n D := by
    refine ⟨hlegal,?_⟩
    intro E hE hEq
    rw [hsize]
    exact hm.2 E hE (hEq.trans he)
  have hrD : ∀ v ∉ A, 2 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧
      ((rd v).length = 3 → ∀ g ∈ rd v, g.op = .or) := by
    intro v hv
    obtain ⟨lo,hi,all⟩ := hreads v hv
    refine ⟨by simpa [hlen] using lo,by simpa [hlen] using hi,?_⟩
    intro hl g hg
    have hmop : g.op ∈ (readers v).map Gate.op := by
      rw [← hrd v]
      exact List.mem_map.mpr ⟨g,hg,rfl⟩
    obtain ⟨a,ha,haop⟩ := List.mem_map.mp hmop
    exact haop ▸ all (by simpa [hlen] using hl) a ha
  have hnD : ∃ v ∉ A, (rd v).length = 2 ∧ ∃ g ∈ rd v, g.op = .not := by
    obtain ⟨v,hv,hl,g,hg,hgn⟩ := hnot
    have hnop : GateOp.not ∈ (rd v).map Gate.op := by
      rw [hrd v]
      exact List.mem_map.mpr ⟨g,hg,hgn⟩
    obtain ⟨a,ha,haop⟩ := List.mem_map.mp hnop
    exact ⟨v,hv,by simpa [hlen] using hl,a,ha,haop⟩
  obtain ⟨v,hv,hn,hin⟩ := hnD
  have hfD : circuitFun n D = f := he.trans heval
  have nc : ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false) := by
    obtain ⟨a,ha,hav⟩ := Set.exists_ne_of_one_lt_ncard (s := G.neighborSet v)
      (show 1 < (G.neighborSet v).ncard by rw [hdeg v hv]; omega) v
    have hA := hmarked a v (show G.Adj v a from ha).symm
    obtain ⟨b,hb,hbv⟩ := Set.exists_ne_of_one_lt_ncard (s := G.neighborSet a)
      (show 1 < (G.neighborSet a).ncard by rw [hdeg a hA]; omega) v
    let x := fun i : Fin n => decide (i = a ∨ i = b)
    have hh : ∃ i j, G.Adj i j ∧ Function.update x v false i = true ∧ Function.update x v false j = true :=
      ⟨a,b,hb,by simp [Function.update, hav, x],by simp [Function.update,hbv,x]⟩
    refine ⟨fun _ => false,x,?_⟩
    change (decide (∃ a ∈ A, Function.update (fun _ : Fin n => false) v false a = true) ||
      decide (∃ a b, G.Adj a b ∧ Function.update (fun _ : Fin n => false) v false a = true ∧
          Function.update (fun _ : Fin n => false) v false b = true)) ≠
      (decide (∃ a ∈ A, Function.update x v false a = true) ||
        decide (∃ a b, G.Adj a b ∧ Function.update x v false a = true ∧ Function.update x v false b = true))
    simp [hh]
  have nc' : ∃ x y, circuitFun n D (Function.update x v false) ≠ circuitFun n D (Function.update y v false) := by
    rw [hfD]; exact nc
  rcases localElim n D v hmD hshape nc' hn hin with ⟨s,hs,hc⟩ | hard
  · exact ⟨v,hv,s,by omega,by rw [hfD] at hc; exact hc⟩
  · by_cases pays : Aᶜ.card ≤ 2 * (G.indepNum - A.card + ((Aᶜ.filter (fun z => (rd z).length = 3)).card + (D.gates.filter fun g => g.op.eval [false]).length))
    · obtain ⟨J, hJ⟩ := G.exists_isNIndepSet_indepNum
      let I := J \ A
      have subI : I ⊆ Aᶜ := fun z hz => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hz).2
      have indI : ∀ u ∈ I, ∀ w ∈ I, ¬G.Adj u w := by
        intro u hu w hw he
        exact hJ.isIndepSet (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hw).1 he.ne he
      have subJ : J ⊆ I ∪ A := by
        intro z hz
        by_cases zz : z ∈ A
        · exact Finset.mem_union_right _ zz
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz,zz⟩)
      have hcard := (Finset.card_le_card subJ).trans (Finset.card_union_le I A)
      rw [hJ.card_eq] at hcard
      have eqg (g : Gate) (hg : g ∈ D.gates) : portRD g = g.inputs := by
        obtain ⟨a,b,e⟩ := List.append_of_mem hg
        rcases hshape a g b e with ⟨hop,i,_,hin⟩ | ⟨hop,i,_,j,_,_,hin⟩
        · change g.inputs.take (bif g.op.eval [false] then 1 else 2) = _
          rw [hop,hin]; rfl
        · change g.inputs.take (bif g.op.eval [false] then 1 else 2) = _
          rcases hop with hop|hop <;> rw [hop,hin] <;> rfl
      have hreadEq : (fun z : Fin n => (rd z).length) =
          (fun z => (D.gates.filter (fun g => (portRD g).contains z.val)).length) := by
        funext z
        have ee : rd z = D.gates.filter (fun g => (portRD g).contains z.val) := by
          apply List.filter_congr
          intro g hg
          rw [eqg g hg]
        exact congrArg List.length ee
      have hminD : ∀ s, HasCircuitSize n f s → D.size ≤ s := by
        intro s hh
        rw [hsize]
        exact hmin s hh
      have hb := indepBranch G A D hdeg hmarked hedge hlegal hfD hminD _ hreadEq
        (fun z hz => ⟨(hrD z hz).1,(hrD z hz).2.1⟩) I subI indI (by omega)
      obtain ⟨w,hw,s,hs,hc⟩ := hb
      exact ⟨w,hw,s,by omega,hc⟩
    · obtain ⟨w,hw,s,hs,hc⟩ := mixed n G A D v hdeg hgirth hmarked hfD hmD hrD (by
        change 2 * (G.indepNum - A.card + (Aᶜ.filter (fun z => (rd z).length = 3)).card + (D.gates.filter fun g => g.op.eval [false]).length) < Aᶜ.card
        omega) hv hn hard
      exact ⟨w,hw,s,by omega,hc⟩
