import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reduce the 19-gate Petersen lower bound by automorphism symmetry and degenerate
-- first-gate elimination to explicit first-gate circuits on Fin 10.
set_option maxRecDepth 24000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_651_47 :
    (∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 10 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 || y 1)) →
      circuitFun 10 C = (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) →
      20 ≤ C.size) →
    (∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 10 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 || y 2)) →
      circuitFun 10 C = (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) →
      20 ≤ C.size) →
    (∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 10 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 && y 1)) →
      circuitFun 10 C = (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) →
      20 ≤ C.size) →
    (∀ C : Circuit, FanInTwo C →
      ((∀ y : Fin 10 → Bool, (C.wires (List.ofFn y)).getD 10 false = !y 0) ∨
       (∀ y : Fin 10 → Bool, (C.wires (List.ofFn y)).getD 10 false = (y 0 && y 2))) →
      circuitFun 10 C = (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) →
      20 ≤ C.size) →
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 19 := by
  classical
  intro hOrEdge hOrNon hAndEdge hNotOrAndNon h19
  let F : (Fin 10 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
    (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  have eval_and : ∀ xs : List Bool, GateOp.and.eval xs = xs.all id := fun _ => rfl
  have eval_or : ∀ xs : List Bool, GateOp.or.eval xs = xs.any id := fun _ => rfl
  have eval_not : ∀ xs : List Bool, GateOp.not.eval xs = !(xs.headD false) := fun _ => rfl
  have hex : ∃ s : ℕ, HasCircuitSize 10 F s := ⟨19, h19⟩
  let s := Nat.find hex
  have hs_le : s ≤ 19 := Nat.find_min' hex h19
  exact Exists.elim (Nat.find_spec hex) fun C0 hC0 => by
    let gs0 := C0.gates
    let out := C0.output
    have hok : FanInTwo (Circuit.mk gs0 out) := hC0.1
    have hsz : (Circuit.mk gs0 out).size ≤ s := hC0.2.1
    have hev : ∀ x : Fin 10 → Bool, (Circuit.mk gs0 out).eval (List.ofFn x) = F x := hC0.2.2
    have hF0 : F (fun _ => false) = false := rfl
    have hF01 : F (fun i => decide (i = 0 ∨ i = 1)) = true := by decide
    have hF23 : F (fun i => decide (i = 2 ∨ i = 3)) = true := by decide
    have wires_snoc : ∀ (gs : List Gate) (w : List Bool) (g : Gate),
        (g :: gs).foldl (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)]) w =
          gs.foldl (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)])
            (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := fun _ _ _ => rfl
    have fold_len : ∀ (gs : List Gate) (w : List Bool),
        (gs.foldl (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)]) w).length =
          w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp
      | cons g gs ih => intro w; rw [wires_snoc, ih]; simp; omega
    have fold_getD_lt : ∀ (gs : List Gate) (w : List Bool) (k : ℕ), k < w.length →
        (gs.foldl (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)]) w).getD k false =
          w.getD k false := by
      intro gs
      induction gs with
      | nil => intro w k _; rfl
      | cons g gs ih =>
        intro w k hk
        rw [wires_snoc, ih _ k (by simp; omega), List.getD_append _ _ _ _ hk]
    let statVal : List Bool → Bool ⊕ ℕ → Bool := fun w st =>
      Sum.elim id (fun j => w.getD j false) st
    let statValid : ℕ → Bool ⊕ ℕ → Prop := fun m st =>
      Sum.elim (fun _ => True) (fun j => j < m) st
    let simpAnd2 : ℕ → (Bool ⊕ ℕ) → (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m s1 s2 =>
      Sum.elim
        (fun c => Sum.elim (fun d => (none, Sum.inl (c && d)))
          (fun j => (none, bif c then Sum.inr j else Sum.inl false)) s2)
        (fun i => Sum.elim (fun d => (none, bif d then Sum.inr i else Sum.inl false))
          (fun j => (some { op := GateOp.and, inputs := [i, j] }, Sum.inr m)) s2)
        s1
    let simpOr2 : ℕ → (Bool ⊕ ℕ) → (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun m s1 s2 =>
      Sum.elim
        (fun c => Sum.elim (fun d => (none, Sum.inl (c || d)))
          (fun j => (none, bif c then Sum.inl true else Sum.inr j)) s2)
        (fun i => Sum.elim (fun d => (none, bif d then Sum.inl true else Sum.inr i))
          (fun j => (some { op := GateOp.or, inputs := [i, j] }, Sum.inr m)) s2)
        s1
    let simpGate : GateOp → ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun op m ins =>
      if op = GateOp.and then
        List.casesOn ins (none, Sum.inl true) fun s1 t1 =>
          List.casesOn t1 (none, s1) fun s2 t2 =>
            List.casesOn t2 (simpAnd2 m s1 s2) fun _ _ => (none, Sum.inl false)
      else if op = GateOp.or then
        List.casesOn ins (none, Sum.inl false) fun s1 t1 =>
          List.casesOn t1 (none, s1) fun s2 t2 =>
            List.casesOn t2 (simpOr2 m s1 s2) fun _ _ => (none, Sum.inl false)
      else
        List.casesOn ins (none, Sum.inl true) fun s1 _ =>
          Sum.elim (fun c => (none, Sum.inl (!c)))
            (fun j => (some { op := GateOp.not, inputs := [j] }, Sum.inr m)) s1
    let elimStep : (List (Bool ⊕ ℕ) × List Gate) → Gate → List (Bool ⊕ ℕ) × List Gate :=
      fun acc g =>
        let r := simpGate g.op (10 + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
        (acc.1 ++ [r.2], acc.2 ++ r.1.toList)
    have simp_sound : ∀ (op : GateOp),
        op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
        ∀ (w : List Bool) (ins : List (Bool ⊕ ℕ)), ins.length ≤ 2 →
          (∀ st ∈ ins, statValid w.length st) →
          (∀ gt ∈ (simpGate op w.length ins).1,
            gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2) ∧
          statValid (w.length + (simpGate op w.length ins).1.toList.length)
            (simpGate op w.length ins).2 ∧
          statVal ((simpGate op w.length ins).1.toList.foldl
            (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)]) w)
            (simpGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
      intro op hop w ins hlen hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      have hne_ao : GateOp.or ≠ GateOp.and := by intro h; exact GateOp.noConfusion h
      have hne_na : GateOp.not ≠ GateOp.and := by intro h; exact GateOp.noConfusion h
      have hne_no : GateOp.not ≠ GateOp.or := by intro h; exact GateOp.noConfusion h
      exact hop.elim
        (fun ha => by
          rw [ha]
          cases ins with
          | nil =>
            simp [simpGate, statValid, statVal, eval_and]
          | cons s1 t1 =>
            cases t1 with
            | nil =>
              have hv1 := hv s1 List.mem_cons_self
              cases s1 <;> simp [simpGate, statValid, statVal, eval_and] at hv1 ⊢ <;> exact hv1
            | cons s2 t2 =>
              cases t2 with
              | nil =>
                have hv1 := hv s1 List.mem_cons_self
                have hv2 := hv s2 (List.mem_cons_of_mem _ List.mem_cons_self)
                cases s1 with
                | inl c =>
                  cases s2 with
                  | inl d => simp [simpGate, simpAnd2, statValid, statVal, eval_and]
                  | inr j =>
                    cases c <;> simp [simpGate, simpAnd2, statValid, statVal, eval_and] at hv2 ⊢ <;> exact hv2
                | inr i =>
                  cases s2 with
                  | inl d =>
                    cases d <;> simp [simpGate, simpAnd2, statValid, statVal, eval_and] at hv1 ⊢ <;> exact hv1
                  | inr j =>
                    simp [simpGate, simpAnd2, statValid, statVal, eval_and] at hv1 hv2 ⊢
              | cons _ _ => simp at hlen)
        (fun hor_not => hor_not.elim
          (fun ho => by
            rw [ho]
            cases ins with
            | nil =>
              simp [simpGate, hne_ao, statValid, statVal, eval_or]
            | cons s1 t1 =>
              cases t1 with
              | nil =>
                have hv1 := hv s1 List.mem_cons_self
                cases s1 <;> simp [simpGate, hne_ao, statValid, statVal, eval_or] at hv1 ⊢ <;> exact hv1
              | cons s2 t2 =>
                cases t2 with
                | nil =>
                  have hv1 := hv s1 List.mem_cons_self
                  have hv2 := hv s2 (List.mem_cons_of_mem _ List.mem_cons_self)
                  cases s1 with
                  | inl c =>
                    cases s2 with
                    | inl d => simp [simpGate, hne_ao, simpOr2, statValid, statVal, eval_or]
                    | inr j =>
                      cases c <;> simp [simpGate, hne_ao, simpOr2, statValid, statVal, eval_or] at hv2 ⊢ <;> exact hv2
                  | inr i =>
                    cases s2 with
                    | inl d =>
                      cases d <;> simp [simpGate, hne_ao, simpOr2, statValid, statVal, eval_or] at hv1 ⊢ <;> exact hv1
                    | inr j =>
                      simp [simpGate, hne_ao, simpOr2, statValid, statVal, eval_or] at hv1 hv2 ⊢
                | cons _ _ => simp at hlen)
          (fun hn => by
            rw [hn]
            cases ins with
            | nil =>
              simp [simpGate, hne_na, hne_no, statValid, statVal, eval_not]
            | cons s1 t1 =>
              have hv1 := hv s1 List.mem_cons_self
              cases s1 <;> simp [simpGate, hne_na, hne_no, statValid, statVal, eval_not] at hv1 ⊢))
    have elim_pass : ∀ (gs : List Gate),
        (∀ gt ∈ gs, gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2) →
        ∀ (x : Fin 10 → Bool) (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate),
          acc.1.length = w_old.length →
          (∀ gt ∈ acc.2, gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2) →
          (∀ k : ℕ,
            statValid (10 + acc.2.length) (acc.1.getD k (Sum.inl false)) ∧
            statVal (acc.2.foldl (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)])
              (List.ofFn x)) (acc.1.getD k (Sum.inl false)) = w_old.getD k false) →
          let res := gs.foldl elimStep acc
          res.2.length ≤ acc.2.length + gs.length ∧
          (∀ gt ∈ res.2, gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2) ∧
          (∀ k : ℕ, statVal (res.2.foldl
            (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)]) (List.ofFn x))
            (res.1.getD k (Sum.inl false)) =
              (gs.foldl (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)]) w_old).getD k false) := by
      intro gs
      induction gs with
      | nil =>
        intro _ x w_old acc _ hokA hinv
        exact ⟨by simp, hokA, fun k => (hinv k).2⟩
      | cons g gs ih =>
        intro hokG x w_old acc hlenA hokA hinv
        have hg := hokG g List.mem_cons_self
        let w_cur := acc.2.foldl
          (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)]) (List.ofFn x)
        have hw_len : w_cur.length = 10 + acc.2.length := by
          change (acc.2.foldl _ (List.ofFn x)).length = 10 + acc.2.length
          rw [fold_len]; simp
        let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
        have hins_len : ins.length ≤ 2 := by simp [ins, hg.2]
        have hins_val : ∀ st ∈ ins, statValid w_cur.length st := by
          intro st hst
          exact Exists.elim (List.mem_map.mp hst) fun idx hidx => by
            rw [← hidx.2, hw_len]
            exact (hinv idx).1
        have hsnd := simp_sound g.op hg.1 w_cur ins hins_len hins_val
        rw [hw_len] at hsnd
        let acc' := elimStep acc g
        have hlen' : acc'.1.length = (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)]).length := by
          simp [acc', elimStep, hlenA]
        have hok' : ∀ gt ∈ acc'.2,
            gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2 := by
          intro gt hgt
          exact (List.mem_append.mp hgt).elim (fun h1 => hokA gt h1)
            (fun h2 => hsnd.1 gt (Option.mem_toList.mp h2))
        have hopt_le : (simpGate g.op (10 + acc.2.length) ins).1.toList.length ≤ 1 := by
          cases (simpGate g.op (10 + acc.2.length) ins).1 <;> simp
        have hinv' : ∀ k : ℕ,
            statValid (10 + acc'.2.length) (acc'.1.getD k (Sum.inl false)) ∧
            statVal (acc'.2.foldl (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)])
              (List.ofFn x)) (acc'.1.getD k (Sum.inl false)) =
                (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)]).getD k false := by
          intro k
          by_cases hklt : k < acc.1.length
          · have e1 : acc'.1.getD k (Sum.inl false) = acc.1.getD k (Sum.inl false) :=
              List.getD_append _ _ _ _ hklt
            have e2 : (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)]).getD k false =
                w_old.getD k false := List.getD_append _ _ _ _ (hlenA ▸ hklt)
            rw [e1, e2]
            have hv_k := (hinv k).1
            have heq_k := (hinv k).2
            refine ⟨?_, ?_⟩
            · cases hst : acc.1.getD k (Sum.inl false) with
              | inl _ => trivial
              | inr j =>
                rw [hst] at hv_k
                change j < 10 + acc.2.length at hv_k
                change j < 10 + (acc.2 ++ _).length
                rw [List.length_append]
                omega
            · cases hst : acc.1.getD k (Sum.inl false) with
              | inl c => rw [hst] at heq_k; exact heq_k
              | inr j =>
                rw [hst] at hv_k heq_k
                change j < 10 + acc.2.length at hv_k
                change (acc'.2.foldl _ (List.ofFn x)).getD j false = _
                simp only [acc', elimStep, List.foldl_append]
                rw [fold_getD_lt _ w_cur j (by rw [hw_len]; exact hv_k)]
                exact heq_k
          · by_cases hkeq : k = acc.1.length
            · subst hkeq
              have e1 : acc'.1.getD acc.1.length (Sum.inl false) =
                  (simpGate g.op (10 + acc.2.length) ins).2 := by
                change (acc.1 ++ [(simpGate g.op (10 + acc.2.length) ins).2]).getD acc.1.length (Sum.inl false) = _
                simp
              have e2 : (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)]).getD acc.1.length false =
                  g.op.eval (g.inputs.map fun i => w_old.getD i false) := by
                rw [hlenA]; simp
              rw [e1, e2]
              refine ⟨?_, ?_⟩
              · simp only [acc', elimStep, List.length_append, ← Nat.add_assoc]
                exact hsnd.2.1
              · simp only [acc', elimStep, List.foldl_append]
                rw [hsnd.2.2]
                congr 1
                rw [List.map_map]
                apply List.map_congr_left
                intro idx _
                exact (hinv idx).2
            · have e1 : acc'.1.getD k (Sum.inl false) = Sum.inl false :=
                List.getD_eq_default _ _ (by simp [acc', elimStep]; omega)
              have e2 : (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)]).getD k false = false :=
                List.getD_eq_default _ _ (by simp [← hlenA]; omega)
              rw [e1, e2]
              exact ⟨trivial, rfl⟩
        have hstep := ih (fun gt hgt => hokG gt (List.mem_cons_of_mem _ hgt)) x _ acc' hlen' hok' hinv'
        refine ⟨?_, hstep.2.1, hstep.2.2⟩
        have hl_ih := hstep.1
        change (gs.foldl elimStep acc').2.length ≤ acc.2.length + (g :: gs).length
        have hacc'_len : acc'.2.length ≤ acc.2.length + 1 := by
          change (acc.2 ++ (simpGate g.op (10 + acc.2.length) ins).1.toList).length ≤ acc.2.length + 1
          rw [List.length_append]
          omega
        rw [List.length_cons]
        omega
    cases hgs0 : gs0 with
    | nil =>
      rw [hgs0] at hev
      have eval_nil : ∀ x : Fin 10 → Bool,
          (Circuit.mk [] out).eval (List.ofFn x) = (List.ofFn x).getD out false := fun _ => rfl
      have hc1 := hev (fun i => decide (i = 0 ∨ i = 1))
      have hc2 := hev (fun i => decide (i = 2 ∨ i = 3))
      rw [eval_nil, hF01] at hc1
      rw [eval_nil, hF23] at hc2
      by_cases hout : out < 10
      · rw [List.getD_eq_getElem _ _ (by simp [hout]), List.getElem_ofFn] at hc1 hc2
        have h01 : (⟨out, hout⟩ : Fin 10) = 0 ∨ (⟨out, hout⟩ : Fin 10) = 1 := of_decide_eq_true hc1
        have h23 : (⟨out, hout⟩ : Fin 10) = 2 ∨ (⟨out, hout⟩ : Fin 10) = 3 := of_decide_eq_true hc2
        omega
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hc1
        exact Bool.noConfusion hc1
    | cons g0 gs =>
      rw [hgs0] at hok hsz hev
      have hsz_cons : gs.length + 1 ≤ s := by
        change (g0 :: gs).length ≤ s at hsz
        simpa only [List.length_cons] using hsz
      let V : (Fin 10 → Bool) → Bool := fun x =>
        g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)
      have noDegen : ∀ st0 : Bool ⊕ ℕ,
          statValid 10 st0 →
          (∀ x : Fin 10 → Bool, V x = statVal (List.ofFn x) st0) → False := by
        intro st0 hst0 hV
        let init1 : List (Bool ⊕ ℕ) := (List.range 10).map Sum.inr ++ [st0]
        let res := gs.foldl elimStep (init1, [])
        have hres_all : ∀ x : Fin 10 → Bool,
            res.2.length ≤ gs.length ∧
            (∀ gt ∈ res.2, gt.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gt.inputs.length ≤ 2) ∧
            statVal (res.2.foldl (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)])
              (List.ofFn x)) (res.1.getD out (Sum.inl false)) = F x := by
          intro x
          have hp := elim_pass gs (fun gt hgt => hok gt (List.mem_cons_of_mem _ hgt))
            x (List.ofFn x ++ [V x]) (init1, []) (by simp [init1]) (by simp) (by
              intro k
              by_cases hk10 : k < 10
              · have e1 : init1.getD k (Sum.inl false) = Sum.inr k := by
                  rw [List.getD_append _ _ _ _ (by simp [init1, hk10])]
                  rw [List.getD_eq_getElem _ _ (by simp [hk10])]
                  simp
                have e2 : (List.ofFn x ++ [V x]).getD k false = (List.ofFn x).getD k false :=
                  List.getD_append _ _ _ _ (by simp [hk10])
                rw [e1, e2]
                exact ⟨by change k < 10 + 0; omega, rfl⟩
              · by_cases hkeq : k = 10
                · subst hkeq
                  have e1 : init1.getD 10 (Sum.inl false) = st0 := by
                    simp [init1]
                  have e2 : (List.ofFn x ++ [V x]).getD 10 false = V x := by
                    change (List.ofFn x ++ [V x]).getD (List.ofFn x).length false = V x
                    simp
                  rw [e1, e2, hV x]
                  exact ⟨hst0, rfl⟩
                · rw [List.getD_eq_default _ _ (by simp [init1]; omega),
                      List.getD_eq_default _ _ (by simp; omega)]
                  exact ⟨trivial, rfl⟩)
          exact ⟨by simpa using hp.1, hp.2.1, (hp.2.2 out).trans (hev x)⟩
        cases hst_out : res.1.getD out (Sum.inl false) with
        | inl c =>
          have e0 := (hres_all (fun _ => false)).2.2
          have e1 := (hres_all (fun i => decide (i = 0 ∨ i = 1))).2.2
          rw [hst_out, hF0] at e0
          rw [hst_out, hF01] at e1
          change c = false at e0
          change c = true at e1
          exact Bool.false_ne_true (e0.symm.trans e1)
        | inr j =>
          have h0 := hres_all (fun _ => false)
          have hsmall : HasCircuitSize 10 F gs.length := by
            refine ⟨{ gates := res.2, output := j }, h0.2.1, h0.1, fun x => ?_⟩
            have ex := (hres_all x).2.2
            rw [hst_out] at ex
            exact ex
          exact Nat.find_min hex (by omega : gs.length < s) hsmall
      let genA : Fin 10 → Fin 10 := ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5]
      have hGenA : ∀ x : Fin 10 → Bool, F (x ∘ genA) = F x := by
        intro x; change F (fun i => x (genA i)) = F x; dsimp [F, genA]; ac_rfl
      let genB : Fin 10 → Fin 10 := ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7]
      have hGenB : ∀ x : Fin 10 → Bool, F (x ∘ genB) = F x := by
        intro x; change F (fun i => x (genB i)) = F x; dsimp [F, genB]; ac_rfl
      let move : List Bool → Fin 10 → Fin 10 := fun word i =>
        word.foldl (fun j bit => if bit then genB j else genA j) i
      have moveInv : ∀ (word : List Bool) (x : Fin 10 → Bool), F (x ∘ move word) = F x := by
        intro word
        induction word with
        | nil => intro x; rfl
        | cons bit rest ih =>
          intro x
          cases bit
          · exact (hGenA (x ∘ move rest)).trans (ih x)
          · exact (hGenB (x ∘ move rest)).trans (ih x)
      have hinjA : Function.Injective genA := by decide
      have hinjB : Function.Injective genB := by decide
      have hinjM : ∀ w : List Bool, Function.Injective (move w) := by
        intro w
        induction w with
        | nil => exact Function.injective_id
        | cons bit rest ih =>
          intro a1 a2 heq
          cases bit
          · exact hinjA (ih heq)
          · exact hinjB (ih heq)
      let words := (List.range 7).flatMap fun n =>
        (List.range (2 ^ n)).map fun m => (List.range n).map m.testBit
      have cover : ∀ i j : Fin 10, words.any (fun w =>
          decide (move w i = 0 ∧ (move w j = 0 ∨ move w j = 1 ∨ move w j = 2))) = true := by decide
      let remap : (Fin 10 → Fin 10) → ℕ → ℕ := fun p w =>
        if h : w < 10 then (p ⟨w, h⟩).val else w
      let mapGate : (Fin 10 → Fin 10) → Gate → Gate := fun p gt =>
        { op := gt.op, inputs := gt.inputs.map (remap p) }
      let relabelC : (Fin 10 → Fin 10) → Circuit := fun p =>
        { gates := (g0 :: gs).map (mapGate p), output := remap p out }
      have relabel_wires : ∀ (p : Fin 10 → Fin 10) (y : Fin 10 → Bool) (k : ℕ),
          ((relabelC p).wires (List.ofFn y)).getD (remap p k) false =
            ((Circuit.mk (g0 :: gs) out).wires (List.ofFn (y ∘ p))).getD k false := by
        intro p y
        suffices hfold : ∀ (gl : List Gate) (w1 w2 : List Bool),
            10 ≤ w1.length → w1.length = w2.length →
            (∀ k : ℕ, w1.getD (remap p k) false = w2.getD k false) →
            ∀ k : ℕ,
              ((gl.map (mapGate p)).foldl
                (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)]) w1).getD
                (remap p k) false =
              (gl.foldl (fun l gt => l ++ [gt.op.eval (gt.inputs.map fun i => l.getD i false)]) w2).getD
                k false by
          apply hfold (g0 :: gs) (List.ofFn y) (List.ofFn (y ∘ p)) (by simp) (by simp)
          intro k
          by_cases hk : k < 10
          · simp only [remap, hk, ↓reduceDIte]
            rw [List.getD_eq_getElem _ _ (by simp [(p ⟨k, hk⟩).isLt]), List.getElem_ofFn,
                List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
            rfl
          · simp only [remap, hk, ↓reduceDIte]
            rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]
        intro gl
        induction gl with
        | nil => intro w1 w2 _ _ hrel k; exact hrel k
        | cons g gl ih =>
          intro w1 w2 hw10 hlenEq hrel k
          simp only [List.map_cons, wires_snoc, mapGate]
          have hmap_eq : ((g.inputs.map (remap p)).map fun i => w1.getD i false) =
              (g.inputs.map fun i => w2.getD i false) := by
            rw [List.map_map]
            exact List.map_congr_left fun idx _ => hrel idx
          rw [hmap_eq]
          apply ih _ _ (by simp; omega) (by simp [hlenEq]) _ k
          intro m
          by_cases hm10 : m < 10
          · have hrm : remap p m < w1.length := by
              simp only [remap, hm10, ↓reduceDIte]
              exact lt_of_lt_of_le (p ⟨m, hm10⟩).isLt hw10
            rw [List.getD_append _ _ _ _ hrm, List.getD_append _ _ _ _ (by omega)]
            exact hrel m
          · have hrm_eq : remap p m = m := by simp [remap, hm10]
            rw [hrm_eq]
            by_cases hmlt : m < w1.length
            · rw [List.getD_append _ _ _ _ hmlt, List.getD_append _ _ _ _ (hlenEq ▸ hmlt)]
              have := hrel m
              rwa [hrm_eq] at this
            · by_cases hmeq : m = w1.length
              · subst hmeq
                have hget1 : (w1 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]).getD w1.length false =
                    g.op.eval (g.inputs.map fun i => w2.getD i false) := by simp
                have hget2 : (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]).getD w1.length false =
                    g.op.eval (g.inputs.map fun i => w2.getD i false) := by rw [hlenEq]; simp
                rw [hget1, hget2]
              · rw [List.getD_eq_default _ _ (by simp; omega),
                    List.getD_eq_default _ _ (by simp [← hlenEq]; omega)]
      have relabel_props : ∀ (p : Fin 10 → Fin 10),
          (∀ x : Fin 10 → Bool, F (x ∘ p) = F x) →
          FanInTwo (relabelC p) ∧ (relabelC p).size ≤ 19 ∧ circuitFun 10 (relabelC p) = F ∧
          (∀ y : Fin 10 → Bool, ((relabelC p).wires (List.ofFn y)).getD 10 false = V (y ∘ p)) := by
        intro p hpF
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro gt hgt
          exact Exists.elim (List.mem_map.mp hgt) fun g1 hg1 => by
            rw [← hg1.2]
            have h1 := hok g1 hg1.1
            exact ⟨h1.1, by simpa [mapGate] using h1.2⟩
        · have hcsz : (relabelC p).size = (g0 :: gs).length := by
            change ((g0 :: gs).map (mapGate p)).length = (g0 :: gs).length
            simp
          rw [hcsz, List.length_cons]
          omega
        · funext y
          change ((relabelC p).wires (List.ofFn y)).getD (remap p out) false = F y
          rw [relabel_wires p y out]
          exact (hev (y ∘ p)).trans (hpF y)
        · intro y
          have h10 : remap p 10 = 10 := by simp [remap]
          have hw := relabel_wires p y 10
          rw [h10] at hw
          rw [hw]
          change (gs.foldl _ (List.ofFn (y ∘ p) ++ [V (y ∘ p)])).getD 10 false = V (y ∘ p)
          rw [fold_getD_lt gs (List.ofFn (y ∘ p) ++ [V (y ∘ p)]) 10 (by simp)]
          change (List.ofFn (y ∘ p) ++ [V (y ∘ p)]).getD (List.ofFn (y ∘ p)).length false = V (y ∘ p)
          simp
      have readValid : ∀ (x : Fin 10 → Bool) (w : ℕ) (hw : w < 10),
          (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
        intro x w hw
        rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_ofFn]
      have readMissing : ∀ (x : Fin 10 → Bool) (w : ℕ), ¬ w < 10 →
          (List.ofFn x).getD w false = false := by
        intro x w hw
        exact List.getD_eq_default _ _ (by simp; omega)
      have hg0 := hok g0 List.mem_cons_self
      have hop0 := hg0.1
      have hlen0 : g0.inputs.length ≤ 2 := hg0.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop0
      cases hin0 : g0.inputs with
      | nil =>
        exact noDegen (Sum.inl (g0.op.eval [])) trivial (by intro x; simp [V, hin0, statVal])
      | cons u tail =>
        cases htail : tail with
        | nil =>
          by_cases hu : u < 10
          · exact hop0.elim
              (fun hop => noDegen (Sum.inr u) hu (by
                intro x; simp only [V, hin0, htail, hop, List.map_cons, List.map_nil, eval_and, statVal]; simp))
              (fun hor_not => hor_not.elim
                (fun hop => noDegen (Sum.inr u) hu (by
                  intro x; simp only [V, hin0, htail, hop, List.map_cons, List.map_nil, eval_or, statVal]; simp))
                (fun hop =>
                  Exists.elim (List.any_eq_true.mp (cover ⟨u, hu⟩ ⟨u, hu⟩)) fun w hw => by
                    have hm := of_decide_eq_true hw.2
                    let p := move w
                    have hi0 : p ⟨u, hu⟩ = 0 := hm.1
                    have hrp := relabel_props p (moveInv w)
                    have h20 := hNotOrAndNon (relabelC p) hrp.1 (Or.inl (fun y => by
                      rw [hrp.2.2.2 y]
                      simp only [V, hin0, htail, hop, List.map_cons, List.map_nil, eval_not,
                        readValid (y ∘ p) u hu, Function.comp_apply, hi0]
                      rfl)) hrp.2.2.1
                    have hs19 := hrp.2.1
                    omega))
          · exact noDegen (Sum.inl (g0.op.eval [false])) trivial (by
              intro x
              simp only [V, hin0, htail, List.map_cons, List.map_nil, readMissing x u hu, statVal]
              rfl)
        | cons v tail2 =>
          have htl : tail2 = [] := by simpa [hin0, htail] using hlen0
          have hin2 : ∀ z : Fin 10 → Bool, V z =
              g0.op.eval [(List.ofFn z).getD u false, (List.ofFn z).getD v false] := by
            intro z; dsimp only [V]; rw [hin0, htail, htl]; rfl
          have eval2_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by
            intro b1 b2; rw [eval_and]; simp
          have eval2_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by
            intro b1 b2; rw [eval_or]; simp
          have stat_inr : ∀ (z : Fin 10 → Bool) (w : ℕ),
              statVal (List.ofFn z) (Sum.inr w) = (List.ofFn z).getD w false := fun _ _ => rfl
          have stat_inl : ∀ (z : Fin 10 → Bool) (c : Bool),
              statVal (List.ofFn z) (Sum.inl c) = c := fun _ _ => rfl
          exact hop0.elim
            (fun hop => by
              by_cases hu : u < 10
              · by_cases hv : v < 10
                · exact Exists.elim (List.any_eq_true.mp (cover ⟨u, hu⟩ ⟨v, hv⟩)) fun w hw => by
                    have hm := of_decide_eq_true hw.2
                    let p := move w
                    have hi0 : p ⟨u, hu⟩ = 0 := hm.1
                    have hrp := relabel_props p (moveInv w)
                    have hs19 := hrp.2.1
                    exact hm.2.elim
                      (fun hj0 => by
                        have huv : u = v := congrArg Fin.val (hinjM w (hi0.trans hj0.symm))
                        subst huv
                        exact noDegen (Sum.inr u) hu (fun x => by
                          rw [hin2 x, hop, eval2_and, stat_inr, readValid x u hu, Bool.and_self]))
                      (fun hj12 => hj12.elim
                        (fun hj1 => by
                          have h20 := hAndEdge (relabelC p) hrp.1 (fun y => by
                            rw [hrp.2.2.2 y, hin2 (y ∘ p), hop, eval2_and,
                              readValid (y ∘ p) u hu, readValid (y ∘ p) v hv]
                            dsimp only [Function.comp_def, p] at hi0 ⊢
                            rw [hi0, hj1]) hrp.2.2.1
                          omega)
                        (fun hj2 => by
                          have h20 := hNotOrAndNon (relabelC p) hrp.1 (Or.inr (fun y => by
                            rw [hrp.2.2.2 y, hin2 (y ∘ p), hop, eval2_and,
                              readValid (y ∘ p) u hu, readValid (y ∘ p) v hv]
                            dsimp only [Function.comp_def, p] at hi0 ⊢
                            rw [hi0, hj2])) hrp.2.2.1
                          omega))
                · exact noDegen (Sum.inl false) trivial (fun x => by
                    rw [hin2 x, hop, eval2_and, readMissing x v hv, Bool.and_false, stat_inl])
              · exact noDegen (Sum.inl false) trivial (fun x => by
                  rw [hin2 x, hop, eval2_and, readMissing x u hu, Bool.false_and, stat_inl]))
            (fun hor_not => hor_not.elim
              (fun hop => by
                by_cases hu : u < 10
                · by_cases hv : v < 10
                  · exact Exists.elim (List.any_eq_true.mp (cover ⟨u, hu⟩ ⟨v, hv⟩)) fun w hw => by
                      have hm := of_decide_eq_true hw.2
                      let p := move w
                      have hi0 : p ⟨u, hu⟩ = 0 := hm.1
                      have hrp := relabel_props p (moveInv w)
                      have hs19 := hrp.2.1
                      exact hm.2.elim
                        (fun hj0 => by
                          have huv : u = v := congrArg Fin.val (hinjM w (hi0.trans hj0.symm))
                          subst huv
                          exact noDegen (Sum.inr u) hu (fun x => by
                            rw [hin2 x, hop, eval2_or, stat_inr, readValid x u hu, Bool.or_self]))
                        (fun hj12 => hj12.elim
                          (fun hj1 => by
                            have h20 := hOrEdge (relabelC p) hrp.1 (fun y => by
                              rw [hrp.2.2.2 y, hin2 (y ∘ p), hop, eval2_or,
                                readValid (y ∘ p) u hu, readValid (y ∘ p) v hv]
                              dsimp only [Function.comp_def, p] at hi0 ⊢
                              rw [hi0, hj1]) hrp.2.2.1
                            omega)
                          (fun hj2 => by
                            have h20 := hOrNon (relabelC p) hrp.1 (fun y => by
                              rw [hrp.2.2.2 y, hin2 (y ∘ p), hop, eval2_or,
                                readValid (y ∘ p) u hu, readValid (y ∘ p) v hv]
                              dsimp only [Function.comp_def, p] at hi0 ⊢
                              rw [hi0, hj2]) hrp.2.2.1
                            omega))
                  · exact noDegen (Sum.inr u) hu (fun x => by
                      rw [hin2 x, hop, eval2_or, readMissing x v hv, Bool.or_false, stat_inr])
                · by_cases hv : v < 10
                  · exact noDegen (Sum.inr v) hv (fun x => by
                      rw [hin2 x, hop, eval2_or, readMissing x u hu, Bool.false_or, stat_inr])
                  · exact noDegen (Sum.inl false) trivial (fun x => by
                      rw [hin2 x, hop, eval2_or, readMissing x u hu, readMissing x v hv,
                        Bool.false_or, stat_inl]))
              (fun hop => by
                by_cases hu : u < 10
                · exact Exists.elim (List.any_eq_true.mp (cover ⟨u, hu⟩ ⟨u, hu⟩)) fun w hw => by
                    have hm := of_decide_eq_true hw.2
                    let p := move w
                    have hi0 : p ⟨u, hu⟩ = 0 := hm.1
                    have hrp := relabel_props p (moveInv w)
                    have hs19 := hrp.2.1
                    have h20 := hNotOrAndNon (relabelC p) hrp.1 (Or.inl (fun y => by
                      rw [hrp.2.2.2 y, hin2 (y ∘ p), hop, eval_not, readValid (y ∘ p) u hu]
                      simp only [List.headD_cons, Function.comp_apply, hi0])) hrp.2.2.1
                    omega
                · exact noDegen (Sum.inl true) trivial (fun x => by
                    rw [hin2 x, hop, eval_not, readMissing x u hu, stat_inl]
                    rfl)))
