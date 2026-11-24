import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Exchanging bits four and six preserves their OR. A single gate which reads
-- both bits also preserves the exchange. The edge at vertices zero and four
-- distinguishes the two assignments, so two different gates must read them.
theorem PEqualNP.Outside.R_meta_1910_1
    (earlyFour : ∀ (D : Circuit) (i j : Fin D.gates.length), FanInTwo D → D.size ≤ 14 → i < j →
      (∀ k : Fin D.gates.length, ((D.gates.get k).inputs[0]? = some 4 ∨ ((D.gates.get k).op ≠ GateOp.not ∧ 4 ∈ (D.gates.get k).inputs)) ↔ k = i) →
      (∀ k : Fin D.gates.length, ((D.gates.get k).inputs[0]? = some 6 ∨ ((D.gates.get k).op ≠ GateOp.not ∧ 6 ∈ (D.gates.get k).inputs)) ↔ k = j) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x)
    (earlySix : ∀ (D : Circuit) (i j : Fin D.gates.length), FanInTwo D → D.size ≤ 14 → i < j →
      (∀ k : Fin D.gates.length, ((D.gates.get k).inputs[0]? = some 4 ∨ ((D.gates.get k).op ≠ GateOp.not ∧ 4 ∈ (D.gates.get k).inputs)) ↔ k = j) →
      (∀ k : Fin D.gates.length, ((D.gates.get k).inputs[0]? = some 6 ∨ ((D.gates.get k).op ≠ GateOp.not ∧ 6 ∈ (D.gates.get k).inputs)) ↔ k = i) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x7 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x8 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x7;               x8.inputs[(0 : ℕ)]? = Option.some x5 ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x8.inputs) →           (16 : ℕ) ≤ x1.size := by
  intro ⟨gs, out⟩ fan first heval uniqueReader
  by_contra! small
  have keep (s : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      ((Circuit.mk s 0).wires w).getD j false = w.getD j false := by
    induction s generalizing w with
    | nil => rfl
    | cons z s ih =>
      change ((Circuit.mk s 0).wires (w ++ [_])).getD j false = _
      rw [ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hj
  cases gs with
  | nil =>
    obtain ⟨k, _⟩ := uniqueReader 4 (by simp)
    exact Fin.elim0 k
  | cons g tail =>
    let D : Circuit := ⟨tail, out⟩
    let R (v : ℕ) (z : Gate) := (z.inputs[0]? = some v ∨ (z.op ≠ GateOp.not ∧ v ∈ z.inputs))
    have ur (v : ℕ) (hv : v ∈ [4,6]) : ∃! k : Fin tail.length, R v (tail.get k) :=
      uniqueReader v hv
    obtain ⟨i, hi, ui⟩ := ur 4 (by simp)
    obtain ⟨j, hj, uj⟩ := ur 6 (by simp)
    have ri (k : Fin tail.length) : R 4 (tail.get k) ↔ k = i := ⟨ui k, fun h => h ▸ hi⟩
    have rj (k : Fin tail.length) : R 6 (tail.get k) ↔ k = j := ⟨uj k, fun h => h ▸ hj⟩
    have hd : FanInTwo D := fun z hz => fan z (List.mem_cons_of_mem _ hz)
    have hs : D.size ≤ 14 := by
      change (g :: tail).length < 16 at small
      change tail.length ≤ 14
      simp only [List.length_cons] at small
      omega
    have run (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 4 || x 6]) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x := by
      let v := g.op.eval (g.inputs.map (fun p => (List.ofFn x).getD p false))
      have h := first x
      change ((Circuit.mk tail 0).wires (List.ofFn x ++ [v])).getD 9 false = _ at h
      rw [keep _ _ _ (by simp)] at h
      have hv : v = (x 4 || x 6) := by simpa [List.getD_eq_getElem?_getD, List.getElem?_append] using h
      have ev := congrFun heval x
      change D.eval (List.ofFn x ++ [v]) = _ at ev
      simpa only [hv] using ev
    rcases lt_trichotomy i j with lt | eq | gt
    · obtain ⟨x, bad⟩ := earlyFour D i j hd hs lt ri rj
      exact bad (run x)
    · subst j
      have equiv (z : Gate) (hz : z ∈ tail) : R 4 z ↔ R 6 z := by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
        exact (ri ⟨k,hk⟩).trans (rj ⟨k,hk⟩).symm
      let l : Fin 9 → Bool := fun v => v == 0 || v == 4
      let r : Fin 9 → Bool := fun v => v == 0 || v == 6
      let L := List.ofFn l
      let T := List.ofFn r
      have agree (s : List Bool) (v : ℕ) (h4 : v ≠ 4) (h6 : v ≠ 6) :
          (L ++ s).getD v false = (T ++ s).getD v false := by
        by_cases h : v < 9
        · rw [List.getD_append _ _ _ _ (by simpa [L] using h),
              List.getD_append _ _ _ _ (by simpa [T] using h)]
          interval_cases v <;> first | rfl | contradiction
        · rw [List.getD_append_right _ _ _ _ (by simpa [L] using h),
              List.getD_append_right _ _ _ _ (by simpa [T] using h)]
          simp [L,T]
      have sameGate (z : Gate) (hz : z ∈ tail) (s : List Bool) :
          z.op.eval (z.inputs.map (fun v => (L ++ s).getD v false)) =
          z.op.eval (z.inputs.map (fun v => (T ++ s).getD v false)) := by
        obtain ⟨allowed, len⟩ := hd z hz
        have sym := equiv z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at allowed
        rcases ins : z.inputs with _ | ⟨a, rest⟩
        · rfl
        rcases rest with _ | ⟨b, rest⟩
        · simp only [R, ins, List.getElem?_cons_zero, Option.some.injEq,
              List.mem_singleton] at sym
          have a4 : a ≠ 4 := by intro h; subst a; simp at sym
          have a6 : a ≠ 6 := by intro h; subst a; simp at sym
          simp only [List.map_cons, List.map_nil, agree s a a4 a6]
        rcases rest with _ | ⟨c, rest⟩
        · have v4 : (L ++ s).getD 4 false = true ∧ (T ++ s).getD 4 false = false :=
            ⟨List.getD_append _ _ _ _ (by decide), List.getD_append _ _ _ _ (by decide)⟩
          have v6 : (L ++ s).getD 6 false = false ∧ (T ++ s).getD 6 false = true :=
            ⟨List.getD_append _ _ _ _ (by decide), List.getD_append _ _ _ _ (by decide)⟩
          have repr (v : ℕ) : (L ++ s).getD v false =
              if v = 4 then true else if v = 6 then false else (T ++ s).getD v false := by
            by_cases h4 : v = 4
            · subst v; exact v4.1
            by_cases h6 : v = 6
            · subst v; exact v6.1
            · simpa [h4, h6] using agree s v h4 h6
          rcases allowed with h | h | h <;>
            simp only [R, ins, h] at sym <;>
            by_cases a4 : a = 4 <;> by_cases a6 : a = 6 <;>
            by_cases b4 : b = 4 <;> by_cases b6 : b = 6 <;>
            simp [a4, a6, b4, b6, @eq_comm ℕ (4 : ℕ) a, @eq_comm ℕ (6 : ℕ) a,
              @eq_comm ℕ (4 : ℕ) b, @eq_comm ℕ (6 : ℕ) b] at sym <;>
            first | omega | (simp only [h, List.map_cons, List.map_nil, GateOp.eval,
              List.all_cons, List.any_cons, List.any_nil, List.all_nil, List.headD_cons,
              id_eq, repr, a4, a6, b4, b6, v4.2, v6.2]; simp)
        · rw [ins] at len
          simp at len
      have trace (s : List Gate) (sub : ∀ z ∈ s, z ∈ tail) (w : List Bool) :
          ∃ w', (Circuit.mk s 0).wires (L ++ w) = L ++ w' ∧
            (Circuit.mk s 0).wires (T ++ w) = T ++ w' := by
        induction s generalizing w with
        | nil => exact ⟨w,rfl,rfl⟩
        | cons z s ih =>
          let b := z.op.eval (z.inputs.map (fun v => (T ++ w).getD v false))
          obtain ⟨w', hl, hr⟩ := ih (fun t ht => sub t (List.mem_cons_of_mem _ ht)) (w ++ [b])
          refine ⟨w', ?_, ?_⟩
          · change (Circuit.mk s 0).wires ((L ++ w) ++ [_]) = _
            rw [sameGate z (sub z List.mem_cons_self) w, List.append_assoc]
            exact hl
          · change (Circuit.mk s 0).wires ((T ++ w) ++ [b]) = _
            rw [List.append_assoc]
            exact hr
      have h4 : out ≠ 4 := by
        intro e
        have h := run (fun v => v == 4)
        change ((Circuit.mk tail 0).wires _).getD out false = false at h
        rw [e, keep _ _ _ (by decide)] at h
        contradiction
      have h6 : out ≠ 6 := by
        intro e
        have h := run (fun v => v == 6)
        change ((Circuit.mk tail 0).wires _).getD out false = false at h
        rw [e, keep _ _ _ (by decide)] at h
        contradiction
      obtain ⟨w, hl, hr⟩ := trace tail (fun _ h => h) [true]
      have vl := run l
      have vr := run r
      change ((Circuit.mk tail 0).wires (L ++ [true])).getD out false = true at vl
      change ((Circuit.mk tail 0).wires (T ++ [true])).getD out false = false at vr
      rw [hl, agree w out h4 h6, ← hr, vr] at vl
      contradiction
    · obtain ⟨x, bad⟩ := earlySix D j i hd hs gt ri rj
      exact bad (run x)
