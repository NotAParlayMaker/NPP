import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pin vertex four to zero. Either two gates disappear, including the final
-- disjunction in the count, or the only surviving use of vertex four is
-- through a disjunction with a prefix wire. In the latter case compare the
-- eight-variable cofactors with that wire connected and with it forced high.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3138_317
    (peel :
      let cost := fun gs : List Gate => gs.countP (fun g => g.op.eval [false])
      ∀ (gs : List Gate) (a b : ℕ), FanInTwo (⟨gs,0⟩ : Circuit) → a ≠ 4 → b ≠ 4 →
      let f := fun (t : Bool) (x : Fin 9 → Bool) =>
        let w := (Circuit.mk gs 0).wires (List.ofFn ((4 : Fin 10).insertNth t x))
        w.getD a false || w.getD b false
      (∃ x, f false x ≠ f true x) → (∃ x y, f false x ≠ f false y) →
      (∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ gs.length ∧ cost D.gates ≤ cost gs ∧
        circuitFun 9 D = f false) ∨
      ∃ (P Q : Circuit) (r : ℕ), FanInTwo P ∧ FanInTwo Q ∧ P.size + Q.size + 1 ≤ gs.length ∧
        cost P.gates + cost Q.gates ≤ cost gs ∧
        ∀ (x : Fin 9 → Bool) (t : Bool), let w := P.wires (List.ofFn x)
          let z := Q.wires (w ++ [t || w.getD P.output false])
          (z.getD Q.output false || z.getD r false) = f t x)
    (deleted :
      let edge := fun x : Fin 8 → Bool =>
        ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any fun e =>
          x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))
      ∀ D : Circuit, FanInTwo D → D.size ≤ 12 → D.gates.countP (fun g => g.op.eval [false]) ≤ 1 →
        ∃ x : Fin 8 → Bool, D.eval (List.ofFn x ++ [x 0 || x 3]) ≠ edge x)
    (paired :
      let hit := fun (l : List ℕ) (x : Fin 8 → Bool) =>
        l.any fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))
      let h := hit [1,12,23,4,15,26,37,46,57,74]
      let c := hit [12,15,26,46,57,74]
      let seed := fun x : Fin 8 → Bool => List.ofFn x ++ [x 0 || x 3]
      ∀ (P Q : Circuit) (r : ℕ), FanInTwo P → FanInTwo Q → P.size + Q.size ≤ 12 →
        P.gates.countP (fun g => g.op.eval [false]) +
          Q.gates.countP (fun g => g.op.eval [false]) ≤ 1 →
        9 ≤ P.output → (∀ x, (x 0 || x 3) = true → h x = false → P.eval (seed x) = false) →
        ∃ x : Fin 8 → Bool, let w := P.wires (seed x)
          let out := fun b => let z := Q.wires (w ++ [b])
                              z.getD Q.output false || z.getD r false
          out (w.getD P.output false) ≠ h x ∨ out true ≠ (c x || x 0 || x 3)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false || x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro gs a b length fan few _ _
  by_contra! good
  let hit := fun (l : List ℕ) (x : Fin 8 → Bool) =>
    l.any fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))
  let h := hit [1,12,23,4,15,26,37,46,57,74]
  let c := hit [12,15,26,46,57,74]
  let f (x : Fin 9 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let read (w : List Bool) := w.getD a false || w.getD b false
  have correct (x : Fin 9 → Bool) :
      read (gs.foldl step (List.ofFn x ++ [x 0 || x 3])) = f x :=
    Classical.not_not.mp (good x)
  have stable (ls : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (ls.foldl step w).getD i false = w.getD i false := by
    induction ls generalizing w with
    | nil => rfl
    | cons g ls ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  let single := fun j : Fin 9 => decide (j = 4)
  let ws := List.ofFn single ++ [single 0 || single 3]
  have off : read (gs.foldl step ws) = false := (correct single).trans (by decide)
  have on4 : (gs.foldl step ws).getD 4 false = true :=
    (stable gs ws 4 (by simp [ws])).trans (by decide)
  have ab : a ≠ 4 ∧ b ≠ 4 := by
    simp only [read, Bool.or_eq_false_iff] at off
    exact ⟨fun e => Bool.noConfusion ((e ▸ off.1).symm.trans on4),
           fun e => Bool.noConfusion ((e ▸ off.2).symm.trans on4)⟩
  let lift (x : Fin 8 → Bool) : Fin 9 → Bool := Fin.lastCases (x 0 || x 3) x
  let seed (x : Fin 8 → Bool) := List.ofFn x ++ [x 0 || x 3]
  have seed_eq (x : Fin 8 → Bool) : List.ofFn (lift x) = seed x := by
    rw [List.ofFn_succ_last]
    simp [lift,seed]
    rfl
  let expand (t : Bool) (x : Fin 8 → Bool) : Fin 9 → Bool := (4 : Fin 9).insertNth t x
  have insert_eq : ∀ (t : Bool) (x : Fin 8 → Bool),
      List.ofFn ((4 : Fin 10).insertNth t (lift x)) =
        List.ofFn (expand t x) ++ [expand t x 0 || expand t x 3] := by decide +kernel
  have cofactors : ∀ x : Fin 8 → Bool, f (expand false x) = h x ∧
      f (expand true x) = (c x || x 0 || x 3) := by decide +kernel
  let value (t : Bool) (y : Fin 9 → Bool) :=
    read (gs.foldl step (List.ofFn ((4 : Fin 10).insertNth t y)))
  have valid (x : Fin 8 → Bool) (t : Bool) :
      value t (lift x) = f (expand t x) := by
    unfold value
    rw [insert_eq]
    exact correct _
  have sensitive : ∃ y, value false y ≠ value true y := by
    refine ⟨lift (fun i => decide (i=0)), ?_⟩
    rw [valid (fun i => decide (i=0)) false, valid (fun i => decide (i=0)) true]
    decide
  have varies : ∃ y z, value false y ≠ value false z := by
    refine ⟨lift (fun _ => false), lift (fun _ => true), ?_⟩
    rw [valid (fun _ => false) false, valid (fun _ => true) false]
    decide
  rcases peel gs a b fan ab.1 ab.2 sensitive varies with
    ⟨D, fD, sD, nD, eD⟩ | ⟨P, Q, r, fP, fQ, sz, nn, eq⟩
  · obtain ⟨x,hx⟩ := deleted D fD (by omega) (nD.trans few)
    apply hx
    have e := congrFun eD (lift x)
    change D.eval (List.ofFn (lift x)) = value false (lift x) at e
    rw [seed_eq] at e
    exact e.trans ((valid x false).trans (cofactors x).1)
  · let out (x : Fin 8 → Bool) (t : Bool) :=
      let z := Q.wires (P.wires (seed x) ++ [t])
      z.getD Q.output false || z.getD r false
    have vals (x : Fin 8 → Bool) :
        out x (P.eval (seed x)) = h x ∧ out x true = (c x || x 0 || x 3) := by
      have hv (t : Bool) := eq (lift x) t
      change ∀ t, (let w := P.wires (List.ofFn (lift x))
                    let z := Q.wires (w ++ [t || w.getD P.output false])
                    z.getD Q.output false || z.getD r false) = value t (lift x) at hv
      rw [seed_eq] at hv
      exact ⟨(hv false).trans ((valid x false).trans (cofactors x).1),
             (hv true).trans ((valid x true).trans (cofactors x).2)⟩
    have guard (x : Fin 8 → Bool) (hs : (x 0 || x 3) = true) (hh : h x = false) :
        P.eval (seed x) = false := by
      have lo := (vals x).1
      have hi := (vals x).2
      rw [hh] at lo
      rw [Bool.or_assoc,hs,Bool.or_true] at hi
      cases e : P.eval (seed x) <;> simp_all
    have late : 9 ≤ P.output := by
      by_contra! small
      let i : Fin 9 := ⟨P.output,small⟩
      have separating : ∀ j : Fin 9, ∃ x : Fin 8 → Bool,
          (x 0 || x 3) = true ∧ h x = false ∧ (seed x).getD j.val false = true := by
        decide +kernel
      obtain ⟨x,hs,hh,hr⟩ := separating i
      have e := guard x hs hh
      change (P.gates.foldl step (seed x)).getD P.output false = false at e
      rw [stable _ _ _ (by simpa [seed] using small)] at e
      exact Bool.noConfusion (hr.symm.trans e)
    obtain ⟨x,hx⟩ := paired P Q r fP fQ (by omega) (nn.trans few) late guard
    exact hx.elim (fun ne => ne (vals x).1) (fun ne => ne (vals x).2)
