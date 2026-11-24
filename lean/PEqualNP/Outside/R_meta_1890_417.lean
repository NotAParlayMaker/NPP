import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1890_417
    (peel :
      let q := fun x : Fin 10 → Bool => x 0 && x 2
      let feature := fun (code : ℕ) (x : Fin 10 → Bool) =>
            let read := fun i : ℕ => (List.ofFn x ++ [q x, false, true]).getD i false
            let a := read (code % 169 / 13)
            let b := read (code % 13)
            if code / 169 = 0 then a && b else if code / 169 = 1 then a || b else !a
      ∀ (C : Circuit) (p : Fin 10 → Fin 10), FanInTwo C →
        ∃ c : Fin 507, ∀ s : Fin 10 → Fin 10, ∃ D : Circuit,
          FanInTwo D ∧ D.size = C.size - 1 ∧ ∀ x : Fin 10 → Bool,
          C.eval (List.ofFn ((x ∘ s) ∘ p) ++ [q (x ∘ s)]) =
          D.eval (List.ofFn x ++ [q (x ∘ s), feature c.val (x ∘ s)]))
    (orbits :
      let q := fun x : Fin 10 → Bool => x 0 && x 2
      let feature := fun (code : ℕ) (x : Fin 10 → Bool) =>
            let read := fun i : ℕ => (List.ofFn x ++ [q x, false, true]).getD i false
            let a := read (code % 169 / 13)
            let b := read (code % 13)
            if code / 169 = 0 then a && b else if code / 169 = 1 then a || b else !a
      let target := fun x : Fin 10 → Bool =>
            let v := List.ofFn x
            ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e => v.getD (e / 10) false && v.getD (e % 10) false
      let reps := ({e : ℕ | (([11092315, 261120, 22020096, 458752, 67112960, 1375911168, 133169153, 2147483648, 201326594, 0, 2147745792, 33554432, 0, 67108865, 1048576] : List ℕ).getD (e / 32) 0).testBit (e % 32) = true} : Set ℕ)
      ∀ c : ℕ, ∃ e ∈ reps, ∃ s : Fin 10 → Fin 10,
        (∀ x : Fin 10 → Bool, q (x ∘ s) = q x) ∧
        (∀ x : Fin 10 → Bool, target (x ∘ s) = target x) ∧
        ∀ x : Fin 10 → Bool, feature c (x ∘ s) = feature e x)
    (residual :
      let q := fun x : Fin 10 → Bool => x 0 && x 2
      let feature := fun (code : ℕ) (x : Fin 10 → Bool) =>
            let read := fun i : ℕ => (List.ofFn x ++ [q x, false, true]).getD i false
            let a := read (code % 169 / 13)
            let b := read (code % 13)
            if code / 169 = 0 then a && b else if code / 169 = 1 then a || b else !a
      let target := fun x : Fin 10 → Bool =>
            let v := List.ofFn x
            ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e => v.getD (e / 10) false && v.getD (e % 10) false
      let reps := ({e : ℕ | (([11092315, 261120, 22020096, 458752, 67112960, 1375911168, 133169153, 2147483648, 201326594, 0, 2147745792, 33554432, 0, 67108865, 1048576] : List ℕ).getD (e / 32) 0).testBit (e % 32) = true} : Set ℕ)
      ∀ D : Circuit, FanInTwo D → D.size ≤ 17 → ∀ e ∈ reps,
        ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [q x, feature e x]) ≠ target x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  let q := fun x : Fin 10 → Bool => x 0 && x 2
  let feature := fun (code : ℕ) (x : Fin 10 → Bool) =>
        let read := fun i : ℕ => (List.ofFn x ++ [q x, false, true]).getD i false
        let a := read (code % 169 / 13)
        let b := read (code % 13)
        if code / 169 = 0 then a && b else if code / 169 = 1 then a || b else !a
  let target := fun x : Fin 10 → Bool =>
        let v := List.ofFn x
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e => v.getD (e / 10) false && v.getD (e % 10) false
  intro circuit p fan bound
  by_contra noWitness
  have sameTarget (x : Fin 10 → Bool) : target x = (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x := by
    change ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) || ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false))))))))))))))) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
    simp only [Bool.or_false, Bool.or_assoc]
  have correct (x : Fin 10 → Bool) :
      circuit.eval (List.ofFn (x ∘ p) ++ [q x]) = target x :=
    Classical.byContradiction (fun h => noWitness ⟨x, fun original => h (original.trans (sameTarget x).symm)⟩)
  obtain ⟨c, tailModel⟩ := peel circuit p fan
  obtain ⟨e, he, s, hq, ht, hf⟩ := orbits c.val
  obtain ⟨D, hD, lengthD, represents⟩ := tailModel s
  obtain ⟨x, hx⟩ := residual D hD (by omega) e he
  apply hx
  have hc := correct (x ∘ s)
  have hr := represents x
  change circuit.eval (List.ofFn ((x ∘ s) ∘ p) ++ [q (x ∘ s)]) =
    D.eval (List.ofFn x ++ [q (x ∘ s), feature c.val (x ∘ s)]) at hr
  have aq : q (x ∘ s) = q x := hq x
  have af : feature c.val (x ∘ s) = feature e x := hf x
  have atgt : target (x ∘ s) = target x := ht x
  rw [aq, af] at hr
  rw [aq, atgt] at hc
  exact hr.symm.trans hc
