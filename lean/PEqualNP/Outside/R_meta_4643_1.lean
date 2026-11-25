import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Failure of the masked goal is the normal form below: on the side v = b, and on every
-- input whose wire k is !b, the circuit already agrees with the edge function. The two
-- children are that normal form at the first gate wire and at every later wire.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4643_1
    (c10 :
      let F : (Fin 9 → Bool) → Bool := fun x =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
          x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let row : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      let W : Circuit → (Fin 9 → Bool) → Bool := fun C x => (C.wires (row x)).getD 10 false
      ∀ (v : Fin 9) (C : Circuit) (b : Bool),
        v ≠ 0 → v ≠ 6 → FanInTwo C → C.size = 13 → C.output = 22 →
        (b = false → v = 1 ∨ v = 4 ∨ v = 7) →
        (∀ g ∈ C.gates.take 1, v.val ∉ g.inputs) →
        (∀ x y : Fin 9 → Bool, (∀ u, u ≠ v → x u = y u) → F x ≠ F y → W C x = !b) →
        (∃ g ∈ C.gates, 9 ∈ g.inputs) →
        (∃ x, x v = !b ∧ W C x = b ∧ C.eval (row x) ≠ F x) →
        (∀ x, x v = b → C.eval (row x) = F x) →
        (∀ x, W C x = !b → C.eval (row x) = F x) →
        ∃ x, C.eval ((row x).set v.val (if b = true then x v || W C x else x v && W C x)) ≠ F x)
    (cHi :
      let F : (Fin 9 → Bool) → Bool := fun x =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
          x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let row : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      let W : Circuit → ℕ → (Fin 9 → Bool) → Bool := fun C k x => (C.wires (row x)).getD k false
      ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (b : Bool),
        v ≠ 0 → v ≠ 6 → FanInTwo C → C.size = 13 → C.output = 22 →
        10 < k → k < 22 →
        (∀ g ∈ C.gates.take (k + 1 - 10), v.val ∉ g.inputs) →
        (∀ x y : Fin 9 → Bool, (∀ u, u ≠ v → x u = y u) → F x ≠ F y → W C k x = !b) →
        (∃ g ∈ C.gates, 9 ∈ g.inputs) →
        (∃ x, x v = !b ∧ W C k x = b ∧ C.eval (row x) ≠ F x) →
        (∀ x, x v = b → C.eval (row x) = F x) →
        (∀ x, W C k x = !b → C.eval (row x) = F x) →
        ∃ x, C.eval ((row x).set v.val (if b = true then x v || W C k x else x v && W C k x)) ≠ F x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Fin (9 : ℕ) → Bool) => (x3.wires (x2 x5)).getD x4 Bool.false; ∀ (x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Bool), x4 ≠ (0 : Fin (9 : ℕ)) → x4 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x5 → x5.size = (13 : ℕ) → x5.output = (22 : ℕ) → (10 : ℕ) ≤ x6 → x6 < (22 : ℕ) → (x7 = Bool.false → x6 = (10 : ℕ) → x4 = (1 : Fin (9 : ℕ)) ∨ x4 = (4 : Fin (9 : ℕ)) ∨ x4 = (7 : Fin (9 : ℕ))) → (∀ x16 ∈ List.take (x6 + (1 : ℕ) - (10 : ℕ)) x5.gates, ↑x4 ∉ x16.inputs) → (∀ (x17 x18 : Fin (9 : ℕ) → Bool), (∀ (x19 : Fin (9 : ℕ)), x19 ≠ x4 → x17 x19 = x18 x19) → x1 x17 ≠ x1 x18 → x3 x5 x6 x17 = !x7) → (∃ x18 ∈ x5.gates, (9 : ℕ) ∈ x18.inputs) → (∃ (x19 : Fin (9 : ℕ) → Bool), x19 x4 = !x7 ∧ x3 x5 x6 x19 = x7 ∧ x5.eval (x2 x19) ≠ x1 x19) → ∃ (x20 : Fin (9 : ℕ) → Bool), x5.eval ((x2 x20).set (↑x4) (if x7 = Bool.true then x20 x4 || x3 x5 x6 x20 else x20 x4 && x3 x5 x6 x20)) ≠ x1 x20 := by
  intro F row W v C k b hv0 hv6 hfan hsize hout hklo hkhi hguard havoid hsens hread hbad
  by_contra hgoal
  have fixed (x : Fin 9 → Bool) :
      C.eval ((row x).set (↑v) (if b = Bool.true then x v || W C k x else x v && W C k x)) = F x := by
    by_contra hne
    apply hgoal
    exact ⟨x, hne⟩
  have row_pivot (x : Fin 9 → Bool) (i : Fin 9) : (row x).getD i.val false = x i := by
    have hrow : row x = List.ofFn x ++ [x 0 || x 6] := rfl
    rw [hrow, List.getD_append _ _ _ _ (by simp),
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have set_self (x : Fin 9 → Bool) (i : Fin 9) : (row x).set i.val (x i) = row x := by
    have room : i.val < (row x).length := by
      have hrow : row x = List.ofFn x ++ [x 0 || x 6] := rfl
      rw [hrow]
      simp
      have := i.isLt
      omega
    have read : (row x)[i.val] = x i := by
      rw [← List.getD_eq_getElem _ false room, row_pivot]
    rw [← read, List.set_getElem_self room]
  have mask_self (p q : Bool) (hside : p = b ∨ q = !b) :
      (if b = Bool.true then p || q else p && q) = p := by
    cases b
    · cases hside with
      | inl hp =>
        subst hp
        cases q <;> rfl
      | inr hq =>
        subst hq
        cases p <;> rfl
    · cases hside with
      | inl hp =>
        subst hp
        cases q <;> rfl
      | inr hq =>
        subst hq
        cases p <;> rfl
  have on_side : ∀ x : Fin 9 → Bool, x v = b → C.eval (row x) = F x := by
    intro x hx
    have hm := mask_self (x v) (W C k x) (Or.inl hx)
    have hs := set_self x v
    have hag := fixed x
    rw [hm, hs] at hag
    exact hag
  have on_free : ∀ x : Fin 9 → Bool, W C k x = !b → C.eval (row x) = F x := by
    intro x hx
    have hm := mask_self (x v) (W C k x) (Or.inr hx)
    have hs := set_self x v
    have hag := fixed x
    rw [hm, hs] at hag
    exact hag
  by_cases hk : k = 10
  · subst hk
    have hav : ∀ g ∈ C.gates.take 1, ↑v ∉ g.inputs := by
      simpa using havoid
    have hgv : b = false → v = 1 ∨ v = 4 ∨ v = 7 := by
      intro hb
      exact hguard hb rfl
    have got := c10 v C b hv0 hv6 hfan hsize hout hgv hav hsens hread hbad on_side on_free
    exact hgoal got
  · have hlt : 10 < k := by omega
    have got := cHi v C k b hv0 hv6 hfan hsize hout hlt hkhi havoid hsens hread hbad on_side on_free
    exact hgoal got
