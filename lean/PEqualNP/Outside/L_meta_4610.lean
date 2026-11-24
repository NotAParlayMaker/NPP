import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4610 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ),   x2 x3 x4 x5 →     have x8 : List ℕ := List.map (fun (x8 : ℕ) => x8 &&& x4) x3;     x1 x8 x6 → x5 &&& x4 ∈ x8 ++ x6 → ∃ (x11 : List ℕ), x11.length ≤ x6.length ∧ x1 x3 x11 ∧ x5 ∈ x3 ++ x11 := by
  intro x1 x2 L a b M hx2 L' hM hmem
  classical
  choose σ hσa hσb hσL using hx2
  let R : ℕ → Prop := fun y => ∀ p, if b.testBit p = true then y.testBit (σ p) = true →
    y.testBit p = true else y.testBit p = true → y.testBit (σ p) = true
  have RL : ∀ y ∈ L, R y := fun y hy p => hσL p y hy
  have Rand : ∀ y z, R y → R z → R (y &&& z) := by
    intro y z hy hz p
    have h1 := hy p
    have h2 := hz p
    rw [Nat.testBit_and, Nat.testBit_and]
    revert h1 h2
    cases b.testBit p <;> cases y.testBit p <;> cases y.testBit (σ p) <;>
      cases z.testBit p <;> cases z.testBit (σ p) <;> simp
  have Ror : ∀ y z, R y → R z → R (y ||| z) := by
    intro y z hy hz p
    have h1 := hy p
    have h2 := hz p
    rw [Nat.testBit_or, Nat.testBit_or]
    revert h1 h2
    cases b.testBit p <;> cases y.testBit p <;> cases y.testBit (σ p) <;>
      cases z.testBit p <;> cases z.testBit (σ p) <;> simp
  have dand : ∀ y1 y2 : ℕ, (y1 &&& y2) &&& a = (y1 &&& a) &&& (y2 &&& a) := by
    intro y1 y2
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases y1.testBit i <;> cases y2.testBit i <;> cases a.testBit i <;> rfl
  have dor : ∀ y1 y2 : ℕ, (y1 ||| y2) &&& a = (y1 &&& a) ||| (y2 &&& a) := by
    intro y1 y2
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases y1.testBit i <;> cases y2.testBit i <;> cases a.testBit i <;> rfl
  have key : ∀ k, k ≤ M.length → ∃ N : List ℕ, N.length = k ∧ x1 L N ∧
      ∀ z ∈ L' ++ M.take k, ∃ y ∈ L ++ N, y &&& a = z ∧ R y := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], rfl, ?_, ?_⟩
      · intro i
        exact absurd i.2 (by simp)
      · intro z hz
        simp only [List.take_zero, List.append_nil] at hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
        exact ⟨y, by simpa using hy, rfl, RL y hy⟩
    | succ k ih =>
      intro hk
      obtain ⟨N, hN, hNx, hNz⟩ := ih (by omega)
      obtain ⟨z1, hz1, z2, hz2, hop⟩ := hM ⟨k, by omega⟩
      obtain ⟨y1, hy1, e1, r1⟩ := hNz z1 hz1
      obtain ⟨y2, hy2, e2, r2⟩ := hNz z2 hz2
      have hex : ∃ y, (y = y1 &&& y2 ∨ y = y1 ||| y2) ∧
          y &&& a = M.get ⟨k, by omega⟩ ∧ R y := by
        rcases hop with h | h
        · refine ⟨y1 &&& y2, Or.inl rfl, ?_, Rand _ _ r1 r2⟩
          rw [h, ← e1, ← e2, dand]
        · refine ⟨y1 ||| y2, Or.inr rfl, ?_, Ror _ _ r1 r2⟩
          rw [h, ← e1, ← e2, dor]
      obtain ⟨y, hyop, hya, hyR⟩ := hex
      refine ⟨N ++ [y], by simp [hN], ?_, ?_⟩
      · intro i
        have hi : i.val < k + 1 := by simpa [hN] using i.2
        by_cases hik : i.val < k
        · obtain ⟨u, hu, v, hv, h⟩ := hNx ⟨i.val, by omega⟩
          have ht : List.take i.val (N ++ [y]) = List.take i.val N :=
            List.take_append_of_le_length (by omega)
          have hg : (N ++ [y]).get i = N.get ⟨i.val, by omega⟩ := by
            simp only [List.get_eq_getElem]
            exact List.getElem_append_left (by omega)
          refine ⟨u, ?_, v, ?_, ?_⟩
          · rw [ht]; exact hu
          · rw [ht]; exact hv
          · rw [hg]; exact h
        · have hik' : i.val = k := by omega
          have ht : List.take i.val (N ++ [y]) = N := List.take_left' (by omega)
          have hg : (N ++ [y]).get i = y := by
            simp only [List.get_eq_getElem]
            rw [List.getElem_append_right (by omega)]
            simp
          refine ⟨y1, ?_, y2, ?_, ?_⟩
          · rw [ht]; exact hy1
          · rw [ht]; exact hy2
          · rw [hg]; exact hyop
      · intro z hz
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)] at hz
        simp only [Option.toList_some, ← List.append_assoc, List.mem_append,
          List.mem_singleton] at hz
        rcases hz with hz | hz
        · obtain ⟨w, hw, ew, rw'⟩ := hNz z (List.mem_append.2 hz)
          refine ⟨w, ?_, ew, rw'⟩
          rw [← List.append_assoc]
          exact List.mem_append_left _ hw
        · refine ⟨y, by simp, ?_, hyR⟩
          rw [hz, hya]
          rfl
  obtain ⟨N, hN, hNx, hNz⟩ := key M.length le_rfl
  rw [List.take_length] at hNz
  obtain ⟨y, hy, ey, ry⟩ := hNz _ hmem
  have hyb : y = b := by
    apply Nat.eq_of_testBit_eq
    intro p
    have h1 := ry p
    have h2 := hσa p
    have h3 := hσb p
    have h4 := congrArg (fun t => Nat.testBit t (σ p)) ey
    simp only [Nat.testBit_and, h2, Bool.and_true] at h4
    rw [h3] at h4
    revert h1 h4
    cases b.testBit p <;> cases y.testBit p <;> cases y.testBit (σ p) <;> simp
  exact ⟨N, by omega, hNx, hyb ▸ hy⟩
