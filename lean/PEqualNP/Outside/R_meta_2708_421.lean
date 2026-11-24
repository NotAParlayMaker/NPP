import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2708_421
    (wireSupport : ∀ (n : ℕ) (C : Circuit) (i : ℕ), Monotone2 C → i < n + C.size →
      ∃ S : Finset (Fin n), S.card ≤ i + 1 - n + 1 ∧
        ∀ (x y : Fin n → Bool), (∀ v ∈ S, x v = y v) →
          (C.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn y)).getD i false)
    (residual : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size → (19 : ℕ) ≤ x2 → (19 : ℕ) ≤ x3 →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → (26 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∧ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∨ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), ¬x8 x12 ∧ x9 x2 x12 = Bool.false ∧ x9 x3 x12 = Bool.true) → (∃ (x13 : Fin (14 : ℕ) → Bool), ¬x8 x13 ∧ x9 x3 x13 = Bool.false ∧ x9 x2 x13 = Bool.true) → (26 : ℕ) ≤ x1.size := by
  intro C a b hC ha hb edges positive read hpos hneg hA hB
  let left (i : Fin 7) : Fin 14 := ⟨i.val, by have := i.isLt; omega⟩
  let right (i : Fin 7) : Fin 14 := Fin.ofNat 14 (([7,9,8,12,13,10,11] : List ℕ).getD i.val 7)
  have leftLt (i : Fin 7) : (left i).val < 7 := i.isLt
  have rightGe : ∀ i : Fin 7, 7 ≤ (right i).val := by
    change ∀ i : Fin 7, 7 ≤ (Fin.ofNat 14 (([7,9,8,12,13,10,11] : List ℕ).getD i.val 7)).val
    decide
  have leftInj : Function.Injective left := by
    intro i j eq
    have he : (left i).val = (left j).val := congrArg (fun v : Fin 14 => v.val) eq
    exact Fin.ext he
  have rightInj : Function.Injective right := by
    change ∀ i j : Fin 7, (Fin.ofNat 14 (([7,9,8,12,13,10,11] : List ℕ).getD i.val 7)) =
      (Fin.ofNat 14 (([7,9,8,12,13,10,11] : List ℕ).getD j.val 7)) → i = j
    decide
  have edgeMem : ∀ i : Fin 7, ((left i).val, (right i).val) ∈ edges := by
    change ∀ i : Fin 7, (i.val, (Fin.ofNat 14 (([7,9,8,12,13,10,11] : List ℕ).getD i.val 7)).val) ∈
      ([((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] : List (ℕ × ℕ))
    decide

  classical
  have uncovered (S : Finset (Fin 14)) (hS : S.card ≤ 6) :
      ∃ u v : Fin 14, (u.val,v.val) ∈ edges ∧ u ∉ S ∧ v ∉ S := by
    by_contra allHit
    have hit (i : Fin 7) : left i ∈ S ∨ right i ∈ S := by
      by_cases h : left i ∈ S
      · exact Or.inl h
      · right
        by_contra hr
        exact allHit ⟨left i, right i, edgeMem i, h, hr⟩
    let selected (i : Fin 7) : Fin 14 := if left i ∈ S then left i else right i
    have selMem (i : Fin 7) : selected i ∈ S := by
      by_cases hl : left i ∈ S
      · simpa only [selected, ite_eq_left hl] using hl
      · have hr := (hit i).resolve_left hl
        simpa only [selected, ite_eq_right hl] using hr
    have selInj : Function.Injective selected := by
      intro i j eq
      by_cases hi : left i ∈ S <;> by_cases hj : left j ∈ S
      · apply leftInj
        simpa only [selected, ite_eq_left hi, ite_eq_left hj] using eq
      · have he : (left i).val = (right j).val := congrArg Fin.val (by
          simpa only [selected, ite_eq_left hi, ite_eq_right hj] using eq)
        have := leftLt i
        have := rightGe j
        omega
      · have he : (right i).val = (left j).val := congrArg Fin.val (by
          simpa only [selected, ite_eq_right hi, ite_eq_left hj] using eq)
        have := rightGe i
        have := leftLt j
        omega
      · apply rightInj
        simpa only [selected, ite_eq_right hi, ite_eq_right hj] using eq
    let picked := (Finset.univ : Finset (Fin 7)).image selected
    have sub : picked ⊆ S := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact selMem i
    have card : picked.card = 7 := by
      simp [picked, Finset.card_image_of_injective _ selInj]
    have le := Finset.card_le_card sub
    omega

  have late (i : ℕ) (hi : i < 14 + C.size)
      (accept : ∀ x, positive x → read i x = true)
      (reject : ∃ x, read i x = false) : 19 ≤ i := by
    by_contra small
    obtain ⟨S, hSize, dep⟩ := wireSupport 14 C i hC hi
    obtain ⟨u, v, he, hu, hv⟩ := uncovered S (by omega)
    obtain ⟨x, hx⟩ := reject
    let y (j : Fin 14) : Bool := if j ∈ S then x j else true
    have hp : positive y := ⟨u,v,he,by simp only [y, ite_eq_right hu],
      by simp only [y, ite_eq_right hv]⟩
    have same : read i x = read i y := dep x y (by intro j hj; simp [y,hj])
    rw [hx, accept y hp] at same
    contradiction
  have la : 19 ≤ a := late a ha (fun x h => (hpos x h).1) (by
    obtain ⟨x, _, hx, _⟩ := hA
    exact ⟨x,hx⟩)
  have lb : 19 ≤ b := late b hb (fun x h => (hpos x h).2) (by
    obtain ⟨x, _, hx, _⟩ := hB
    exact ⟨x,hx⟩)
  exact residual C a b hC ha hb la lb hpos hneg hA hB
