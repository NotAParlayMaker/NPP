import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1999_487
    (restrict : ∀ (m n : ℕ) (R : Fin m → Fin n → Prop) [DecidableRel R] (C : Circuit),
      Monotone2 C →
      (∀ (x : Fin m → Bool) (y : Fin n → Bool), C.eval (List.ofFn x ++ List.ofFn y) =
        decide (∃ i j, R i j ∧ x i = true ∧ y j = true)) →
      ∀ (A : Finset (Fin m)) (B : Finset (Fin n)),
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 1 ∧
        ∀ (x : Fin m → Bool) (y : Fin n → Bool), D.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ i j, (i ∈ A ∧ j ∈ B ∧ R i j) ∧ x i = true ∧ y j = true))
    (dense : ∃ (k c : ℕ), 3 ≤ k ∧ ∀ (m n : ℕ) (R : Fin m → Fin n → Prop) [DecidableRel R],
      (∀ i, (Finset.univ.filter (R i)).card = 0 ∨ k ≤ (Finset.univ.filter (R i)).card) →
      (∀ j, (Finset.univ.filter (Function.swap R j)).card = 0 ∨
        k ≤ (Finset.univ.filter (Function.swap R j)).card) →
      (∀ i i' j j', R i j → R i' j → R i j' → R i' j' → i = i' ∨ j = j') →
      ∀ C : Circuit, Monotone2 C →
      (∀ (x : Fin m → Bool) (y : Fin n → Bool), C.eval (List.ofFn x ++ List.ofFn y) =
        decide (∃ i j, R i j ∧ x i = true ∧ y j = true)) →
      (∑ i, (Finset.univ.filter (R i)).card) ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ x1 * (x9.size + (1 : ℕ)) := by
  have peel : ∀ (k m n : ℕ) (R : Fin m → Fin n → Prop) [DecidableRel R],
        ∃ (A : Finset (Fin m)) (B : Finset (Fin n)),
          let S := fun (i : Fin m) (j : Fin n) => i ∈ A ∧ j ∈ B ∧ R i j
          (∀ i, (Finset.univ.filter (S i)).card = 0 ∨ k ≤ (Finset.univ.filter (S i)).card) ∧
          (∀ j, (Finset.univ.filter (Function.swap S j)).card = 0 ∨
            k ≤ (Finset.univ.filter (Function.swap S j)).card) ∧
          (∑ i, (Finset.univ.filter (R i)).card) ≤
            (∑ i, (Finset.univ.filter (S i)).card) +
              (k - 1) * ((Finset.univ.filter fun i => ∃ j, R i j).card +
                (Finset.univ.filter fun j => ∃ i, R i j).card) := by
    intro k m n R _
    let row (A : Finset (Fin m)) (B : Finset (Fin n)) (i : Fin m) :=
      (Finset.univ.filter fun j => i ∈ A ∧ j ∈ B ∧ R i j).card
    let col (A : Finset (Fin m)) (B : Finset (Fin n)) (j : Fin n) :=
      (Finset.univ.filter fun i => i ∈ A ∧ j ∈ B ∧ R i j).card
    let edges (A : Finset (Fin m)) (B : Finset (Fin n)) := ∑ i, row A B i
    have countCols (A : Finset (Fin m)) (B : Finset (Fin n)) :
        edges A B = ∑ j, col A B j := by
      simp only [edges, row, col, Finset.card_filter]
      exact Finset.sum_comm
    have eraseRow (A : Finset (Fin m)) (B : Finset (Fin n)) (i : Fin m) :
        edges A B = edges (A.erase i) B + row A B i := by
      calc
        edges A B = ∑ t : Fin m, (row (A.erase i) B t + if t = i then row A B i else 0) := by
          apply Finset.sum_congr rfl
          intro t _
          by_cases ht : t = i
          · subst t
            simp [row]
          · simp [row, Finset.mem_erase, ht]
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp [edges]
    have eraseCol (A : Finset (Fin m)) (B : Finset (Fin n)) (j : Fin n) :
        edges A B = edges A (B.erase j) + col A B j := by
      rw [countCols A B, countCols A (B.erase j)]
      calc
        (∑ t : Fin n, col A B t) =
            ∑ t : Fin n, (col A (B.erase j) t + if t = j then col A B j else 0) := by
          apply Finset.sum_congr rfl
          intro t _
          by_cases ht : t = j
          · subst t
            simp [col]
          · simp [col, Finset.mem_erase, ht]
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp
    have findCore (q : ℕ) :
        ∀ (A : Finset (Fin m)) (B : Finset (Fin n)), A.card + B.card = q →
          ∃ (A' : Finset (Fin m)) (B' : Finset (Fin n)),
            (∀ i, row A' B' i = 0 ∨ k ≤ row A' B' i) ∧
            (∀ j, col A' B' j = 0 ∨ k ≤ col A' B' j) ∧
            edges A B ≤ edges A' B' + (k - 1) * q := by
      induction q using Nat.strong_induction_on with
      | ind q smaller =>
        intro A B hq
        by_cases stable :
            (∀ i, row A B i = 0 ∨ k ≤ row A B i) ∧
            (∀ j, col A B j = 0 ∨ k ≤ col A B j)
        · exact ⟨A, B, stable.1, stable.2, by omega⟩
        have step : ∃ (A' : Finset (Fin m)) (B' : Finset (Fin n)),
            A'.card + B'.card + 1 = q ∧ edges A B ≤ edges A' B' + (k - 1) := by
          rcases not_and_or.mp stable with hr | hc
          · push Not at hr
            obtain ⟨i, hNonzero, hSmall⟩ := hr
            have hi : i ∈ A := by
              by_contra h
              exact hNonzero (by simp [row, h])
            refine ⟨A.erase i, B, ?_, ?_⟩
            · rw [Finset.card_erase_of_mem hi]
              have := Finset.card_pos.mpr ⟨i, hi⟩
              omega
            · rw [eraseRow A B i]
              omega
          · push Not at hc
            obtain ⟨j, hNonzero, hSmall⟩ := hc
            have hj : j ∈ B := by
              by_contra h
              exact hNonzero (by simp [col, h])
            refine ⟨A, B.erase j, ?_, ?_⟩
            · rw [Finset.card_erase_of_mem hj]
              have := Finset.card_pos.mpr ⟨j, hj⟩
              omega
            · rw [eraseCol A B j]
              omega
        obtain ⟨A', B', hSize, hRemoved⟩ := step
        obtain ⟨A'', B'', hRows, hCols, hBudget⟩ :=
          smaller (A'.card + B'.card) (by omega) A' B' rfl
        refine ⟨A'', B'', hRows, hCols, ?_⟩
        calc
          edges A B ≤ edges A' B' + (k - 1) := hRemoved
          _ ≤ edges A'' B'' + (k - 1) * (A'.card + B'.card) + (k - 1) :=
            Nat.add_le_add_right hBudget _
          _ = edges A'' B'' + (k - 1) * q := by
            rw [← hSize, Nat.mul_succ, Nat.add_assoc]
    let A := Finset.univ.filter fun i => ∃ j, R i j
    let B := Finset.univ.filter fun j => ∃ i, R i j
    have initial : edges A B = ∑ i, (Finset.univ.filter (R i)).card := by
      apply Finset.sum_congr rfl
      intro i _
      unfold row
      congr 1
      ext j
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2.2, fun h => ⟨⟨j, h⟩, ⟨i, h⟩, h⟩⟩
    obtain ⟨A', B', hRows, hCols, hBudget⟩ := findCore (A.card + B.card) A B rfl
    refine ⟨A', B', hRows, hCols, ?_⟩
    rw [initial] at hBudget
    exact hBudget
  have support : ∀ (m n : ℕ) (R : Fin m → Fin n → Prop) [DecidableRel R] (C : Circuit),
        Monotone2 C →
        (∀ (x : Fin m → Bool) (y : Fin n → Bool), C.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ i j, R i j ∧ x i = true ∧ y j = true)) →
        (Finset.univ.filter fun i => ∃ j, R i j).card +
          (Finset.univ.filter fun j => ∃ i, R i j).card ≤ 2 * (C.size + 1) := by
    intro m n R _ C hMono hComputes
    let references := C.output :: C.gates.flatMap Gate.inputs
    have lengthBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
        (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        have head := h g (by simp)
        have tail := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega
    have refsLength : references.length ≤ 2 * (C.size + 1) := by
      have bound := lengthBound C.gates (fun g hg => (hMono g hg).2)
      simp only [references, List.length_cons, Circuit.size]
      omega
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have foldAgree (p : ℕ) (gs : List Gate) (noRead : ∀ g ∈ gs, p ∉ g.inputs)
        (a b : List Bool) (hlen : a.length = b.length)
        (agree : ∀ q : ℕ, q ≠ p → a.getD q false = b.getD q false) :
        ∀ q : ℕ, q ≠ p → (gs.foldl step a).getD q false = (gs.foldl step b).getD q false := by
      induction gs generalizing a b with
      | nil => exact agree
      | cons g gs ih =>
        simp only [List.foldl_cons]
        have sameRead : (g.inputs.map fun i => a.getD i false) =
            (g.inputs.map fun i => b.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact agree i (fun e => noRead g (by simp) (e ▸ hi))
        apply ih (fun t ht => noRead t (List.mem_cons_of_mem _ ht))
        · simp [step, hlen]
        intro q hq
        simp only [step, sameRead]
        by_cases inInput : q < a.length
        · have rightInput : q < b.length := by omega
          simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left inInput,
            List.getElem?_append_left rightInput] using agree q hq
        · have leftPast : a.length ≤ q := by omega
          have rightPast : b.length ≤ q := by omega
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right leftPast,
            List.getElem?_append_right rightPast, hlen]
    have mustRead (a b : Fin (m + n) → Bool) (p : Fin (m + n))
        (agree : ∀ q, q ≠ p → a q = b q)
        (diff : C.eval (List.ofFn a) ≠ C.eval (List.ofFn b)) :
        p.val ∈ references := by
      by_contra hAbsent
      apply diff
      have noOut : C.output ≠ p.val := by
        intro e
        exact hAbsent (by simp [references, e])
      have noGate (g : Gate) (hg : g ∈ C.gates) : p.val ∉ g.inputs := by
        intro hp
        exact hAbsent (List.mem_cons_of_mem _ (List.mem_flatMap_of_mem hg hp))
      change (C.gates.foldl step (List.ofFn a)).getD C.output false =
        (C.gates.foldl step (List.ofFn b)).getD C.output false
      refine foldAgree p.val C.gates noGate _ _ (by simp) ?_ _ noOut
      intro q hq
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      split
      · rename_i hqLt
        rw [agree ⟨q, hqLt⟩ (fun h => hq (congrArg Fin.val h))]
      · rfl
    have packed (x : Fin m → Bool) (y : Fin n → Bool) :
        List.ofFn (Fin.addCases x y) = List.ofFn x ++ List.ofFn y := by
      rw [List.ofFn_add]
      congr 1
      · congr 1
        funext i
        exact Fin.addCases_left i
      · simp
    let onLeft (i : Fin m) : Fin m → Bool := fun j => decide (j = i)
    let onRight (j : Fin n) : Fin n → Bool := fun i => decide (i = j)
    have pairOn (i : Fin m) (j : Fin n) (h : R i j) :
        C.eval (List.ofFn (onLeft i) ++ List.ofFn (onRight j)) = true := by
      rw [hComputes]
      exact decide_eq_true ⟨i, j, h, by simp [onLeft], by simp [onRight]⟩
    have rowUsed (i : Fin m) (j : Fin n) (h : R i j) : i.val ∈ references := by
      apply mustRead (Fin.addCases (onLeft i) (onRight j))
        (Fin.addCases (fun _ => false) (onRight j)) (Fin.castAdd n i)
      · intro q
        induction q using Fin.addCases with
        | left t =>
          intro ht
          have hne : t ≠ i := fun e => ht (congrArg (Fin.castAdd n) e)
          simp [onLeft, hne]
        | right t =>
          intro _
          simp
      · rw [packed, packed, pairOn i j h, hComputes]
        simp
    have colUsed (i : Fin m) (j : Fin n) (h : R i j) : m + j.val ∈ references := by
      apply mustRead (Fin.addCases (onLeft i) (onRight j))
        (Fin.addCases (onLeft i) (fun _ => false)) (Fin.natAdd m j)
      · intro q
        induction q using Fin.addCases with
        | left t =>
          intro _
          simp
        | right t =>
          intro ht
          have hne : t ≠ j := fun e => ht (congrArg (Fin.natAdd m) e)
          simp [onRight, hne]
      · rw [packed, packed, pairOn i j h, hComputes]
        simp
    let A := Finset.univ.filter fun i => ∃ j, R i j
    let B := Finset.univ.filter fun j => ∃ i, R i j
    let left : Fin m ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
    let right : Fin n ↪ ℕ := ⟨fun j => m + j.val, by
      intro a b h
      change m + a.val = m + b.val at h
      exact Fin.val_injective (Nat.add_left_cancel h)⟩
    have noOverlap : Disjoint (A.map left) (B.map right) := by
      refine Finset.disjoint_left.mpr ?_
      intro w hwA hwB
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hwA
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hwB
      change i.val = w at hi
      change m + j.val = w at hj
      have := i.isLt
      omega
    have contained : A.map left ∪ B.map right ⊆ references.toFinset := by
      intro u hu
      apply List.mem_toFinset.mpr
      rcases Finset.mem_union.mp hu with ha | hb
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
        obtain ⟨j, h⟩ := (Finset.mem_filter.mp hi).2
        exact rowUsed i j h
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
        obtain ⟨i, h⟩ := (Finset.mem_filter.mp hj).2
        exact colUsed i j h
    calc
      A.card + B.card = (A.map left ∪ B.map right).card := by
        rw [Finset.card_union_of_disjoint noOverlap, Finset.card_map, Finset.card_map]
      _ ≤ references.toFinset.card := Finset.card_le_card contained
      _ ≤ references.length := List.toFinset_card_le references
      _ ≤ 2 * (C.size + 1) := refsLength
  obtain ⟨k, c, _, hDense⟩ := dense
  refine ⟨2 * c + 2 * (k - 1), ?_⟩
  intro m n R _ _ _ hNoSquare C hMonotone hComputes
  obtain ⟨A, B, hRows, hCols, hPeel⟩ := peel k m n R
  obtain ⟨D, hDMonotone, hDSize, hDComputes⟩ := restrict m n R C hMonotone hComputes A B
  let S := fun (i : Fin m) (j : Fin n) => i ∈ A ∧ j ∈ B ∧ R i j
  let _ : DecidableRel S := fun i j => inferInstanceAs (Decidable (i ∈ A ∧ j ∈ B ∧ R i j))
  have hSNoSquare (i i' : Fin m) (j j' : Fin n) :
      S i j → S i' j → S i j' → S i' j' → i = i' ∨ j = j' := by
    intro h₁ h₂ h₃ h₄
    exact hNoSquare i i' j j' h₁.2.2 h₂.2.2 h₃.2.2 h₄.2.2
  have hSBound := hDense m n S hRows hCols hSNoSquare D hDMonotone hDComputes
  have hSupport := support m n R C hMonotone hComputes
  have hSize : D.size + 1 ≤ 2 * (C.size + 1) := by omega
  calc
    (∑ i, (Finset.univ.filter (R i)).card) ≤
        (∑ i, (Finset.univ.filter (S i)).card) +
          (k - 1) * ((Finset.univ.filter fun i => ∃ j, R i j).card +
            (Finset.univ.filter fun j => ∃ i, R i j).card) := hPeel
    _ ≤ c * (2 * (C.size + 1)) + (k - 1) * (2 * (C.size + 1)) :=
      Nat.add_le_add (hSBound.trans (Nat.mul_le_mul_left c hSize))
        (Nat.mul_le_mul_left (k - 1) hSupport)
    _ = (2 * c + 2 * (k - 1)) * (C.size + 1) := by ring
