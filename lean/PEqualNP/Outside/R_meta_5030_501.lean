import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5030_501
    (single : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ),
      let v (x : Fin (N + N) → Bool) (w : ℕ) := wireValue C (List.ofFn x) w
      let neg (Y : Finset (Fin N)) := Fin.addCases
        (fun p => decide (∀ l ∈ Y, ¬ I p l)) (fun l => decide (l ∈ Y))
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ w ∈ F, N + N ≤ w ∧ w < N + N + C.size ∧ (gateAt C (w - (N + N))).op = .and) →
      (∀ l : Fin N, ∀ w ∈ F, v (neg {l}) w = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        ∃ w ∈ F, PEqualNP.ReadK.lineSingle { gates := C.gates, output := w } (N + N)
          (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true} ≤ 6 * C.size)
    (residual : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ),
      let v (x : Fin (N + N) → Bool) (w : ℕ) := wireValue C (List.ofFn x) w
      let pair (p l : Fin N) (i : Fin (N + N)) :=
        decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
      let neg (Y : Finset (Fin N)) := Fin.addCases
        (fun p => decide (∀ l ∈ Y, ¬ I p l)) (fun l => decide (l ∈ Y))
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ (i : ℕ) (g : Gate), C.gates[i]? = some g →
        ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i) →
      (∀ w ∈ F, N + N ≤ w ∧ w < N + N + C.size ∧
        (gateAt C (w - (N + N))).op = .and ∧ ∃ p l, I p l ∧ v (pair p l) w = true) →
      (∀ p l, I p l → ∃ w ∈ F, v (pair p l) w = true) →
      (∀ (Y : Finset (Fin N)), Y.card ≤ q → ∀ w ∈ F, v (neg Y) w = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        ¬ ∃ w ∈ F, PEqualNP.ReadK.lineSingle { gates := C.gates, output := w } (N + N)
          (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true} ≤ 94 * (C.size + 1)) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset ℕ),   have x7 : (Fin (x2 + x2) → Bool) → ℕ → Bool := fun (x7 : Fin (x2 + x2) → Bool) (x8 : ℕ) => PEqualNP.CircuitLowerBounds.wireValue x5 (List.ofFn x7) x8;   have x8 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x8 x9 : Fin x2) (x10 : Fin (x2 + x2)) => Decidable.decide (x10 = Fin.castAdd x2 x8 ∨ x10 = Fin.natAdd x2 x9);   have x9 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x9 : Finset (Fin x2)) (x10 : Fin (x2 + x2)) => Fin.addCases (fun (x11 : Fin x2) => Decidable.decide (∀ x12 ∈ x9, ¬x3 x11 x12)) (fun (x11 : Fin x2) => Decidable.decide (x11 ∈ x9)) x10;   (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x12 : Fin x2), Fintype.card { x13 : Fin x2 // x3 x13 x12 } = x1 + (1 : ℕ)) → (∀ (x13 x14 : Fin x2), x13 ≠ x14 → ∃! x16 : Fin x2, x3 x13 x16 ∧ x3 x14 x16) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 → ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) → (∀ x16 ∈ x6, x2 + x2 ≤ x16 ∧ x16 < x2 + x2 + x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x16 - (x2 + x2))).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x7 (x8 x18 x19) x16 = Bool.true) → (∀ (x17 x18 : Fin x2), x3 x17 x18 → ∃ x20 ∈ x6, x7 (x8 x17 x18) x20 = Bool.true) → (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∀ x20 ∈ x6, x7 (x9 x18) x20 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * (x5.size + (1 : ℕ)) := by
  classical
  intro q N I _ C F v pair neg hq hN cols unique mono norm front cover sound
  have model : PEqualNP.TopForm.IsAO2 (N + N) C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (mono g hg).1
    · intro j hj i hij
      have get : C.gates[j]? = some C.gates[j] := by simp [hj]
      obtain ⟨a,b,hab,ha,hb⟩ := norm j _ get
      have gate : gateAt C j = C.gates[j] := by simp [gateAt, hj]
      rw [gate, hab] at hij
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hij
      rcases hij with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      obtain ⟨a,b,hab,_,_⟩ := norm j C.gates[j] (by simp [hj])
      simp [hab]
  have hF (w : ℕ) (hw : w ∈ F) :
      N + N ≤ w ∧ w < N + N + C.size ∧ (gateAt C (w - (N + N))).op = .and := by
    obtain ⟨h1, h2, h3, _⟩ := front w hw
    exact ⟨h1, h2, h3⟩
  have oneLine (l : Fin N) (w : ℕ) (hw : w ∈ F) : v (neg {l}) w = false :=
    sound {l} (by simp; omega) w hw
  have small := single N I C F unique model hF oneLine
  have rest := residual q N I C F hq hN cols unique model norm front cover sound
  have partition :
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        ∃ w ∈ F, PEqualNP.ReadK.lineSingle { gates := C.gates, output := w } (N + N)
          (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true} +
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        ¬ ∃ w ∈ F, PEqualNP.ReadK.lineSingle { gates := C.gates, output := w } (N + N)
          (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true} =
      Fintype.card {e : Fin N × Fin N // I e.1 e.2} := by
    simp only [Fintype.card_subtype]
    simpa only [Finset.filter_filter] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2))
        (fun e => ∃ w ∈ F, PEqualNP.ReadK.lineSingle { gates := C.gates, output := w } (N + N)
          (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true))
  let e : {pl : Fin N × Fin N // I pl.1 pl.2} ≃ (Σ l : Fin N, {p : Fin N // I p l}) :=
    { toFun := fun x => ⟨x.val.2,⟨x.val.1,x.property⟩⟩
      invFun := fun x => ⟨(x.2.val,x.1),x.2.property⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }
  have total : Fintype.card {e : Fin N × Fin N // I e.1 e.2} = N * (q + 1) := by
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [cols, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [total] at partition
  have : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega
