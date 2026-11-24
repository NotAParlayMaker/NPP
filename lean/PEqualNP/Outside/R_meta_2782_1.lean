import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
  PEqualNP.TopForm

-- Separate the semantic upgrade from the large-order circuit lower bound.
theorem PEqualNP.Outside.R_meta_2782_1
    (hSem :
      ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
        IsAO2 (N + N) C → RightOnIncidentPairs S C →
        (∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y →
          C.eval (incidenceInput X Y) = false) →
        ComputesIncidence S C)
    (hLin :
      ∀ (n : ℕ) (C : Circuit), Monotone2 C →
        (∀ k : Fin n, ∃ x y : Fin n → Bool,
          (∀ j : Fin n, j ≠ k → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) →
        n ≤ C.size + 1)
    (hCore :
      ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit) (X : Finset ℕ),
        100 < q → N = q ^ 2 + q + 1 →
        (∀ l : Fin N, (S l).card = q + 1) →
        (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) →
        IsAO2 (N + N) C → C.output < N + N + C.size → ComputesIncidence S C →
        (∀ j < C.size, j ∉ X → (NestedCover.gateAt C j).op = GateOp.and →
          ∃ f g : Finset (Fin N) → Bool, ∀ X' Y' : Finset (Fin N),
            wireValue C (incidenceInput X' Y') (N + N + j) = (f X' && g Y')) →
        100 * X.card < N * q → N * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → (∀ x14 < x4.size, x14 ∉ x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x18 : Finset (Fin x2) → Bool) (x19 : Finset (Fin x2) → Bool), ∀ (x20 x21 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x20 x21) (x2 + x2 + x14) = (x18 x20 && x19 x21)) → (100 : ℕ) * x5.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 x5 hq hN hcard huniq hAO hout hright hfalse hfactor hbudget
  have hcomp : ComputesIncidence x3 x4 := hSem x1 x2 x3 x4 hAO hright hfalse
  have hmon : Monotone2 x4 := by
    intro g hg
    exact ⟨hAO.1 g hg, by rw [hAO.2.2 g hg]⟩
  have heval : ∀ X Y : Finset (Fin x2),
      circuitFun (x2 + x2) x4 (Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))) =
        incidenceFun x3 X Y := by
    intro X Y
    unfold circuitFun
    have heq : List.ofFn (Fin.append (fun p : Fin x2 => decide (p ∈ X))
        (fun l : Fin x2 => decide (l ∈ Y))) = incidenceInput X Y := by
      change List.ofFn (Fin.append (fun p : Fin x2 => decide (p ∈ X))
        (fun l : Fin x2 => decide (l ∈ Y))) =
        List.ofFn (fun p : Fin x2 => decide (p ∈ X)) ++
          List.ofFn (fun l : Fin x2 => decide (l ∈ Y))
      rw [List.ofFn_add]
      congr 1
      · apply congrArg List.ofFn
        funext i
        rw [show Fin.castLE (Nat.le_add_right x2 x2) i = Fin.castAdd x2 i from Fin.ext rfl]
        exact Fin.append_left _ _ i
      · apply congrArg List.ofFn
        funext i
        exact Fin.append_right _ _ i
    rw [heq]
    exact hcomp X Y
  by_cases hq0 : x1 = 0
  · subst x1
    norm_num at hN
    subst x2
    simp
  · have hq1 : 1 ≤ x1 := by omega
    have hN2 : 2 ≤ x2 := by rw [hN]; nlinarith
    have hsens : ∀ k : Fin (x2 + x2), ∃ x y : Fin (x2 + x2) → Bool,
        (∀ j : Fin (x2 + x2), j ≠ k → x j = y j) ∧
          circuitFun (x2 + x2) x4 x ≠ circuitFun (x2 + x2) x4 y := by
      intro k
      by_cases hk : k.val < x2
      · let p : Fin x2 := ⟨k.val, hk⟩
        have hkp : k = Fin.castAdd x2 p := Fin.ext rfl
        let p' : Fin x2 := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
        have hne : p ≠ p' := by
          intro h
          have hv := congrArg Fin.val h
          by_cases hp0 : p.val = 0 <;> simp [p', hp0] at hv
        obtain ⟨l, ⟨hIpl, _⟩, _⟩ := huniq p p' hne
        let x : Fin (x2 + x2) → Bool :=
          Fin.append (fun _ => false) (fun b => decide (b = l))
        let y : Fin (x2 + x2) → Bool :=
          Fin.append (fun a => decide (a = p)) (fun b => decide (b = l))
        refine ⟨x, y, ?_, ?_⟩
        · intro j hj
          rw [hkp] at hj
          cases j using Fin.addCases with
          | left a =>
            have ha : a ≠ p := by
              intro h
              apply hj
              rw [h]
            simp only [x, y, Fin.append_left]
            simp [ha]
          | right b => simp only [x, y, Fin.append_right]
        · have hy : circuitFun (x2 + x2) x4 y = true := by
            calc
              _ = incidenceFun x3 {p} {l} := by
                change circuitFun (x2 + x2) x4
                  (Fin.append (fun a => decide (a = p)) (fun b => decide (b = l))) = _
                simpa only [Finset.mem_singleton] using heval ({p} : Finset (Fin x2)) {l}
              _ = true := by
                change decide (∃ p' ∈ ({p} : Finset (Fin x2)),
                  ∃ l' ∈ ({l} : Finset (Fin x2)), p' ∈ x3 l') = true
                simp [hIpl]
          have hx : circuitFun (x2 + x2) x4 x = false := by
            calc
              _ = incidenceFun x3 ∅ {l} := by
                change circuitFun (x2 + x2) x4
                  (Fin.append (fun _ => false) (fun b => decide (b = l))) = _
                simpa using heval (∅ : Finset (Fin x2)) {l}
              _ = false := by
                change decide (∃ p' ∈ (∅ : Finset (Fin x2)),
                  ∃ l' ∈ ({l} : Finset (Fin x2)), p' ∈ x3 l') = false
                simp
          rw [hx, hy]
          decide
      · let l : Fin x2 := ⟨k.val - x2, by omega⟩
        have hkl : k = Fin.natAdd x2 l := Fin.ext (by simp [l]; omega)
        have hnon : (x3 l).Nonempty := Finset.card_pos.mp (by rw [hcard l]; omega)
        obtain ⟨p, hIpl⟩ := hnon
        let x : Fin (x2 + x2) → Bool :=
          Fin.append (fun a => decide (a = p)) (fun _ => false)
        let y : Fin (x2 + x2) → Bool :=
          Fin.append (fun a => decide (a = p)) (fun b => decide (b = l))
        refine ⟨x, y, ?_, ?_⟩
        · intro j hj
          rw [hkl] at hj
          cases j using Fin.addCases with
          | left a => simp [x, y]
          | right b =>
            have hb : b ≠ l := by
              intro h
              apply hj
              rw [h]
            simp only [x, y, Fin.append_right]
            simp [hb]
        · have hy : circuitFun (x2 + x2) x4 y = true := by
            calc
              _ = incidenceFun x3 {p} {l} := by
                change circuitFun (x2 + x2) x4
                  (Fin.append (fun a => decide (a = p)) (fun b => decide (b = l))) = _
                simpa only [Finset.mem_singleton] using heval ({p} : Finset (Fin x2)) {l}
              _ = true := by
                change decide (∃ p' ∈ ({p} : Finset (Fin x2)),
                  ∃ l' ∈ ({l} : Finset (Fin x2)), p' ∈ x3 l') = true
                simp [hIpl]
          have hx : circuitFun (x2 + x2) x4 x = false := by
            calc
              _ = incidenceFun x3 {p} ∅ := by
                change circuitFun (x2 + x2) x4
                  (Fin.append (fun a => decide (a = p)) (fun _ => false)) = _
                simpa using heval {p} (∅ : Finset (Fin x2))
              _ = false := by
                change decide (∃ p' ∈ ({p} : Finset (Fin x2)),
                  ∃ l' ∈ (∅ : Finset (Fin x2)), p' ∈ x3 l') = false
                simp
          rw [hx, hy]
          decide
    have hNsize : x2 ≤ x4.size := by
      have h2N := hLin (x2 + x2) x4 hmon hsens
      omega
    by_cases hq100 : x1 ≤ 100
    · calc x2 * x1 ≤ x2 * 100 := Nat.mul_le_mul_left x2 hq100
        _ = 100 * x2 := Nat.mul_comm x2 100
        _ ≤ 100 * x4.size := Nat.mul_le_mul_left 100 hNsize
    · have hqgt : 100 < x1 := by omega
      exact hCore x1 x2 x3 x4 x5 hqgt hN hcard huniq hAO hout hcomp hfactor hbudget
