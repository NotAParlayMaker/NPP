import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.HeptadCover

-- Freeze the first conjunction to false. If it had a reader, the first reader
-- also disappears by constant propagation. Otherwise deleting the unused gate
-- saves one gate and preserves every test. On a minimal positive pair, freezing
-- two distinct primary inputs' conjunction can lose at most that one pair.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2346_52
    (hfreeze : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → 2 ≤ C.size →
      (gateAt C 0).op = GateOp.and → opnd C 0 0 ≠ opnd C 0 1 →
      ∃ (a b : Fin n) (D : Circuit), a ≠ b ∧ IsAO2 n D ∧ D.size < C.size ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true) ∧
        (∀ x : Fin n → Bool, (x a = false ∨ x b = false) → D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
        (D.size + 2 ≤ C.size ∨ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)))
    (hprofile : ∀ (D : Circuit), IsAO2 14 D → D.size ≤ 26 →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true → ∃ p l : Fin 7, p ∈ fanoLines l ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      ((incidences fanoLines).filter fun pl => D.eval (List.ofFn
        (pairInput (Fin.castAdd 7 pl.1) (Fin.natAdd 7 pl.2))) = true).card + 6 ≤ max 25 D.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  intro C hsize hAO hdistinct hand hF _
  let E := incidences fanoLines
  let row (pl : Fin 7 × Fin 7) := pairInput (Fin.castAdd 7 pl.1) (Fin.natAdd 7 pl.2)
  have hE : E.card = 21 := by decide
  have hline : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l + 1 ∨ p = l + 3 := by decide
  have sound : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true → ∃ p l : Fin 7, p ∈ fanoLines l ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    intro x hx
    obtain ⟨p,l,h,i,j⟩ := (hF x).mp hx
    exact ⟨p,l,(hline p l).mpr h,i,j⟩
  have full : ∀ pl ∈ E, C.eval (List.ofFn (row pl)) = true := by
    intro pl h
    have hm : pl.1 ∈ fanoLines pl.2 := (Finset.mem_filter.mp h).2
    apply (hF _).mpr
    refine ⟨pl.1,pl.2,(hline _ _).mp hm, ?_, ?_⟩
    · exact decide_eq_true (Or.inl rfl)
    · exact decide_eq_true (Or.inr rfl)
  have small : 2 ≤ C.size := by
    by_contra! h
    have hh := hprofile C hAO (by omega) sound
    change (E.filter fun pl => C.eval (List.ofFn (row pl)) = true).card + 6 ≤ _ at hh
    rw [Finset.filter_true_of_mem full, hE] at hh
    omega
  obtain ⟨a,b,D,hab,hao,hs,hle,hfix,hcost⟩ := hfreeze 14 C hAO small hand (hdistinct 0 (by omega))
  have hh := hprofile D hao (by omega) (fun x hx => sound x (hle x hx))
  let A := E.filter fun pl => D.eval (List.ofFn (row pl)) = true
  change A.card + 6 ≤ max 25 D.size at hh
  rcases hcost with hcost | hexact
  · let keep := E.filter fun pl => row pl a = false ∨ row pl b = false
    have hsub : keep ⊆ A := by
      intro pl h
      obtain ⟨hp,hzero⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨hp, (hfix _ hzero).trans (full pl hp)⟩
    have hc : 20 ≤ keep.card := by
      have table : ∀ i j : Fin 14, i ≠ j → 20 ≤ (E.filter fun pl => row pl i = false ∨ row pl j = false).card := by decide
      exact table a b hab
    have := Finset.card_le_card hsub
    omega
  · have hall : E ⊆ A := by
      intro pl hp
      exact Finset.mem_filter.mpr ⟨hp, (hexact _).trans (full pl hp)⟩
    have := Finset.card_le_card hall
    omega
