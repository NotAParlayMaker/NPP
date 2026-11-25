import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5284_1
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∃ D : Circuit, Monotone2 D ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧
        D.size ≤ C.size ∧
        ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g → g.op = GateOp.and →
          ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
            ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (decode : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : Circuit),
      (∀ (j : ℕ) (g : Gate), D.gates[j]? = some g → g.op = GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g → g.op = GateOp.and →
        ∀ S : Finset (Fin n), S.card ≤ 2 →
          (D.wires (List.ofFn (fun i => decide (i ∈ S)))).getD (n + j) false = true →
          ∃ u ∈ S, ∃ v ∈ S, G.Adj u v) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x1 → Bool), x9.eval (List.ofFn x11) = x4 x11) → x6 x9 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size ≤ x9.size ∧ (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x13.eval (List.ofFn (x5 {x14, x15})) = Bool.true) ∧ (∀ (x14 : Fin x1), x13.eval (List.ofFn (x5 {x14})) = Bool.false) ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x13.gates[x14]? = Option.some x15 → x15.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x18 : Finset (Fin x1)), x18.card ≤ (2 : ℕ) → (x13.wires (List.ofFn (x5 x18))).getD (x1 + x14) Bool.false = Bool.true → ∃ x21 ∈ x18, ∃ x22 ∈ x18, x2.Adj x21 x22 := by
  classical
  dsimp only
  intro n G _ _ hFour C hMono hComp _
  by_cases hE : ∃ u v : Fin n, G.Adj u v
  · have hC4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a := by
      intro a b c d _ hac _ _ hbd _ hab hbc hcd da
      exact (hFour a b c d hab hbc hcd da).elim hac hbd
    have hCompI : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
      intro x
      rw [hComp x]
      simp
    obtain ⟨D, hMD, hCompD, hSize, hSound⟩ := normalize n G C hE hC4 hMono hCompI
    refine ⟨D, hMD, hSize, ?_, ?_, ?_⟩
    · intro u v huv
      apply (hCompD _).2
      exact ⟨u, v, huv, by simp, by simp⟩
    · intro u
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨a, b, hab, ha, hb⟩ := (hCompD _).1 htrue
      have hae : a = u := by simpa using ha
      have hbe : b = u := by simpa using hb
      subst a
      subst b
      exact G.loopless.irrefl _ hab
    · exact decode n G D hSound
  · refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · simp [Circuit.size]
    · intro u v huv
      exact (hE ⟨u, v, huv⟩).elim
    · intro u
      simp [Circuit.eval, Circuit.wires]
    · intro j g hj
      simp at hj
