import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8164

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ev {n : ℕ} : DMFormula n → (Fin n → Bool) → Bool
  | .lit i _, x => x i
  | .and φ ψ, x => ev φ x && ev ψ x
  | .or φ ψ, x => ev φ x || ev ψ x

theorem evrec {n : ℕ} (φ : DMFormula n) : ∀ y : Fin n → Bool, (DMFormula.rec (motive := fun _ => Bool) (fun (x4 : Fin n) (_ : Bool) => y x4) (fun (_ _ : DMFormula n) (x6 x7 : Bool) => x6 && x7) (fun (_ _ : DMFormula n) (x6 x7 : Bool) => x6 || x7) φ) = ev φ y := by
  intro y
  induction φ with
  | lit i b => rfl
  | and φ ψ h1 h2 => simp only [ev, ← h1, ← h2]
  | or φ ψ h1 h2 => simp only [ev, ← h1, ← h2]

theorem kw {n : ℕ} (φ : DMFormula n) : ∃ (P Q : Fin φ.leaves → (Fin n → Bool) → Prop) (v : Fin φ.leaves → Fin n), ∀ y z, ev φ y = true → ev φ z = false →
    (∃! l, P l y ∧ Q l z) ∧ ∀ l, P l y → Q l z → y (v l) = true ∧ z (v l) = false := by
  induction φ with
  | lit i b =>
    refine ⟨fun _ _ => True, fun _ _ => True, fun _ => i, fun y z hy hz => ⟨⟨(⟨0, by simp [DMFormula.leaves]⟩ : Fin (DMFormula.lit i b).leaves), ⟨trivial, trivial⟩, ?_⟩, fun _ _ _ => ⟨hy, hz⟩⟩⟩
    intro l _
    apply Fin.ext
    have := l.isLt
    simp only [DMFormula.leaves] at this
    simp only
    omega
  | and φ ψ h1 h2 =>
    obtain ⟨P1, Q1, v1, h1⟩ := h1
    obtain ⟨P2, Q2, v2, h2⟩ := h2
    refine ⟨Fin.append (m := φ.leaves) (n := ψ.leaves) P1 P2, Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l z => ev φ z = false ∧ Q1 l z) (fun l z => ev φ z = true ∧ Q2 l z), Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2, ?_⟩
    intro y z hy hz
    simp only [ev, Bool.and_eq_true] at hy
    have hz' : (ev φ z && ev ψ z) = false := hz
    cases hf : ev φ z
    · obtain ⟨⟨l0, hl0, hu⟩, h3⟩ := h1 y z hy.1 hf
      refine ⟨⟨Fin.castAdd ψ.leaves l0, ?_, ?_⟩, ?_⟩
      · simp only [Fin.append_left]
        exact ⟨hl0.1, hf, hl0.2⟩
      · intro l
        refine Fin.addCases (m := φ.leaves) (n := ψ.leaves) (motive := fun l => Fin.append (m := φ.leaves) (n := ψ.leaves) P1 P2 l y ∧ Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l z => ev φ z = false ∧ Q1 l z) (fun l z => ev φ z = true ∧ Q2 l z) l z → l = Fin.castAdd ψ.leaves l0) (fun l => ?_) (fun l => ?_) l
        · simp only [Fin.append_left]
          rintro ⟨q1, _, q2⟩
          rw [hu l ⟨q1, q2⟩]
        · simp only [Fin.append_right]
          rintro ⟨_, q1, _⟩
          rw [hf] at q1; cases q1
      · intro l
        refine Fin.addCases (m := φ.leaves) (n := ψ.leaves) (motive := fun l => Fin.append (m := φ.leaves) (n := ψ.leaves) P1 P2 l y → Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l z => ev φ z = false ∧ Q1 l z) (fun l z => ev φ z = true ∧ Q2 l z) l z → y (Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2 l) = true ∧ z (Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2 l) = false) (fun l => ?_) (fun l => ?_) l
        · simp only [Fin.append_left]
          rintro q1 ⟨_, q2⟩
          exact h3 l q1 q2
        · simp only [Fin.append_right]
          rintro _ ⟨q1, _⟩
          rw [hf] at q1; cases q1
    · have hg : ev ψ z = false := by rw [hf] at hz'; simpa using hz'
      obtain ⟨⟨l0, hl0, hu⟩, h3⟩ := h2 y z hy.2 hg
      refine ⟨⟨Fin.natAdd φ.leaves l0, ?_, ?_⟩, ?_⟩
      · simp only [Fin.append_right]
        exact ⟨hl0.1, hf, hl0.2⟩
      · intro l
        refine Fin.addCases (m := φ.leaves) (n := ψ.leaves) (motive := fun l => Fin.append (m := φ.leaves) (n := ψ.leaves) P1 P2 l y ∧ Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l z => ev φ z = false ∧ Q1 l z) (fun l z => ev φ z = true ∧ Q2 l z) l z → l = Fin.natAdd φ.leaves l0) (fun l => ?_) (fun l => ?_) l
        · simp only [Fin.append_left]
          rintro ⟨_, q1, _⟩
          rw [hf] at q1; cases q1
        · simp only [Fin.append_right]
          rintro ⟨q1, _, q2⟩
          rw [hu l ⟨q1, q2⟩]
      · intro l
        refine Fin.addCases (m := φ.leaves) (n := ψ.leaves) (motive := fun l => Fin.append (m := φ.leaves) (n := ψ.leaves) P1 P2 l y → Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l z => ev φ z = false ∧ Q1 l z) (fun l z => ev φ z = true ∧ Q2 l z) l z → y (Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2 l) = true ∧ z (Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2 l) = false) (fun l => ?_) (fun l => ?_) l
        · simp only [Fin.append_left]
          rintro _ ⟨q1, _⟩
          rw [hf] at q1; cases q1
        · simp only [Fin.append_right]
          rintro q1 ⟨_, q2⟩
          exact h3 l q1 q2
  | or φ ψ h1 h2 =>
    obtain ⟨P1, Q1, v1, h1⟩ := h1
    obtain ⟨P2, Q2, v2, h2⟩ := h2
    refine ⟨Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l y => ev φ y = true ∧ P1 l y) (fun l y => ev φ y = false ∧ P2 l y), Fin.append (m := φ.leaves) (n := ψ.leaves) Q1 Q2, Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2, ?_⟩
    intro y z hy hz
    simp only [ev, Bool.or_eq_false_iff] at hz
    have hy' : (ev φ y || ev ψ y) = true := hy
    cases hf : ev φ y
    · have hg : ev ψ y = true := by rw [hf] at hy'; simpa using hy'
      obtain ⟨⟨l0, hl0, hu⟩, h3⟩ := h2 y z hg hz.2
      refine ⟨⟨Fin.natAdd φ.leaves l0, ?_, ?_⟩, ?_⟩
      · simp only [Fin.append_right]
        exact ⟨⟨hf, hl0.1⟩, hl0.2⟩
      · intro l
        refine Fin.addCases (m := φ.leaves) (n := ψ.leaves) (motive := fun l => Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l y => ev φ y = true ∧ P1 l y) (fun l y => ev φ y = false ∧ P2 l y) l y ∧ Fin.append (m := φ.leaves) (n := ψ.leaves) Q1 Q2 l z → l = Fin.natAdd φ.leaves l0) (fun l => ?_) (fun l => ?_) l
        · simp only [Fin.append_left]
          rintro ⟨⟨q1, _⟩, _⟩
          rw [hf] at q1; cases q1
        · simp only [Fin.append_right]
          rintro ⟨⟨_, q1⟩, q2⟩
          rw [hu l ⟨q1, q2⟩]
      · intro l
        refine Fin.addCases (m := φ.leaves) (n := ψ.leaves) (motive := fun l => Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l y => ev φ y = true ∧ P1 l y) (fun l y => ev φ y = false ∧ P2 l y) l y → Fin.append (m := φ.leaves) (n := ψ.leaves) Q1 Q2 l z → y (Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2 l) = true ∧ z (Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2 l) = false) (fun l => ?_) (fun l => ?_) l
        · simp only [Fin.append_left]
          rintro ⟨q1, _⟩ _
          rw [hf] at q1; cases q1
        · simp only [Fin.append_right]
          rintro ⟨_, q1⟩ q2
          exact h3 l q1 q2
    · obtain ⟨⟨l0, hl0, hu⟩, h3⟩ := h1 y z hf hz.1
      refine ⟨⟨Fin.castAdd ψ.leaves l0, ?_, ?_⟩, ?_⟩
      · simp only [Fin.append_left]
        exact ⟨⟨hf, hl0.1⟩, hl0.2⟩
      · intro l
        refine Fin.addCases (m := φ.leaves) (n := ψ.leaves) (motive := fun l => Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l y => ev φ y = true ∧ P1 l y) (fun l y => ev φ y = false ∧ P2 l y) l y ∧ Fin.append (m := φ.leaves) (n := ψ.leaves) Q1 Q2 l z → l = Fin.castAdd ψ.leaves l0) (fun l => ?_) (fun l => ?_) l
        · simp only [Fin.append_left]
          rintro ⟨⟨_, q1⟩, q2⟩
          rw [hu l ⟨q1, q2⟩]
        · simp only [Fin.append_right]
          rintro ⟨⟨q1, _⟩, _⟩
          rw [hf] at q1; cases q1
      · intro l
        refine Fin.addCases (m := φ.leaves) (n := ψ.leaves) (motive := fun l => Fin.append (m := φ.leaves) (n := ψ.leaves) (fun l y => ev φ y = true ∧ P1 l y) (fun l y => ev φ y = false ∧ P2 l y) l y → Fin.append (m := φ.leaves) (n := ψ.leaves) Q1 Q2 l z → y (Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2 l) = true ∧ z (Fin.append (m := φ.leaves) (n := ψ.leaves) v1 v2 l) = false) (fun l => ?_) (fun l => ?_) l
        · simp only [Fin.append_left]
          rintro ⟨_, q1⟩ q2
          exact h3 l q1 q2
        · simp only [Fin.append_right]
          rintro ⟨q1, _⟩ _
          rw [hf] at q1; cases q1

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8164

theorem PEqualNP.Outside.L_meta_8164 : ∀ (x1 : ℕ) (x2 : PEqualNP.MetaComplexity.DMFormula x1),   have x3 : (Fin x1 → Bool) → Bool := fun (x3 : Fin x1 → Bool) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x4 : Fin x1) (x5 : Bool) => x3 x4) (fun (x4 x5 : PEqualNP.MetaComplexity.DMFormula x1) (x6 x7 : Bool) => x6 && x7) (fun (x4 x5 : PEqualNP.MetaComplexity.DMFormula x1) (x6 x7 : Bool) => x6 || x7) x2;   ∃ (x4 : Fin x2.leaves → (Fin x1 → Bool) → Prop) (x5 : Fin x2.leaves → (Fin x1 → Bool) → Prop) (x6 : Fin x2.leaves → Fin x1), ∀ (x7 x8 : Fin x1 → Bool), x3 x7 = Bool.true → x3 x8 = Bool.false → (∃! x11 : Fin x2.leaves, x4 x11 x7 ∧ x5 x11 x8) ∧ ∀ (x11 : Fin x2.leaves), x4 x11 x7 → x5 x11 x8 → x7 (x6 x11) = Bool.true ∧ x8 (x6 x11) = Bool.false := by
  intro n φ ev
  obtain ⟨P, Q, v, h⟩ := PEqualNP.Outside.L_meta_8164.kw φ
  have he : ∀ y, ev y = PEqualNP.Outside.L_meta_8164.ev φ y := PEqualNP.Outside.L_meta_8164.evrec φ
  refine ⟨P, Q, v, fun y z hy hz => h y z ?_ ?_⟩
  · rw [← he]; exact hy
  · rw [← he]; exact hz
