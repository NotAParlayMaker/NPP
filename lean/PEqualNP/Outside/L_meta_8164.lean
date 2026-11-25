import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8164_aux

open PEqualNP.MetaComplexity

noncomputable def mev {n : ℕ} (φ : DMFormula n) (x : Fin n → Bool) : Bool :=
  DMFormula.rec (fun (i : Fin n) (_ : Bool) => x i) (fun _ _ (a b : Bool) => a && b)
    (fun _ _ (a b : Bool) => a || b) φ

noncomputable def AA {n : ℕ} : (φ : DMFormula n) → Fin φ.leaves → (Fin n → Bool) → Prop
  | DMFormula.lit _ _ => fun _ _ => True
  | DMFormula.and φ ψ => fun k x =>
      Fin.addCases (motive := fun _ => Prop) (fun i => AA φ i x) (fun j => AA ψ j x) k
  | DMFormula.or φ ψ => fun k x =>
      Fin.addCases (motive := fun _ => Prop) (fun i => mev φ x = true ∧ AA φ i x)
        (fun j => mev φ x = false ∧ AA ψ j x) k

noncomputable def BB {n : ℕ} : (φ : DMFormula n) → Fin φ.leaves → (Fin n → Bool) → Prop
  | DMFormula.lit _ _ => fun _ _ => True
  | DMFormula.and φ ψ => fun k y =>
      Fin.addCases (motive := fun _ => Prop) (fun i => mev φ y = false ∧ BB φ i y)
        (fun j => mev φ y = true ∧ BB ψ j y) k
  | DMFormula.or φ ψ => fun k y =>
      Fin.addCases (motive := fun _ => Prop) (fun i => BB φ i y) (fun j => BB ψ j y) k

def VV {n : ℕ} : (φ : DMFormula n) → Fin φ.leaves → Fin n
  | DMFormula.lit i _ => fun _ => i
  | DMFormula.and φ ψ => fun k => Fin.addCases (motive := fun _ => Fin n) (VV φ) (VV ψ) k
  | DMFormula.or φ ψ => fun k => Fin.addCases (motive := fun _ => Fin n) (VV φ) (VV ψ) k

theorem main {n : ℕ} (φ : DMFormula n) : ∀ x y : Fin n → Bool, mev φ x = true → mev φ y = false →
    (∃ k, AA φ k x ∧ BB φ k y) ∧ (∀ k k', AA φ k x → BB φ k y → AA φ k' x → BB φ k' y → k = k') ∧
    ∀ k, AA φ k x → BB φ k y → x (VV φ k) = true ∧ y (VV φ k) = false := by
  induction φ with
  | lit i b =>
    intro x y hx hy
    refine ⟨⟨⟨0, by simp [DMFormula.leaves]⟩, trivial, trivial⟩, ?_, ?_⟩
    · intro k k' _ _ _ _
      apply Fin.ext
      have h1 := k.2
      have h2 := k'.2
      simp [DMFormula.leaves] at h1 h2
      omega
    · intro k _ _
      exact ⟨hx, hy⟩
  | and φ ψ ihφ ihψ =>
    intro x y hx hy
    have hx' : mev φ x = true ∧ mev ψ x = true := by
      simpa [mev] using hx
    refine ⟨?_, ?_, ?_⟩
    · cases hφy : mev φ y
      · obtain ⟨⟨k, hk1, hk2⟩, _, _⟩ := ihφ x y hx'.1 hφy
        exact ⟨Fin.castAdd _ k, by simp [AA, BB, hk1, hk2, hφy]⟩
      · have hψy : mev ψ y = false := by
          have : (mev φ y && mev ψ y) = false := hy
          simp_all
        obtain ⟨⟨k, hk1, hk2⟩, _, _⟩ := ihψ x y hx'.2 hψy
        exact ⟨Fin.natAdd _ k, by simp [AA, BB, hk1, hk2, hφy]⟩
    · intro k k'
      cases k using Fin.addCases with
      | left i =>
        cases k' using Fin.addCases with
        | left i' =>
          intro a1 b1 a2 b2
          simp only [AA, BB, Fin.addCases_left] at a1 b1 a2 b2
          rw [(ihφ x y hx'.1 b1.1).2.1 i i' a1 b1.2 a2 b2.2]
        | right j' =>
          intro a1 b1 a2 b2
          simp only [AA, BB, Fin.addCases_left, Fin.addCases_right] at a1 b1 a2 b2
          simp_all
      | right j =>
        cases k' using Fin.addCases with
        | left i' =>
          intro a1 b1 a2 b2
          simp only [AA, BB, Fin.addCases_left, Fin.addCases_right] at a1 b1 a2 b2
          simp_all
        | right j' =>
          intro a1 b1 a2 b2
          simp only [AA, BB, Fin.addCases_right] at a1 b1 a2 b2
          have hψy : mev ψ y = false := by
            have : (mev φ y && mev ψ y) = false := hy
            simp_all
          rw [(ihψ x y hx'.2 hψy).2.1 j j' a1 b1.2 a2 b2.2]
    · intro k
      cases k using Fin.addCases with
      | left i =>
        intro a1 b1
        simp only [AA, BB, VV, Fin.addCases_left] at a1 b1 ⊢
        exact (ihφ x y hx'.1 b1.1).2.2 i a1 b1.2
      | right j =>
        intro a1 b1
        simp only [AA, BB, VV, Fin.addCases_right] at a1 b1 ⊢
        have hψy : mev ψ y = false := by
          have : (mev φ y && mev ψ y) = false := hy
          simp_all
        exact (ihψ x y hx'.2 hψy).2.2 j a1 b1.2
  | or φ ψ ihφ ihψ =>
    intro x y hx hy
    have hy' : mev φ y = false ∧ mev ψ y = false := by
      simpa [mev] using hy
    refine ⟨?_, ?_, ?_⟩
    · cases hφx : mev φ x
      · have hψx : mev ψ x = true := by
          have : (mev φ x || mev ψ x) = true := hx
          simp_all
        obtain ⟨⟨k, hk1, hk2⟩, _, _⟩ := ihψ x y hψx hy'.2
        exact ⟨Fin.natAdd _ k, by simp [AA, BB, hk1, hk2, hφx]⟩
      · obtain ⟨⟨k, hk1, hk2⟩, _, _⟩ := ihφ x y hφx hy'.1
        exact ⟨Fin.castAdd _ k, by simp [AA, BB, hk1, hk2, hφx]⟩
    · intro k k'
      cases k using Fin.addCases with
      | left i =>
        cases k' using Fin.addCases with
        | left i' =>
          intro a1 b1 a2 b2
          simp only [AA, BB, Fin.addCases_left] at a1 b1 a2 b2
          rw [(ihφ x y a1.1 hy'.1).2.1 i i' a1.2 b1 a2.2 b2]
        | right j' =>
          intro a1 b1 a2 b2
          simp only [AA, BB, Fin.addCases_left, Fin.addCases_right] at a1 b1 a2 b2
          simp_all
      | right j =>
        cases k' using Fin.addCases with
        | left i' =>
          intro a1 b1 a2 b2
          simp only [AA, BB, Fin.addCases_left, Fin.addCases_right] at a1 b1 a2 b2
          simp_all
        | right j' =>
          intro a1 b1 a2 b2
          simp only [AA, BB, Fin.addCases_right] at a1 b1 a2 b2
          have hψx : mev ψ x = true := by
            have : (mev φ x || mev ψ x) = true := hx
            simp_all
          rw [(ihψ x y hψx hy'.2).2.1 j j' a1.2 b1 a2.2 b2]
    · intro k
      cases k using Fin.addCases with
      | left i =>
        intro a1 b1
        simp only [AA, BB, VV, Fin.addCases_left] at a1 b1 ⊢
        exact (ihφ x y a1.1 hy'.1).2.2 i a1.2 b1
      | right j =>
        intro a1 b1
        simp only [AA, BB, VV, Fin.addCases_right] at a1 b1 ⊢
        have hψx : mev ψ x = true := by
          have : (mev φ x || mev ψ x) = true := hx
          simp_all
        exact (ihψ x y hψx hy'.2).2.2 j a1.2 b1

end PEqualNP.Outside.L_meta_8164_aux

open PEqualNP.Outside.L_meta_8164_aux in
theorem PEqualNP.Outside.L_meta_8164 : ∀ (x1 : ℕ) (x2 : PEqualNP.MetaComplexity.DMFormula x1),   have x3 : (Fin x1 → Bool) → Bool := fun (x3 : Fin x1 → Bool) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x4 : Fin x1) (x5 : Bool) => x3 x4) (fun (x4 x5 : PEqualNP.MetaComplexity.DMFormula x1) (x6 x7 : Bool) => x6 && x7) (fun (x4 x5 : PEqualNP.MetaComplexity.DMFormula x1) (x6 x7 : Bool) => x6 || x7) x2;   ∃ (x4 : Fin x2.leaves → (Fin x1 → Bool) → Prop) (x5 : Fin x2.leaves → (Fin x1 → Bool) → Prop) (x6 : Fin x2.leaves → Fin x1), ∀ (x7 x8 : Fin x1 → Bool), x3 x7 = Bool.true → x3 x8 = Bool.false → (∃! x11 : Fin x2.leaves, x4 x11 x7 ∧ x5 x11 x8) ∧ ∀ (x11 : Fin x2.leaves), x4 x11 x7 → x5 x11 x8 → x7 (x6 x11) = Bool.true ∧ x8 (x6 x11) = Bool.false := by
  intro n φ x3
  refine ⟨AA φ, BB φ, VV φ, fun x y hx hy => ?_⟩
  obtain ⟨⟨k, hk⟩, hu, hv⟩ := main φ x y hx hy
  exact ⟨⟨k, hk, fun k' hk' => hu k' k hk'.1 hk'.2 hk.1 hk.2⟩, hv⟩
