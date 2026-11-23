import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_180_Proof

open PEqualNP.MetaComplexity

def ren {N M : ℕ} (ρ : Fin N → Fin M) : DMFormula N → DMFormula M
  | DMFormula.lit i b => DMFormula.lit (ρ i) b
  | DMFormula.and φ ψ => DMFormula.and (ren ρ φ) (ren ρ ψ)
  | DMFormula.or φ ψ => DMFormula.or (ren ρ φ) (ren ρ ψ)

theorem ren_eval {N M : ℕ} (ρ : Fin N → Fin M) (z : Fin M → Bool) :
    ∀ φ : DMFormula N, (ren ρ φ).eval z = φ.eval (fun i => z (ρ i))
  | DMFormula.lit _ _ => rfl
  | DMFormula.and φ ψ => by
    simp only [ren, DMFormula.eval, ren_eval ρ z φ, ren_eval ρ z ψ]
  | DMFormula.or φ ψ => by
    simp only [ren, DMFormula.eval, ren_eval ρ z φ, ren_eval ρ z ψ]

theorem ren_leaves {N M : ℕ} (ρ : Fin N → Fin M) :
    ∀ φ : DMFormula N, (ren ρ φ).leaves = φ.leaves
  | DMFormula.lit _ _ => rfl
  | DMFormula.and φ ψ => by
    simp only [ren, DMFormula.leaves, ren_leaves ρ φ, ren_leaves ρ ψ]
  | DMFormula.or φ ψ => by
    simp only [ren, DMFormula.leaves, ren_leaves ρ φ, ren_leaves ρ ψ]

def rlit {M : ℕ} : (Fin M ⊕ Bool) → Bool → (DMFormula M ⊕ Bool)
  | Sum.inl j, b => Sum.inl (DMFormula.lit j b)
  | Sum.inr c, b => Sum.inr (if b then c else !c)

def rand {M : ℕ} : (DMFormula M ⊕ Bool) → (DMFormula M ⊕ Bool) → (DMFormula M ⊕ Bool)
  | Sum.inr false, _ => Sum.inr false
  | Sum.inr true, r => r
  | Sum.inl _, Sum.inr false => Sum.inr false
  | Sum.inl φ, Sum.inr true => Sum.inl φ
  | Sum.inl φ, Sum.inl ψ => Sum.inl (DMFormula.and φ ψ)

def ror {M : ℕ} : (DMFormula M ⊕ Bool) → (DMFormula M ⊕ Bool) → (DMFormula M ⊕ Bool)
  | Sum.inr true, _ => Sum.inr true
  | Sum.inr false, r => r
  | Sum.inl _, Sum.inr true => Sum.inr true
  | Sum.inl φ, Sum.inr false => Sum.inl φ
  | Sum.inl φ, Sum.inl ψ => Sum.inl (DMFormula.or φ ψ)

def rval {M : ℕ} : (DMFormula M ⊕ Bool) → (Fin M → Bool) → Bool
  | Sum.inl φ, x => φ.eval x
  | Sum.inr c, _ => c

def rleaves {M : ℕ} : (DMFormula M ⊕ Bool) → ℕ
  | Sum.inl φ => φ.leaves
  | Sum.inr _ => 0

theorem rand_val {M : ℕ} (r1 r2 : DMFormula M ⊕ Bool) (x : Fin M → Bool) :
    rval (rand r1 r2) x = (rval r1 x && rval r2 x) := by
  rcases r1 with φ | (_ | _) <;> rcases r2 with ψ | (_ | _) <;>
    simp [rand, rval, DMFormula.eval]

theorem ror_val {M : ℕ} (r1 r2 : DMFormula M ⊕ Bool) (x : Fin M → Bool) :
    rval (ror r1 r2) x = (rval r1 x || rval r2 x) := by
  rcases r1 with φ | (_ | _) <;> rcases r2 with ψ | (_ | _) <;>
    simp [ror, rval, DMFormula.eval]

theorem rand_leaves {M : ℕ} (r1 r2 : DMFormula M ⊕ Bool) :
    rleaves (rand r1 r2) ≤ rleaves r1 + rleaves r2 := by
  rcases r1 with φ | (_ | _) <;> rcases r2 with ψ | (_ | _) <;>
    simp [rand, rleaves, DMFormula.leaves]

theorem ror_leaves {M : ℕ} (r1 r2 : DMFormula M ⊕ Bool) :
    rleaves (ror r1 r2) ≤ rleaves r1 + rleaves r2 := by
  rcases r1 with φ | (_ | _) <;> rcases r2 with ψ | (_ | _) <;>
    simp [ror, rleaves, DMFormula.leaves]

def subst {N M : ℕ} (σ : Fin N → (Fin M ⊕ Bool)) : DMFormula N → (DMFormula M ⊕ Bool)
  | DMFormula.lit i b => rlit (σ i) b
  | DMFormula.and φ ψ => rand (subst σ φ) (subst σ ψ)
  | DMFormula.or φ ψ => ror (subst σ φ) (subst σ ψ)

def cnt {N M : ℕ} (σ : Fin N → (Fin M ⊕ Bool)) : DMFormula N → ℕ
  | DMFormula.lit i _ => Sum.elim (fun _ => 1) (fun _ => 0) (σ i)
  | DMFormula.and φ ψ => cnt σ φ + cnt σ ψ
  | DMFormula.or φ ψ => cnt σ φ + cnt σ ψ

theorem subst_val {N M : ℕ} (σ : Fin N → (Fin M ⊕ Bool)) (x : Fin M → Bool) :
    ∀ φ : DMFormula N, rval (subst σ φ) x = φ.eval (fun i => Sum.elim x id (σ i))
  | DMFormula.lit i b => by
    simp only [subst, DMFormula.eval]
    cases σ i with
    | inl j => simp [rlit, rval, DMFormula.eval]
    | inr c => cases b <;> simp [rlit, rval]
  | DMFormula.and φ ψ => by
    simp only [subst, rand_val, subst_val σ x φ, subst_val σ x ψ, DMFormula.eval]
  | DMFormula.or φ ψ => by
    simp only [subst, ror_val, subst_val σ x φ, subst_val σ x ψ, DMFormula.eval]

theorem subst_leaves {N M : ℕ} (σ : Fin N → (Fin M ⊕ Bool)) :
    ∀ φ : DMFormula N, rleaves (subst σ φ) ≤ cnt σ φ
  | DMFormula.lit i b => by
    simp only [subst, cnt]
    cases σ i <;> simp [rlit, rleaves, DMFormula.leaves]
  | DMFormula.and φ ψ => by
    simp only [subst, cnt]
    exact le_trans (rand_leaves _ _) (Nat.add_le_add (subst_leaves σ φ) (subst_leaves σ ψ))
  | DMFormula.or φ ψ => by
    simp only [subst, cnt]
    exact le_trans (ror_leaves _ _) (Nat.add_le_add (subst_leaves σ φ) (subst_leaves σ ψ))

def sL {n k : ℕ} (y0 : Fin k → Bool) : Fin (n + k) → (Fin n ⊕ Bool) :=
  fun i => Fin.addCases (fun i' => Sum.inl i') (fun j => Sum.inr (y0 j)) i

def sR {n k : ℕ} (x0 : Fin n → Bool) : Fin (n + k) → (Fin k ⊕ Bool) :=
  fun i => Fin.addCases (fun i' => Sum.inr (x0 i')) (fun j => Sum.inl j) i

theorem cnt_split {n k : ℕ} (x0 : Fin n → Bool) (y0 : Fin k → Bool) :
    ∀ Φ : DMFormula (n + k), cnt (sL y0) Φ + cnt (sR x0) Φ = Φ.leaves
  | DMFormula.lit i _ => by
    simp only [cnt, DMFormula.leaves, sL, sR]
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
    · simp
    · simp
  | DMFormula.and φ ψ => by
    simp only [cnt, DMFormula.leaves]
    have h1 := cnt_split x0 y0 φ
    have h2 := cnt_split x0 y0 ψ
    omega
  | DMFormula.or φ ψ => by
    simp only [cnt, DMFormula.leaves]
    have h1 := cnt_split x0 y0 φ
    have h2 := cnt_split x0 y0 ψ
    omega

theorem sL_fun {n k : ℕ} (x : Fin n → Bool) (y0 : Fin k → Bool) :
    (fun i => Sum.elim x id (sL y0 i)) = Fin.addCases x y0 := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
  · simp [sL]
  · simp [sL]

theorem sR_fun {n k : ℕ} (x0 : Fin n → Bool) (y : Fin k → Bool) :
    (fun i => Sum.elim y id (sR x0 i)) = Fin.addCases x0 y := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
  · simp [sR]
  · simp [sR]

theorem low {M : ℕ} (h : (Fin M → Bool) → Bool) (c : ℕ) (r : DMFormula M ⊕ Bool) (bound : ℕ)
    (hc : ∀ t : ℕ, HasLeafSize M h t ↔ c ≤ t)
    (h1 : ∃ x, h x = true) (h0 : ∃ x, h x = false)
    (hval : ∀ x, rval r x = h x) (hle : rleaves r ≤ bound) : c ≤ bound := by
  rcases r with φ | b
  · have hsz : HasLeafSize M h φ.leaves := ⟨φ, le_rfl, hval⟩
    exact le_trans ((hc _).mp hsz) hle
  · obtain ⟨x1, hx1⟩ := h1
    obtain ⟨x0, hx0⟩ := h0
    have e1 : b = h x1 := hval x1
    have e0 : b = h x0 := hval x0
    rw [hx1] at e1
    rw [hx0] at e0
    rw [e1] at e0
    exact absurd e0 (by decide)

end PEqualNP.Outside.L_meta_180_Proof

open PEqualNP.Outside.L_meta_180_Proof PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_180 : ∀ (n k : ℕ) (f : (Fin n → Bool) → Bool) (g : (Fin k → Bool) → Bool) (a b : ℕ), (∃ x : Fin n → Bool, f x = true) → (∃ x : Fin n → Bool, f x = false) → (∃ y : Fin k → Bool, g y = true) → (∃ y : Fin k → Bool, g y = false) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize n f r ↔ a ≤ r) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize k g r ↔ b ≤ r) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasLeafSize (n + k) (fun z : Fin (n + k) → Bool => f (fun i : Fin n => z (Fin.castAdd k i)) || g (fun j : Fin k => z (Fin.natAdd n j))) s ↔ a + b ≤ s) := by
  intro n k f g a b hf1 hf0 hg1 hg0 ha hb s
  constructor
  · rintro ⟨Φ, hΦs, hΦ⟩
    obtain ⟨x0, hx0⟩ := hf0
    obtain ⟨y0, hy0⟩ := hg0
    have hL : a ≤ cnt (sL y0) Φ := by
      refine low f a (subst (sL y0) Φ) _ ha hf1 ⟨x0, hx0⟩ ?_ (subst_leaves _ _)
      intro x
      rw [subst_val, sL_fun, hΦ]
      simp [hy0]
    have hR : b ≤ cnt (sR x0) Φ := by
      refine low g b (subst (sR x0) Φ) _ hb hg1 ⟨y0, hy0⟩ ?_ (subst_leaves _ _)
      intro y
      rw [subst_val, sR_fun, hΦ]
      simp [hx0]
    have hsp := cnt_split x0 y0 Φ
    omega
  · intro hs
    obtain ⟨φ, hφ, hφe⟩ := (ha a).mpr le_rfl
    obtain ⟨ψ, hψ, hψe⟩ := (hb b).mpr le_rfl
    refine ⟨DMFormula.or (ren (Fin.castAdd k) φ) (ren (Fin.natAdd n) ψ), ?_, ?_⟩
    · simp only [DMFormula.leaves, ren_leaves]
      omega
    · intro z
      simp only [DMFormula.eval, ren_eval, hφe, hψe]
