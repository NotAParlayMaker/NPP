import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_358_aux

/-- The head of an edge is the end that is not in the independent set. -/
theorem pickR {a b t : Fin 5} {I : Finset (Fin 5)} (h : (t = a ∨ t = b) ∧ t ∉ I) (ha : a ∈ I) :
    t = b := by
  rcases h with ⟨h | h, hn⟩
  · exact absurd (h ▸ ha) hn
  · exact h

theorem pickL {a b t : Fin 5} {I : Finset (Fin 5)} (h : (t = a ∨ t = b) ∧ t ∉ I) (hb : b ∈ I) :
    t = a := by
  rcases h with ⟨h | h, hn⟩
  · exact h
  · exact absurd (h ▸ hb) hn

/-- The weighted in-degree at `v`, edge by edge. -/
theorem sum6 (c : Fin 5 × Fin 5 → ℚ) (τ : Fin 5 × Fin 5 → Finset (Fin 5) → Fin 5)
    (I : Finset (Fin 5)) (v : Fin 5) :
    ((([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5)).filter
        (fun e => τ e I = v)).map c).sum
      = (if τ (0, 1) I = v then c (0, 1) else 0) + (if τ (0, 2) I = v then c (0, 2) else 0)
        + (if τ (1, 2) I = v then c (1, 2) else 0) + (if τ (0, 3) I = v then c (0, 3) else 0)
        + (if τ (0, 4) I = v then c (0, 4) else 0) + (if τ (3, 4) I = v then c (3, 4) else 0) := by
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  split_ifs <;> simp <;> ring

end PEqualNP.Outside.L_meta_358_aux

open PEqualNP.Outside.L_meta_358_aux in
theorem PEqualNP.Outside.L_meta_358 : ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] → ∀ τ : Fin 5 × Fin 5 → Finset (Fin 5) → Fin 5, (∀ e ∈ E, ∀ I : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 5 × Fin 5 → ℚ, (∀ I : Finset (Fin 5), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 5, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hc
  subst hE
  have i0 : ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5)),
      ¬ (f.1 ∈ ({0} : Finset (Fin 5)) ∧ f.2 ∈ ({0} : Finset (Fin 5))) := by decide
  have i13 : ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5)),
      ¬ (f.1 ∈ ({1, 3} : Finset (Fin 5)) ∧ f.2 ∈ ({1, 3} : Finset (Fin 5))) := by decide
  have i24 : ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (Fin 5 × Fin 5)),
      ¬ (f.1 ∈ ({2, 4} : Finset (Fin 5)) ∧ f.2 ∈ ({2, 4} : Finset (Fin 5))) := by decide
  -- the set {0}: the four edges at 0 point away from it
  have A01 : τ (0, 1) {0} = 1 := pickR (hτ (0, 1) (by simp) {0} i0) (by simp)
  have A02 : τ (0, 2) {0} = 2 := pickR (hτ (0, 2) (by simp) {0} i0) (by simp)
  have A03 : τ (0, 3) {0} = 3 := pickR (hτ (0, 3) (by simp) {0} i0) (by simp)
  have A04 : τ (0, 4) {0} = 4 := pickR (hτ (0, 4) (by simp) {0} i0) (by simp)
  have B12 : τ (1, 2) {0} = 1 ∨ τ (1, 2) {0} = 2 := (hτ (1, 2) (by simp) {0} i0).1
  have B34 : τ (3, 4) {0} = 3 ∨ τ (3, 4) {0} = 4 := (hτ (3, 4) (by simp) {0} i0).1
  -- the set {1, 3}
  have C01 : τ (0, 1) {1, 3} = 0 := pickL (hτ (0, 1) (by simp) {1, 3} i13) (by simp)
  have C12 : τ (1, 2) {1, 3} = 2 := pickR (hτ (1, 2) (by simp) {1, 3} i13) (by simp)
  have C03 : τ (0, 3) {1, 3} = 0 := pickL (hτ (0, 3) (by simp) {1, 3} i13) (by simp)
  have C34 : τ (3, 4) {1, 3} = 4 := pickR (hτ (3, 4) (by simp) {1, 3} i13) (by simp)
  have D02 : τ (0, 2) {1, 3} = 0 ∨ τ (0, 2) {1, 3} = 2 := (hτ (0, 2) (by simp) {1, 3} i13).1
  have D04 : τ (0, 4) {1, 3} = 0 ∨ τ (0, 4) {1, 3} = 4 := (hτ (0, 4) (by simp) {1, 3} i13).1
  -- the set {2, 4}
  have F02 : τ (0, 2) {2, 4} = 0 := pickL (hτ (0, 2) (by simp) {2, 4} i24) (by simp)
  have F12 : τ (1, 2) {2, 4} = 1 := pickL (hτ (1, 2) (by simp) {2, 4} i24) (by simp)
  have F04 : τ (0, 4) {2, 4} = 0 := pickL (hτ (0, 4) (by simp) {2, 4} i24) (by simp)
  have F34 : τ (3, 4) {2, 4} = 3 := pickL (hτ (3, 4) (by simp) {2, 4} i24) (by simp)
  have G01 : τ (0, 1) {2, 4} = 0 ∨ τ (0, 1) {2, 4} = 1 := (hτ (0, 1) (by simp) {2, 4} i24).1
  have G03 : τ (0, 3) {2, 4} = 0 ∨ τ (0, 3) {2, 4} = 3 := (hτ (0, 3) (by simp) {2, 4} i24).1
  -- the in-degree equations that are used
  have s1 := hc {0} i0 1
  have s2 := hc {0} i0 2
  have s3 := hc {0} i0 3
  have s4 := hc {0} i0 4
  have u2 := hc {1, 3} i13 2
  have u4 := hc {1, 3} i13 4
  have w1 := hc {2, 4} i24 1
  have w3 := hc {2, 4} i24 3
  rw [sum6] at s1 s2 s3 s4 u2 u4 w1 w3
  have key : c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 ∧ c (0, 3) = 0 ∧ c (0, 4) = 0
      ∧ c (3, 4) = 0 := by
    rcases B12 with b12 | b12 <;> rcases B34 with b34 | b34 <;>
    rcases D02 with d02 | d02 <;> rcases D04 with d04 | d04 <;>
    rcases G01 with g01 | g01 <;> rcases G03 with g03 | g03 <;>
    simp [A01, A02, A03, A04, b12, b34, C01, C12, C03, C34, d02, d04, F02, F12, F04, F34,
      g01, g03] at s1 s2 s3 s4 u2 u4 w1 w3 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact key.1
  · exact key.2.1
  · exact key.2.2.1
  · exact key.2.2.2.1
  · exact key.2.2.2.2.1
  · exact key.2.2.2.2.2
