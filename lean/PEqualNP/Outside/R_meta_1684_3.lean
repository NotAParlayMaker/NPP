import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1684_3
    (geometry : let I : Fin 13 → Fin 13 → Prop := fun p w =>
      ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = w+d
    ∀ P : Finset (Fin 13), ((P.card ≤ 3 ∧ ∃ w, ∀ p ∈ P, I p w) ∨
      (∃ W : Finset (Fin 13), W.card ≤ 3 ∧ (∃ v, ∀ w ∈ W, I v w) ∧
        ∀ p, p ∈ P ↔ ∀ w ∈ W, ¬ I p w)) →
      (∀ v, v ∉ P → ∃ w, (∀ p ∈ P, ¬ I p w) ∧ I v w) ∧
      ((∃ l, ∀ p ∈ P, I p l) ∨ (∃ v, ∀ w, (∀ p ∈ P, ¬ I p w) → I v w)))
    (lower : let I : Fin 13 → Fin 13 → Prop := fun p w =>
      ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = w+d
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p w, I p w → C.eval (List.ofFn (fun k : Fin 26 =>
        decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w))) = true) →
      (∀ P : Finset (Fin 13), ((P.card ≤ 3 ∧ ∃ w, ∀ p ∈ P, I p w) ∨
      (∃ W : Finset (Fin 13), W.card ≤ 3 ∧ (∃ v, ∀ w ∈ W, I v w) ∧
        ∀ p, p ∈ P ↔ ∀ w ∈ W, ¬ I p w)) →
        C.eval (List.ofFn (fun k : Fin 26 => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
          ∃ w, k = Fin.natAdd 13 w ∧ ∀ p ∈ P, ¬ I p w))) = false) →
      64 ≤ C.size) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  rintro ⟨C, hC, hsize, hpos, hneg⟩
  have hI (p w : Fin 13) :
      (∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = w+d) ↔
      (∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = w+d) := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false,Finset.mem_insert,Finset.mem_singleton]
  have hbound := lower C hC (fun p w hi => hpos p w ((hI p w).1 hi)) (by
    intro P hshape
    obtain ⟨hclosed, hdeg⟩ := geometry P hshape
    simp_rw [hI] at hclosed hdeg ⊢
    exact hneg P hclosed hdeg)
  omega
