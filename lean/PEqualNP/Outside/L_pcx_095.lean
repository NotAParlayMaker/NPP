import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_095_aux

open PEqualNP.ProofComplexity

private def stepOK {V : Type} [DecidableEq V] (axioms : List (Clause V))
    (acc : List (Clause V)) (C : Clause V) : Option (ℕ × ℕ × V) → Bool
  | none => decide (C ∈ axioms)
  | some (i, j, v) =>
    match acc[i]?, acc[j]? with
    | some A, some B =>
      decide ((v, true) ∈ A ∧ (v, false) ∈ B ∧
        C = A.erase (v, true) ∪ B.erase (v, false))
    | _, _ => false

private theorem checkedStep {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {axioms acc : List (Clause V)} {C : Clause V} {reason : Option (ℕ × ℕ × V)}
    (sub : ∀ D ∈ axioms, D ∈ F) (hd : IsDerivation F acc)
    (ok : stepOK axioms acc C reason = true) : IsDerivation F (C :: acc) := by
  rcases reason with _ | ⟨i, j, v⟩
  · exact .ax hd (sub C (of_decide_eq_true ok))
  · cases hA : acc[i]? with
    | none => simp [stepOK, hA] at ok
    | some A =>
      cases hB : acc[j]? with
      | none => simp [stepOK, hA, hB] at ok
      | some B =>
        exact .res hd (List.mem_of_getElem? hA) (List.mem_of_getElem? hB)
          ⟨v, of_decide_eq_true (by simpa only [stepOK, hA, hB] using ok)⟩

private def certOK {V : Type} [DecidableEq V] (axioms : List (Clause V)) (w : ℕ)
    (acc : List (Clause V)) : List (Clause V × Option (ℕ × ℕ × V)) → Bool
  | [] => decide ((∅ : Clause V) ∈ acc)
  | (C, why) :: rest =>
    (decide (C.card ≤ w) && stepOK axioms acc C why) && certOK axioms w (C :: acc) rest

private theorem checkedCert {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {axioms : List (Clause V)} {w : ℕ} (sub : ∀ D ∈ axioms, D ∈ F)
    (steps : List (Clause V × Option (ℕ × ℕ × V))) (acc : List (Clause V))
    (hd : IsDerivation F acc) (hw : ∀ D ∈ acc, D.card ≤ w)
    (ok : certOK axioms w acc steps = true) :
    ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ w := by
  induction steps generalizing acc with
  | nil => exact ⟨acc, ⟨hd, of_decide_eq_true ok⟩, hw⟩
  | cons step rest ih =>
    obtain ⟨C, why⟩ := step
    simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at ok
    exact ih (C :: acc) (checkedStep sub hd ok.1.2)
      (fun D hD => by
        rcases List.mem_cons.mp hD with rfl | hD
        · exact ok.1.1
        · exact hw D hD)
      ok.2


private def trianglesFormula : Set (Clause ((Fin 6 × Fin 3) ⊕ Fin 6)) :=
  {C6 | ∃ v7 : Fin 6, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C9 | ∃ (u10 v11 : Fin 6) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (u10 ≠ v11 ∧ u10.val / 3 = v11.val / 3) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C14 | ∃ (e15 : Fin 6) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).1, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).2, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 6), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).1 ∉ S18 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).2 ∉ S18)).image (fun e20 : Fin 6 => ((Sum.inr e20 : (Fin 6 × Fin 3) ⊕ Fin 6), true))}

private def trianglesAxioms : List (Clause ((Fin 6 × Fin 3) ⊕ Fin 6)) :=
  [
  {(Sum.inr 0, false), (Sum.inl (1, 0), false), (Sum.inl (0, 0), false)},
  {(Sum.inl (1, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inr 0, true), (Sum.inr 1, true), (Sum.inr 2, true)},
  {(Sum.inr 2, false), (Sum.inl (2, 0), false), (Sum.inl (0, 0), false)},
  {(Sum.inl (2, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inr 3, false), (Sum.inl (4, 1), false), (Sum.inl (3, 1), false)},
  {(Sum.inr 1, true), (Sum.inr 3, true)},
  {(Sum.inr 5, false), (Sum.inl (5, 2), false), (Sum.inl (3, 2), false)},
  {(Sum.inr 1, true), (Sum.inr 5, true)},
  {(Sum.inr 4, false), (Sum.inl (5, 2), false), (Sum.inl (4, 2), false)},
  {(Sum.inr 1, true), (Sum.inr 4, true)},
  {(Sum.inl (0, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inr 5, false), (Sum.inl (5, 1), false), (Sum.inl (3, 1), false)},
  {(Sum.inr 3, false), (Sum.inl (4, 2), false), (Sum.inl (3, 2), false)},
  {(Sum.inr 4, false), (Sum.inl (5, 1), false), (Sum.inl (4, 1), false)},
  {(Sum.inl (2, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inr 1, false), (Sum.inl (2, 1), false), (Sum.inl (1, 1), false)},
  {(Sum.inl (2, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inr 1, false), (Sum.inl (2, 0), false), (Sum.inl (1, 0), false)},
  {(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (1, 2), false)},
  {(Sum.inl (1, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (2, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (2, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
  {(Sum.inr 3, false), (Sum.inl (4, 0), false), (Sum.inl (3, 0), false)},
  {(Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inr 0, false), (Sum.inl (1, 2), false), (Sum.inl (0, 2), false)},
  {(Sum.inl (0, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
  {(Sum.inr 0, true), (Sum.inr 4, true)},
  {(Sum.inr 0, false), (Sum.inl (1, 1), false), (Sum.inl (0, 1), false)},
  {(Sum.inl (0, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inr 4, false), (Sum.inl (5, 0), false), (Sum.inl (4, 0), false)},
  {(Sum.inl (2, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (5, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (1, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
  {(Sum.inl (2, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
  {(Sum.inr 3, true), (Sum.inr 4, true), (Sum.inr 5, true)},
  {(Sum.inr 5, false), (Sum.inl (5, 0), false), (Sum.inl (3, 0), false)},
  {(Sum.inl (1, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)},
  {(Sum.inl (2, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}
  ]

private theorem trianglesAxiomsValid : ∀ C ∈ trianglesAxioms, C ∈ trianglesFormula := by
  intro C h
  simp only [trianglesAxioms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inr ⟨0, 0, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨1, 3, ![false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨0, 3, ![false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inr ⟨{3, 4}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨2, 0, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨2, 3, ![false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨3, 1, by decide⟩)
  · exact Or.inr ⟨{0, 5}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨5, 2, by decide⟩)
  · exact Or.inr ⟨{0, 4}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨4, 2, by decide⟩)
  · exact Or.inr ⟨{0, 3}, by decide, by decide⟩
  · exact Or.inl (Or.inl (Or.inr ⟨0, 4, ![false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨0, 5, ![false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨5, 1, by decide⟩)
  · exact Or.inl (Or.inr ⟨3, 2, by decide⟩)
  · exact Or.inl (Or.inr ⟨4, 1, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨2, 4, ![false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 5, ![false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨1, 1, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨1, 0, by decide⟩)
  · exact Or.inl (Or.inr ⟨1, 2, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨2, 3, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨3, 0, by decide⟩)
  · exact Or.inl (Or.inl (Or.inl ⟨4, by decide⟩))
  · exact Or.inl (Or.inr ⟨0, 2, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 4, ![true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inr ⟨{2, 3}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨0, 1, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 4, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨4, 0, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 5, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inl ⟨5, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨0, 5, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 5, ![true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inr ⟨{0, 1}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨5, 0, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨2, 3, ![true, true, false], by decide, by decide, by decide⟩))

private def trianglesCertificate : List (Clause ((Fin 6 × Fin 3) ⊕ Fin 6) × Option (ℕ × ℕ × ((Fin 6 × Fin 3) ⊕ Fin 6))) :=
  [
  ({(Sum.inr 0, false), (Sum.inl (1, 0), false), (Sum.inl (0, 0), false)}, none),
  ({(Sum.inl (1, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (0, 0), false), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (0, 1, Sum.inl (1, 0))),
  ({(Sum.inl (0, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (0, 1, Sum.inl (0, 0))),
  ({(Sum.inr 0, true), (Sum.inr 1, true), (Sum.inr 2, true)}, none),
  ({(Sum.inl (3, 1), true), (Sum.inl (3, 2), true), (Sum.inr 1, true), (Sum.inr 2, true)}, some (0, 1, Sum.inr 0)),
  ({(Sum.inr 2, false), (Sum.inl (2, 0), false), (Sum.inl (0, 0), false)}, none),
  ({(Sum.inl (2, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, none),
  ({(Sum.inr 2, false), (Sum.inl (0, 0), false), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (0, 1, Sum.inl (2, 0))),
  ({(Sum.inr 2, false), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (6, 0, Sum.inl (0, 0))),
  ({(Sum.inl (3, 1), true), (Sum.inl (3, 2), true), (Sum.inr 1, true)}, some (4, 0, Sum.inr 2)),
  ({(Sum.inr 3, false), (Sum.inl (4, 1), false), (Sum.inl (3, 1), false)}, none),
  ({(Sum.inr 1, true), (Sum.inr 3, true)}, none),
  ({(Sum.inl (4, 1), false), (Sum.inl (3, 1), false), (Sum.inr 1, true)}, some (0, 1, Sum.inr 3)),
  ({(Sum.inl (4, 1), false), (Sum.inl (3, 2), true), (Sum.inr 1, true)}, some (3, 0, Sum.inl (3, 1))),
  ({(Sum.inr 5, false), (Sum.inl (5, 2), false), (Sum.inl (3, 2), false)}, none),
  ({(Sum.inr 1, true), (Sum.inr 5, true)}, none),
  ({(Sum.inl (5, 2), false), (Sum.inl (3, 2), false), (Sum.inr 1, true)}, some (0, 1, Sum.inr 5)),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 1), false), (Sum.inr 1, true)}, some (3, 0, Sum.inl (3, 2))),
  ({(Sum.inr 4, false), (Sum.inl (5, 2), false), (Sum.inl (4, 2), false)}, none),
  ({(Sum.inr 1, true), (Sum.inr 4, true)}, none),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 2), false), (Sum.inr 1, true)}, some (0, 1, Sum.inr 4)),
  ({(Sum.inl (0, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inl (5, 2), false), (Sum.inl (0, 0), true), (Sum.inl (4, 1), true), (Sum.inr 1, true)}, some (0, 1, Sum.inl (4, 2))),
  ({(Sum.inl (5, 2), false), (Sum.inl (0, 0), true), (Sum.inr 1, true)}, some (0, 5, Sum.inl (4, 1))),
  ({(Sum.inl (0, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)}, none),
  ({(Sum.inl (0, 0), true), (Sum.inl (5, 1), true), (Sum.inr 1, true)}, some (0, 1, Sum.inl (5, 2))),
  ({(Sum.inr 5, false), (Sum.inl (5, 1), false), (Sum.inl (3, 1), false)}, none),
  ({(Sum.inl (5, 1), false), (Sum.inl (3, 1), false), (Sum.inr 1, true)}, some (11, 0, Sum.inr 5)),
  ({(Sum.inl (5, 1), false), (Sum.inl (3, 2), true), (Sum.inr 1, true)}, some (18, 0, Sum.inl (3, 1))),
  ({(Sum.inr 3, false), (Sum.inl (4, 2), false), (Sum.inl (3, 2), false)}, none),
  ({(Sum.inl (4, 2), false), (Sum.inl (3, 2), false), (Sum.inr 1, true)}, some (18, 0, Sum.inr 3)),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 2), false), (Sum.inr 1, true)}, some (2, 0, Sum.inl (3, 2))),
  ({(Sum.inr 4, false), (Sum.inl (5, 1), false), (Sum.inl (4, 1), false)}, none),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 1), false), (Sum.inr 1, true)}, some (13, 0, Sum.inr 4)),
  ({(Sum.inl (5, 1), false), (Sum.inl (0, 0), true), (Sum.inl (4, 2), true), (Sum.inr 1, true)}, some (12, 0, Sum.inl (4, 1))),
  ({(Sum.inl (5, 1), false), (Sum.inl (0, 0), true), (Sum.inr 1, true)}, some (0, 3, Sum.inl (4, 2))),
  ({(Sum.inl (0, 0), true), (Sum.inr 1, true)}, some (10, 0, Sum.inl (5, 1))),
  ({(Sum.inr 2, false), (Sum.inl (2, 0), false), (Sum.inr 1, true)}, some (0, 31, Sum.inl (0, 0))),
  ({(Sum.inl (2, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inl (5, 2), false), (Sum.inl (2, 0), true), (Sum.inl (4, 1), true), (Sum.inr 1, true)}, some (0, 18, Sum.inl (4, 2))),
  ({(Sum.inl (5, 2), false), (Sum.inl (2, 0), true), (Sum.inr 1, true)}, some (0, 22, Sum.inl (4, 1))),
  ({(Sum.inl (2, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)}, none),
  ({(Sum.inl (2, 0), true), (Sum.inl (5, 1), true), (Sum.inr 1, true)}, some (0, 1, Sum.inl (5, 2))),
  ({(Sum.inl (5, 1), false), (Sum.inl (2, 0), true), (Sum.inl (4, 2), true), (Sum.inr 1, true)}, some (4, 9, Sum.inl (4, 1))),
  ({(Sum.inl (5, 1), false), (Sum.inl (2, 0), true), (Sum.inr 1, true)}, some (0, 12, Sum.inl (4, 2))),
  ({(Sum.inl (2, 0), true), (Sum.inr 1, true)}, some (2, 0, Sum.inl (5, 1))),
  ({(Sum.inr 2, false), (Sum.inr 1, true)}, some (0, 8, Sum.inl (2, 0))),
  ({(Sum.inr 0, false), (Sum.inl (1, 0), false), (Sum.inr 1, true)}, some (10, 48, Sum.inl (0, 0))),
  ({(Sum.inl (1, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inl (5, 2), false), (Sum.inl (1, 0), true), (Sum.inl (4, 1), true), (Sum.inr 1, true)}, some (0, 28, Sum.inl (4, 2))),
  ({(Sum.inl (5, 2), false), (Sum.inl (1, 0), true), (Sum.inr 1, true)}, some (0, 32, Sum.inl (4, 1))),
  ({(Sum.inl (1, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)}, none),
  ({(Sum.inl (1, 0), true), (Sum.inl (5, 1), true), (Sum.inr 1, true)}, some (0, 1, Sum.inl (5, 2))),
  ({(Sum.inl (5, 1), false), (Sum.inl (1, 0), true), (Sum.inl (4, 2), true), (Sum.inr 1, true)}, some (4, 19, Sum.inl (4, 1))),
  ({(Sum.inl (5, 1), false), (Sum.inl (1, 0), true), (Sum.inr 1, true)}, some (0, 22, Sum.inl (4, 2))),
  ({(Sum.inl (1, 0), true), (Sum.inr 1, true)}, some (2, 0, Sum.inl (5, 1))),
  ({(Sum.inr 0, false), (Sum.inr 1, true)}, some (0, 8, Sum.inl (1, 0))),
  ({(Sum.inr 1, true), (Sum.inr 2, true)}, some (53, 0, Sum.inr 0)),
  ({(Sum.inr 1, true)}, some (0, 11, Sum.inr 2)),
  ({(Sum.inr 1, false), (Sum.inl (2, 1), false), (Sum.inl (1, 1), false)}, none),
  ({(Sum.inl (2, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (1, 1), false), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, some (0, 1, Sum.inl (2, 1))),
  ({(Sum.inl (1, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, some (0, 1, Sum.inl (1, 1))),
  ({(Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, some (5, 0, Sum.inr 1)),
  ({(Sum.inr 1, false), (Sum.inl (2, 0), false), (Sum.inl (1, 0), false)}, none),
  ({(Sum.inr 1, false), (Sum.inl (1, 0), false), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (59, 0, Sum.inl (2, 0))),
  ({(Sum.inr 1, false), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (67, 0, Sum.inl (1, 0))),
  ({(Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (58, 0, Sum.inr 1)),
  ({(Sum.inr 3, false), (Sum.inl (4, 1), false), (Sum.inl (3, 2), true)}, some (0, 58, Sum.inl (3, 1))),
  ({(Sum.inr 3, false), (Sum.inl (4, 2), false), (Sum.inl (4, 1), false)}, some (0, 40, Sum.inl (3, 2))),
  ({(Sum.inr 3, false), (Sum.inl (4, 1), false), (Sum.inl (4, 0), true)}, some (6, 0, Sum.inl (4, 2))),
  ({(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (1, 2), false)}, none),
  ({(Sum.inl (1, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, some (0, 1, Sum.inl (1, 2))),
  ({(Sum.inl (2, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, some (0, 1, Sum.inl (2, 2))),
  ({(Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, some (18, 0, Sum.inr 1)),
  ({(Sum.inr 3, false), (Sum.inl (4, 0), true)}, some (0, 6, Sum.inl (4, 1))),
  ({(Sum.inl (2, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (1, 1), false), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (0, 20, Sum.inl (2, 1))),
  ({(Sum.inl (1, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (0, 1, Sum.inl (1, 1))),
  ({(Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (24, 0, Sum.inr 1)),
  ({(Sum.inr 3, false), (Sum.inl (4, 0), false), (Sum.inl (3, 0), false)}, none),
  ({(Sum.inr 3, false), (Sum.inl (4, 0), false), (Sum.inl (3, 2), true)}, some (1, 0, Sum.inl (3, 0))),
  ({(Sum.inr 3, false), (Sum.inl (3, 2), true)}, some (7, 0, Sum.inl (4, 0))),
  ({(Sum.inr 1, false), (Sum.inl (1, 0), false), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)}, some (45, 21, Sum.inl (2, 0))),
  ({(Sum.inr 1, false), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)}, some (36, 0, Sum.inl (1, 0))),
  ({(Sum.inl (5, 1), true), (Sum.inl (5, 2), true)}, some (30, 0, Sum.inr 1)),
  ({(Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inr 4, false), (Sum.inl (5, 2), false), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, some (0, 72, Sum.inl (4, 2))),
  ({(Sum.inr 0, false), (Sum.inl (1, 2), false), (Sum.inl (0, 2), false)}, none),
  ({(Sum.inl (0, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (1, 2), false), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, some (0, 1, Sum.inl (0, 2))),
  ({(Sum.inr 0, false), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, some (21, 0, Sum.inl (1, 2))),
  ({(Sum.inr 0, true), (Sum.inr 4, true)}, none),
  ({(Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inr 4, true)}, some (0, 1, Sum.inr 0)),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, some (0, 6, Sum.inr 4)),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 0), true), (Sum.inr 1, true)}, some (0, 81, Sum.inl (4, 1))),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, some (0, 36, Sum.inr 1)),
  ({(Sum.inr 4, false), (Sum.inl (5, 2), false), (Sum.inl (4, 0), true)}, some (0, 82, Sum.inl (4, 2))),
  ({(Sum.inr 4, false), (Sum.inl (4, 0), true), (Sum.inl (5, 1), true)}, some (12, 0, Sum.inl (5, 2))),
  ({(Sum.inr 4, false), (Sum.inl (5, 1), false), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, some (12, 70, Sum.inl (4, 1))),
  ({(Sum.inr 0, false), (Sum.inl (1, 1), false), (Sum.inl (0, 1), false)}, none),
  ({(Sum.inr 0, false), (Sum.inl (0, 1), false), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, some (42, 0, Sum.inl (1, 1))),
  ({(Sum.inl (0, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, some (0, 1, Sum.inl (0, 1))),
  ({(Sum.inl (4, 0), true), (Sum.inl (4, 2), true), (Sum.inr 4, true)}, some (11, 0, Sum.inr 0)),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, some (0, 5, Sum.inr 4)),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 0), true), (Sum.inr 1, true)}, some (0, 78, Sum.inl (4, 2))),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, some (0, 34, Sum.inr 1)),
  ({(Sum.inr 4, false), (Sum.inl (5, 1), false), (Sum.inl (4, 0), true)}, some (0, 79, Sum.inl (4, 1))),
  ({(Sum.inr 4, false), (Sum.inl (4, 0), true)}, some (10, 0, Sum.inl (5, 1))),
  ({(Sum.inr 4, false), (Sum.inl (5, 0), false), (Sum.inl (4, 0), false)}, none),
  ({(Sum.inr 4, false), (Sum.inl (5, 0), false)}, some (1, 0, Sum.inl (4, 0))),
  ({(Sum.inl (2, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (1, 1), false), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, some (0, 57, Sum.inl (2, 1))),
  ({(Sum.inl (1, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, some (0, 1, Sum.inl (1, 1))),
  ({(Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, some (61, 0, Sum.inr 1)),
  ({(Sum.inr 4, false), (Sum.inl (5, 2), true)}, some (0, 5, Sum.inl (5, 0))),
  ({(Sum.inr 1, false), (Sum.inl (1, 0), false), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, some (83, 56, Sum.inl (2, 0))),
  ({(Sum.inr 1, false), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, some (74, 0, Sum.inl (1, 0))),
  ({(Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, some (65, 0, Sum.inr 1)),
  ({(Sum.inr 4, false), (Sum.inl (5, 2), false), (Sum.inl (4, 1), true)}, some (0, 106, Sum.inl (4, 2))),
  ({(Sum.inr 4, false), (Sum.inl (4, 1), true)}, some (4, 0, Sum.inl (5, 2))),
  ({(Sum.inl (5, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)}, none),
  ({(Sum.inr 4, false), (Sum.inl (4, 1), false), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, some (0, 95, Sum.inl (5, 1))),
  ({(Sum.inr 0, false), (Sum.inl (0, 1), false), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, some (10, 24, Sum.inl (1, 1))),
  ({(Sum.inl (0, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, some (0, 1, Sum.inl (0, 1))),
  ({(Sum.inl (5, 0), true), (Sum.inl (5, 2), true), (Sum.inr 4, true)}, some (35, 0, Sum.inr 0)),
  ({(Sum.inl (4, 1), false), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)}, some (0, 4, Sum.inr 4)),
  ({(Sum.inl (4, 1), false), (Sum.inl (5, 0), true), (Sum.inr 1, true)}, some (0, 116, Sum.inl (5, 2))),
  ({(Sum.inl (1, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)}, some (0, 63, Sum.inl (1, 2))),
  ({(Sum.inl (2, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)}, some (0, 1, Sum.inl (2, 2))),
  ({(Sum.inl (4, 1), false), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)}, some (4, 0, Sum.inr 1)),
  ({(Sum.inr 4, false), (Sum.inl (4, 1), false), (Sum.inl (5, 0), true)}, some (0, 107, Sum.inl (5, 1))),
  ({(Sum.inr 4, false), (Sum.inl (4, 1), false)}, some (0, 25, Sum.inl (5, 0))),
  ({(Sum.inr 4, false)}, some (15, 0, Sum.inl (4, 1))),
  ({(Sum.inr 3, true), (Sum.inr 4, true), (Sum.inr 5, true)}, none),
  ({(Sum.inr 3, true), (Sum.inr 5, true)}, some (0, 1, Sum.inr 4)),
  ({(Sum.inl (3, 2), true), (Sum.inr 5, true)}, some (0, 58, Sum.inr 3)),
  ({(Sum.inr 5, false), (Sum.inl (5, 1), false), (Sum.inl (3, 2), true)}, some (77, 119, Sum.inl (3, 1))),
  ({(Sum.inl (5, 1), false), (Sum.inl (3, 2), true)}, some (1, 0, Sum.inr 5)),
  ({(Sum.inl (5, 0), true), (Sum.inl (5, 1), true)}, some (89, 9, Sum.inr 1)),
  ({(Sum.inl (3, 2), true), (Sum.inl (5, 0), true)}, some (0, 1, Sum.inl (5, 1))),
  ({(Sum.inr 5, false), (Sum.inl (5, 0), false), (Sum.inl (3, 0), false)}, none),
  ({(Sum.inr 5, false), (Sum.inl (5, 0), false), (Sum.inl (3, 2), true)}, some (67, 0, Sum.inl (3, 0))),
  ({(Sum.inl (5, 0), false), (Sum.inl (3, 2), true)}, some (6, 0, Sum.inr 5)),
  ({(Sum.inl (3, 2), true)}, some (3, 0, Sum.inl (5, 0))),
  ({(Sum.inr 3, false), (Sum.inl (3, 0), false)}, some (75, 69, Sum.inl (4, 0))),
  ({(Sum.inl (1, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}, some (0, 83, Sum.inl (1, 2))),
  ({(Sum.inl (2, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}, some (0, 1, Sum.inl (2, 2))),
  ({(Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}, some (100, 0, Sum.inr 1)),
  ({(Sum.inr 3, false), (Sum.inl (3, 1), true)}, some (0, 5, Sum.inl (3, 0))),
  ({(Sum.inr 3, false), (Sum.inl (4, 1), false)}, some (0, 150, Sum.inl (3, 1))),
  ({(Sum.inr 3, false), (Sum.inl (3, 2), false), (Sum.inl (4, 1), true)}, some (37, 132, Sum.inl (4, 2))),
  ({(Sum.inr 3, false), (Sum.inl (4, 1), true)}, some (76, 0, Sum.inl (3, 2))),
  ({(Sum.inr 3, false)}, some (0, 2, Sum.inl (4, 1))),
  ({(Sum.inr 5, true)}, some (20, 0, Sum.inr 3)),
  ({(Sum.inl (5, 2), false), (Sum.inl (3, 2), false)}, some (0, 151, Sum.inr 5)),
  ({(Sum.inl (5, 2), false)}, some (13, 0, Sum.inl (3, 2))),
  ({(Sum.inl (5, 0), true)}, some (47, 0, Sum.inl (5, 2))),
  ({(Sum.inl (3, 0), false), (Sum.inr 5, true)}, some (24, 14, Sum.inr 3)),
  ({(Sum.inl (5, 0), false), (Sum.inl (3, 0), false)}, some (0, 19, Sum.inr 5)),
  ({(Sum.inl (5, 0), false), (Sum.inl (3, 1), true)}, some (11, 0, Sum.inl (3, 0))),
  ({(Sum.inl (3, 1), true)}, some (3, 0, Sum.inl (5, 0))),
  ({(Sum.inr 5, false), (Sum.inl (3, 1), false), (Sum.inl (5, 2), true)}, some (83, 146, Sum.inl (5, 1))),
  ({(Sum.inl (3, 1), false), (Sum.inl (5, 2), true)}, some (8, 0, Sum.inr 5)),
  ({(Sum.inl (3, 1), false)}, some (0, 7, Sum.inl (5, 2))),
  (∅, some (3, 0, Sum.inl (3, 1)))
  ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem trianglesUpper :
    ∃ π, IsRefutation trianglesFormula π ∧ ∀ C ∈ π, C.card ≤ 4 := by
  exact checkedCert trianglesAxiomsValid trianglesCertificate [] .nil (by simp) (by decide)


private abbrev V := ((Fin 6 × Fin 3) ⊕ Fin 6)

private def narrowClauses : List (Clause V) :=
  [
  {(Sum.inl (0, 0), true), (Sum.inl (0, 1), true), (Sum.inl (0, 2), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (1, 1), true), (Sum.inl (1, 2), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (2, 1), true), (Sum.inl (2, 2), true)},
  {(Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (5, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (0, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (0, 2), true), (Sum.inl (3, 1), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (3, 0), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (0, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (0, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (0, 2), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (4, 0), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (0, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (0, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (0, 2), true), (Sum.inl (5, 1), true)},
  {(Sum.inl (0, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (5, 0), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (0, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (1, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (1, 2), true), (Sum.inl (3, 1), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (3, 0), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (1, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (1, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (1, 2), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (4, 0), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (1, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (1, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (1, 2), true), (Sum.inl (5, 1), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (5, 0), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (1, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (2, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (2, 2), true), (Sum.inl (3, 1), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (3, 0), true)},
  {(Sum.inl (2, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (2, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (2, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (2, 2), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (4, 0), true)},
  {(Sum.inl (2, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (2, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (2, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (2, 2), true), (Sum.inl (5, 1), true)},
  {(Sum.inl (2, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (5, 0), true)},
  {(Sum.inl (2, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
  {(Sum.inl (2, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
  {(Sum.inr 0, false), (Sum.inl (1, 0), false), (Sum.inl (0, 0), false)},
  {(Sum.inr 0, false), (Sum.inl (1, 1), false), (Sum.inl (0, 1), false)},
  {(Sum.inr 0, false), (Sum.inl (1, 2), false), (Sum.inl (0, 2), false)},
  {(Sum.inr 1, false), (Sum.inl (2, 0), false), (Sum.inl (1, 0), false)},
  {(Sum.inr 1, false), (Sum.inl (2, 1), false), (Sum.inl (1, 1), false)},
  {(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (1, 2), false)},
  {(Sum.inr 2, false), (Sum.inl (2, 0), false), (Sum.inl (0, 0), false)},
  {(Sum.inr 2, false), (Sum.inl (2, 1), false), (Sum.inl (0, 1), false)},
  {(Sum.inr 2, false), (Sum.inl (2, 2), false), (Sum.inl (0, 2), false)},
  {(Sum.inr 3, false), (Sum.inl (4, 0), false), (Sum.inl (3, 0), false)},
  {(Sum.inr 3, false), (Sum.inl (4, 1), false), (Sum.inl (3, 1), false)},
  {(Sum.inr 3, false), (Sum.inl (4, 2), false), (Sum.inl (3, 2), false)},
  {(Sum.inr 4, false), (Sum.inl (5, 0), false), (Sum.inl (4, 0), false)},
  {(Sum.inr 4, false), (Sum.inl (5, 1), false), (Sum.inl (4, 1), false)},
  {(Sum.inr 4, false), (Sum.inl (5, 2), false), (Sum.inl (4, 2), false)},
  {(Sum.inr 5, false), (Sum.inl (5, 0), false), (Sum.inl (3, 0), false)},
  {(Sum.inr 5, false), (Sum.inl (5, 1), false), (Sum.inl (3, 1), false)},
  {(Sum.inr 5, false), (Sum.inl (5, 2), false), (Sum.inl (3, 2), false)},
  {(Sum.inr 3, true), (Sum.inr 4, true), (Sum.inr 5, true)},
  {(Sum.inr 1, true), (Sum.inr 4, true)},
  {(Sum.inr 1, true), (Sum.inr 5, true)},
  {(Sum.inr 1, true), (Sum.inr 3, true)},
  {(Sum.inr 2, true), (Sum.inr 4, true)},
  {(Sum.inr 2, true), (Sum.inr 5, true)},
  {(Sum.inr 2, true), (Sum.inr 3, true)},
  {(Sum.inr 0, true), (Sum.inr 4, true)},
  {(Sum.inr 0, true), (Sum.inr 5, true)},
  {(Sum.inr 0, true), (Sum.inr 3, true)},
  {(Sum.inr 0, true), (Sum.inr 1, true), (Sum.inr 2, true)},
  {(Sum.inl (2, 0), false), (Sum.inl (1, 0), false), (Sum.inr 4, true)},
  {(Sum.inl (2, 1), false), (Sum.inl (1, 1), false), (Sum.inr 4, true)},
  {(Sum.inl (2, 2), false), (Sum.inl (1, 2), false), (Sum.inr 4, true)},
  {(Sum.inl (5, 0), false), (Sum.inl (4, 0), false), (Sum.inr 1, true)},
  {(Sum.inl (5, 1), false), (Sum.inl (4, 1), false), (Sum.inr 1, true)},
  {(Sum.inl (5, 2), false), (Sum.inl (4, 2), false), (Sum.inr 1, true)},
  {(Sum.inl (5, 0), false), (Sum.inl (3, 0), false), (Sum.inr 1, true)},
  {(Sum.inl (5, 1), false), (Sum.inl (3, 1), false), (Sum.inr 1, true)},
  {(Sum.inl (5, 2), false), (Sum.inl (3, 2), false), (Sum.inr 1, true)},
  {(Sum.inl (2, 0), false), (Sum.inl (1, 0), false), (Sum.inr 5, true)},
  {(Sum.inl (2, 1), false), (Sum.inl (1, 1), false), (Sum.inr 5, true)},
  {(Sum.inl (2, 2), false), (Sum.inl (1, 2), false), (Sum.inr 5, true)},
  {(Sum.inl (2, 0), false), (Sum.inl (1, 0), false), (Sum.inr 3, true)},
  {(Sum.inl (2, 1), false), (Sum.inl (1, 1), false), (Sum.inr 3, true)},
  {(Sum.inl (2, 2), false), (Sum.inl (1, 2), false), (Sum.inr 3, true)},
  {(Sum.inl (4, 0), false), (Sum.inl (3, 0), false), (Sum.inr 1, true)},
  {(Sum.inl (4, 1), false), (Sum.inl (3, 1), false), (Sum.inr 1, true)},
  {(Sum.inl (4, 2), false), (Sum.inl (3, 2), false), (Sum.inr 1, true)},
  {(Sum.inl (2, 0), false), (Sum.inl (0, 0), false), (Sum.inr 4, true)},
  {(Sum.inl (2, 1), false), (Sum.inl (0, 1), false), (Sum.inr 4, true)},
  {(Sum.inl (2, 2), false), (Sum.inl (0, 2), false), (Sum.inr 4, true)},
  {(Sum.inl (5, 0), false), (Sum.inl (4, 0), false), (Sum.inr 2, true)},
  {(Sum.inl (5, 1), false), (Sum.inl (4, 1), false), (Sum.inr 2, true)},
  {(Sum.inl (5, 2), false), (Sum.inl (4, 2), false), (Sum.inr 2, true)},
  {(Sum.inl (5, 0), false), (Sum.inl (3, 0), false), (Sum.inr 2, true)},
  {(Sum.inl (5, 1), false), (Sum.inl (3, 1), false), (Sum.inr 2, true)},
  {(Sum.inl (5, 2), false), (Sum.inl (3, 2), false), (Sum.inr 2, true)},
  {(Sum.inl (2, 0), false), (Sum.inl (0, 0), false), (Sum.inr 5, true)},
  {(Sum.inl (2, 1), false), (Sum.inl (0, 1), false), (Sum.inr 5, true)},
  {(Sum.inl (2, 2), false), (Sum.inl (0, 2), false), (Sum.inr 5, true)},
  {(Sum.inl (2, 0), false), (Sum.inl (0, 0), false), (Sum.inr 3, true)},
  {(Sum.inl (2, 1), false), (Sum.inl (0, 1), false), (Sum.inr 3, true)},
  {(Sum.inl (2, 2), false), (Sum.inl (0, 2), false), (Sum.inr 3, true)},
  {(Sum.inl (4, 0), false), (Sum.inl (3, 0), false), (Sum.inr 2, true)},
  {(Sum.inl (4, 1), false), (Sum.inl (3, 1), false), (Sum.inr 2, true)},
  {(Sum.inl (4, 2), false), (Sum.inl (3, 2), false), (Sum.inr 2, true)},
  {(Sum.inl (1, 0), false), (Sum.inl (0, 0), false), (Sum.inr 4, true)},
  {(Sum.inl (1, 1), false), (Sum.inl (0, 1), false), (Sum.inr 4, true)},
  {(Sum.inl (1, 2), false), (Sum.inl (0, 2), false), (Sum.inr 4, true)},
  {(Sum.inl (5, 0), false), (Sum.inl (4, 0), false), (Sum.inr 0, true)},
  {(Sum.inl (5, 1), false), (Sum.inl (4, 1), false), (Sum.inr 0, true)},
  {(Sum.inl (5, 2), false), (Sum.inl (4, 2), false), (Sum.inr 0, true)},
  {(Sum.inl (5, 0), false), (Sum.inl (3, 0), false), (Sum.inr 0, true)},
  {(Sum.inl (5, 1), false), (Sum.inl (3, 1), false), (Sum.inr 0, true)},
  {(Sum.inl (5, 2), false), (Sum.inl (3, 2), false), (Sum.inr 0, true)},
  {(Sum.inl (1, 0), false), (Sum.inl (0, 0), false), (Sum.inr 5, true)},
  {(Sum.inl (1, 1), false), (Sum.inl (0, 1), false), (Sum.inr 5, true)},
  {(Sum.inl (1, 2), false), (Sum.inl (0, 2), false), (Sum.inr 5, true)},
  {(Sum.inl (1, 0), false), (Sum.inl (0, 0), false), (Sum.inr 3, true)},
  {(Sum.inl (1, 1), false), (Sum.inl (0, 1), false), (Sum.inr 3, true)},
  {(Sum.inl (1, 2), false), (Sum.inl (0, 2), false), (Sum.inr 3, true)},
  {(Sum.inl (4, 0), false), (Sum.inl (3, 0), false), (Sum.inr 0, true)},
  {(Sum.inl (4, 1), false), (Sum.inl (3, 1), false), (Sum.inr 0, true)},
  {(Sum.inl (4, 2), false), (Sum.inl (3, 2), false), (Sum.inr 0, true)}
  ]
private def closureOK (S : List (Clause V)) (v : V) : Bool :=
  (S.filter fun A => decide ((v, true) ∈ A)).all fun A =>
    (S.filter fun B => decide ((v, false) ∈ B)).all fun B =>
      let R := A.erase (v, true) ∪ B.erase (v, false)
      decide (3 < R.card ∨ R ∈ S)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem checkedClosure (v : V) : closureOK narrowClauses v = true := by
  rcases v with ⟨u, t⟩ | e
  · fin_cases u <;> fin_cases t <;> decide
  · fin_cases e <;> decide

private theorem resolventMem {A B R : Clause V}
    (hA : A ∈ narrowClauses) (hB : B ∈ narrowClauses)
    (hR : IsResolvent A B R) (wR : R.card ≤ 3) : R ∈ narrowClauses := by
  obtain ⟨v, hvA, hvB, rfl⟩ := hR
  have ok := checkedClosure v
  unfold closureOK at ok
  have row := List.all_eq_true.mp ok A (List.mem_filter.mpr ⟨hA, by simpa using hvA⟩)
  have test := List.all_eq_true.mp row B (List.mem_filter.mpr ⟨hB, by simpa using hvB⟩)
  exact (of_decide_eq_true test).resolve_left (Nat.not_lt.mpr wR)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 7000000 in
private theorem axiomsMem (C : Clause V) (h : C ∈ trianglesFormula) : C ∈ narrowClauses := by
  rcases h with ((⟨u, rfl⟩ | ⟨u, v, f, hne, hcross, rfl⟩) | ⟨e, t, rfl⟩) | ⟨S, hs, rfl⟩
  · have hAll : ∀ u : Fin 6, Finset.univ.image (fun t : Fin 3 =>
        ((Sum.inl (u, t) : V), true)) ∈ narrowClauses := by decide
    exact hAll u
  · have hAll : ∀ (u v : Fin 6) (x y z : Fin 2),
        u ≠ v → ¬ (u ≠ v ∧ u.val / 3 = v.val / 3) →
        Finset.univ.image (fun t : Fin 3 =>
          ((Sum.inl (if (![decide (x = 1), decide (y = 1), decide (z = 1)] : Fin 3 → Bool) t = true then v else u, t) : V), true))
          ∈ narrowClauses := by
      intro a b x y z hne' hcross'
      fin_cases a <;> fin_cases b
      all_goals first
      | exact False.elim (hne' (by decide))
      | exact False.elim (hcross' (by decide))
      | fin_cases x <;> fin_cases y <;> fin_cases z <;> decide
    have hf : f = ![f 0, f 1, f 2] := by
      funext t
      fin_cases t <;> rfl
    rw [hf]
    let digit (b : Bool) : Fin 2 := if b then 1 else 0
    have digitSpec (b : Bool) : decide (digit b = 1) = b := by cases b <;> decide
    simpa only [digitSpec] using hAll u v (digit (f 0)) (digit (f 1)) (digit (f 2)) hne hcross
  · have hAll : ∀ (e : Fin 6) (t : Fin 3), ({(Sum.inr e, false),
        (Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] :
          Fin 6 → Fin 6 × Fin 6) e).1, t), false),
        (Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] :
          Fin 6 → Fin 6 × Fin 6) e).2, t), false)} : Clause V) ∈ narrowClauses := by decide
    exact hAll e t
  · have hAll : ∀ S : Finset (Fin 6), S.card = 2 →
        (Finset.univ.filter (fun e : Fin 6 =>
          ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e).1 ∉ S ∧
          ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e).2 ∉ S)).image
            (fun e => ((Sum.inr e : V), true)) ∈ narrowClauses := by decide
    exact hAll S hs

private theorem boundedDerivationMem {π : List (Clause V)} (h : IsDerivation trianglesFormula π)
    (hw : ∀ D ∈ π, D.card ≤ 3) : ∀ C ∈ π, C ∈ narrowClauses := by
  induction h with
  | nil => simp
  | @ax π C d hC ih =>
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact axiomsMem D hC
    · exact ih (fun A hA => hw A (List.mem_cons_of_mem _ hA)) D hD
  | @res π A B R d ha hb hr ih =>
    intro D hD
    have prev := ih (fun C hC => hw C (List.mem_cons_of_mem _ hC))
    rcases List.mem_cons.mp hD with rfl | hD
    · exact resolventMem (prev A ha) (prev B hb) hr (hw D (List.mem_cons_self ..))
    · exact prev D hD

private theorem trianglesLower :
    ¬ ∃ π, IsRefutation trianglesFormula π ∧ ∀ D ∈ π, D.card ≤ 3 := by
  rintro ⟨π, ⟨hd, hempty⟩, hw⟩
  exact (by decide : (∅ : Clause V) ∉ narrowClauses) (boundedDerivationMem hd hw ∅ hempty)

end PEqualNP.Outside.L_pcx_095_aux

open PEqualNP.Outside.L_pcx_095_aux in
theorem PEqualNP.Outside.L_pcx_095 :
    (∀ F1 : Set (PEqualNP.ProofComplexity.Clause ((Fin 6 × Fin 3) ⊕ Fin 6)), F1 = {C6 | ∃ v7 : Fin 6, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C9 | ∃ (u10 v11 : Fin 6) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (u10 ≠ v11 ∧ u10.val / 3 = v11.val / 3) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C14 | ∃ (e15 : Fin 6) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).1, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).2, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 6), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).1 ∉ S18 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).2 ∉ S18)).image (fun e20 : Fin 6 => ((Sum.inr e20 : (Fin 6 × Fin 3) ⊕ Fin 6), true))} → (∃ π2, PEqualNP.ProofComplexity.IsRefutation F1 π2 ∧ ∀ D3 ∈ π2, D3.card ≤ 4) ∧ ¬ ∃ π4, PEqualNP.ProofComplexity.IsRefutation F1 π4 ∧ ∀ D5 ∈ π4, D5.card ≤ 3) := by
  intro F h
  subst F
  exact ⟨trianglesUpper, trianglesLower⟩
