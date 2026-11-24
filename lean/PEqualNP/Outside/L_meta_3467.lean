import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3467

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_prefix (gs : List Gate) (w : List Bool) (j : ℕ) (h : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step]
    exact List.getD_append _ _ _ _ h

lemma eval_low (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  unfold Circuit.eval
  exact fold_prefix C.gates x C.output h

lemma getD_left {N : ℕ} (X Y : Finset (Fin N)) (i : ℕ) (hi : i < N) :
    (incidenceInput X Y).getD i false = decide ((⟨i, hi⟩ : Fin N) ∈ X) := by
  unfold incidenceInput
  rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_ofFn]

lemma getD_right {N : ℕ} (X Y : Finset (Fin N)) (i : ℕ) (hi : N ≤ i) (hi2 : i - N < N) :
    (incidenceInput X Y).getD i false = decide ((⟨i - N, hi2⟩ : Fin N) ∈ Y) := by
  unfold incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simpa using hi2), List.getElem_ofFn]

theorem main (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit) (hq : 200 ≤ q)
    (hN : N = q ^ 2 + q + 1) (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (hout : C.output < N + N) (hright : RightOnIncidentPairs S C) : False := by
  have hlen : ∀ X Y : Finset (Fin N), (incidenceInput X Y).length = N + N := by
    intro X Y; simp [incidenceInput]
  have key : ∀ l : Fin N, ∀ p ∈ S l,
      (incidenceInput {p} {l}).getD C.output false = true := by
    intro l p hp
    rw [← eval_low C _ (by rw [hlen]; exact hout)]
    exact hright l p hp
  have hN2 : 2 ≤ N := by subst hN; nlinarith
  by_cases ho : C.output < N
  · set o : Fin N := ⟨C.output, ho⟩
    have h2 : 1 < (S ⟨0, by omega⟩).card := by rw [hcard]; omega
    obtain ⟨p, hp, hpo⟩ := Finset.exists_mem_ne h2 o
    have := key ⟨0, by omega⟩ p hp
    rw [getD_left _ _ _ ho] at this
    simp only [Finset.mem_singleton, decide_eq_true_eq] at this
    exact hpo this.symm
  · push_neg at ho
    have hlt : C.output - N < N := by omega
    set l0 : Fin N := ⟨C.output - N, hlt⟩
    set l : Fin N := if C.output - N = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩ with hl
    have hne : l0 ≠ l := by
      intro h
      have hv := congrArg Fin.val h
      simp only [l0, hl] at hv
      split_ifs at hv with h0 <;> simp_all
    have hpos : 0 < (S l).card := by rw [hcard]; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.1 hpos
    have := key l p hp
    rw [getD_right _ _ _ ho hlt] at this
    simp only [Finset.mem_singleton, decide_eq_true_eq] at this
    exact hne this

end PEqualNP.Outside.L_meta_3467

theorem PEqualNP.Outside.L_meta_3467 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N S C hq hN hcard _ _ hout hright _
  exact (PEqualNP.Outside.L_meta_3467.main q N S C hq hN hcard hout hright).elim
