import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_901

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

def bicliqueCircuit {n k : ℕ} (X Y : Fin k → Finset (Fin n)) : AndCountCircuit n where
  size := k
  leftVars := X
  leftGates _ := ∅
  rightVars := Y
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

lemma side_bare {n k : ℕ} (U B : Finset (Fin n)) (i : Fin k) (val : Fin k → Bool) :
    sideTrue U B ∅ i val = decide (∃ v ∈ B, v ∈ U) := by
  simp only [sideTrue]
  congr 1
  apply propext
  constructor
  · intro h
    rcases h with h | ⟨j, hj, _⟩
    · exact h
    · exact (Finset.notMem_empty j hj).elim
  · exact Or.inl

lemma fuel_pos {n k : ℕ} (X Y : Fin k → Finset (Fin n)) {d : ℕ} (hd : 0 < d)
    (U : Finset (Fin n)) (i : Fin k) :
    (bicliqueCircuit X Y).gateValFuel U d i =
      (decide (∃ v ∈ X i, v ∈ U) && decide (∃ w ∈ Y i, w ∈ U)) := by
  cases d with
  | zero => exact (Nat.not_lt_zero 0 hd).elim
  | succ _ =>
    simp only [gateValFuel]
    rw [show (bicliqueCircuit X Y).leftVars i = X i from rfl]
    rw [show (bicliqueCircuit X Y).leftGates i = (∅ : Finset (Fin k)) from rfl]
    rw [show (bicliqueCircuit X Y).rightVars i = Y i from rfl]
    rw [show (bicliqueCircuit X Y).rightGates i = (∅ : Finset (Fin k)) from rfl]
    rw (config := { transparency := .default }) [side_bare, side_bare]

lemma gate_iff {n k : ℕ} (X Y : Fin k → Finset (Fin n)) (U : Finset (Fin n)) (i : Fin k) :
    (bicliqueCircuit X Y).gateVal U i = true ↔
      (∃ v ∈ X i, v ∈ U) ∧ (∃ w ∈ Y i, w ∈ U) := by
  simp only [gateVal]
  have hk : 0 < (bicliqueCircuit X Y).size := by
    simpa [bicliqueCircuit] using Nat.zero_lt_of_lt i.isLt
  rw [fuel_pos X Y hk U i]
  simp [Bool.and_eq_true, decide_eq_true_eq]

lemma eval_iff {n k : ℕ} (X Y : Fin k → Finset (Fin n)) (U : Finset (Fin n)) :
    (bicliqueCircuit X Y).eval U = true ↔
      ∃ i : Fin k, (∃ v ∈ X i, v ∈ U) ∧ (∃ w ∈ Y i, w ∈ U) := by
  unfold eval
  rw [decide_eq_true_iff]
  simp only [bicliqueCircuit]
  constructor
  · intro h
    rcases h with ⟨v, hv, _⟩ | ⟨j, _, hj⟩
    · exact (Finset.notMem_empty v hv).elim
    · exact ⟨j, (gate_iff X Y U j).mp hj⟩
  · intro ⟨i, hi⟩
    exact Or.inr ⟨i, Finset.mem_univ _, (gate_iff X Y U i).mpr hi⟩

lemma computes {n k : ℕ} (G : SimpleGraph (Fin n)) (X Y : Fin k → Finset (Fin n))
    (hbic : ∀ i : Fin k, ∀ x ∈ X i, ∀ y ∈ Y i, G.Adj x y)
    (hcov : ∀ a b : Fin n, G.Adj a b →
      ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (a ∈ Y i ∧ b ∈ X i)) :
    (bicliqueCircuit X Y).Computes G := by
  intro U
  rw [eval_iff]
  constructor
  · rintro ⟨i, ⟨x, hxX, hxU⟩, ⟨y, hyY, hyU⟩⟩
    exact ⟨x, hxU, y, hyU, hbic i x hxX y hyY⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨i, hi⟩ := hcov a b hab
    rcases hi with ⟨haX, hbY⟩ | ⟨haY, hbX⟩
    · exact ⟨i, ⟨a, haX, ha⟩, ⟨b, hbY, hb⟩⟩
    · exact ⟨i, ⟨b, hbX, hb⟩, ⟨a, haY, ha⟩⟩

lemma well_formed {n k : ℕ} (X Y : Fin k → Finset (Fin n)) :
    (bicliqueCircuit X Y).WellFormed := by
  intro i
  constructor
  · intro j hj
    exact (Finset.notMem_empty j hj).elim
  · intro j hj
    exact (Finset.notMem_empty j hj).elim

end PEqualNP.Outside.L_meta_901

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem PEqualNP.Outside.L_meta_901 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (X Y : Fin k → Finset (Fin n)),
    (∀ i : Fin k, ∀ x ∈ X i, ∀ y ∈ Y i, G.Adj x y) →
    (∀ a b : Fin n, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (a ∈ Y i ∧ b ∈ X i)) →
    ∃ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed ∧ C.size ≤ k ∧
      ∀ I : Finset (Fin n),
        ((∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) ∧ (∀ u : Fin n, u ∉ I → ∃ a ∈ I, G.Adj u a)) →
        C.eval I = false ∧ ∀ u : Fin n, u ∉ I → C.eval (insert u I) = true := by
  intro n G k X Y hbic hcov
  refine ⟨PEqualNP.Outside.L_meta_901.bicliqueCircuit X Y,
    PEqualNP.Outside.L_meta_901.well_formed X Y, le_rfl, ?_⟩
  intro I ⟨hind, hmax⟩
  have hC := PEqualNP.Outside.L_meta_901.computes G X Y hbic hcov
  constructor
  · apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨a, ha, b, hb, hab⟩ := (hC I).mp ht
    exact hind a ha b hb hab
  · intro u hu
    obtain ⟨a, ha, hau⟩ := hmax u hu
    exact (hC (insert u I)).mpr ⟨u, Finset.mem_insert_self u I, a, Finset.mem_insert_of_mem ha, hau⟩
