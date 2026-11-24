import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  classical
  intro n G _ hcycle U hU x Y hY R π hblocks hcover
  have markedAdj (v : Fin n) (hv : v ∈ Y) : G.Adj x v :=
    G.mem_edgeSet.mp (hU _ (hY v hv))
  -- A block containing a marked neighbor cannot contain a different neighbor of x.
  have eqInBlock {B : Finset (Fin n)} (hB : B ∈ π) {u v : Fin n}
      (hu : u ∈ B) (hv : v ∈ B) (huY : u ∈ Y) (hvx : G.Adj x v) : u = v := by
    rcases (hblocks B hB).2 with hcard | ⟨_, c, hAdj, hOff⟩
    · exact Finset.card_le_one.mp (by rw [hcard]) u hu v hv
    · have hxc : x ≠ c := by
        intro h
        subst c
        exact hOff u hu (hY u huY)
      exact Finset.card_le_one.mp (hcycle x c hxc) u
        (by simp [markedAdj u huY, hAdj u hu]) v (by simp [hvx, hAdj v hv])
  let pick (r : Fin n) : Finset (Fin n) :=
    if hr : r ∈ R then (hcover r hr).choose else ∅
  have pickBlock (r : Fin n) (hr : r ∈ R) : pick r ∈ π ∧ r ∈ pick r := by
    simpa [pick, hr] using (hcover r hr).choose_spec
  have inject : Set.InjOn pick (↑(R ∩ Y) : Set (Fin n)) := by
    intro u hu v hv heq
    obtain ⟨huR, huY⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvR, hvY⟩ := Finset.mem_inter.mp hv
    apply eqInBlock (pickBlock u huR).1 (pickBlock u huR).2 _ huY (markedAdj v hvY)
    rw [heq]
    exact (pickBlock v hvR).2
  refine ⟨Finset.card_le_card_of_injOn pick ?_ inject, ?_⟩
  · intro v hv
    exact (pickBlock v (Finset.mem_inter.mp hv).1).1
  · intro hR hnot
    obtain ⟨r, hrR, hrY⟩ := Finset.not_subset.mp hnot
    have hbound : (R ∩ Y).card ≤ (π.erase (pick r)).card := by
      apply Finset.card_le_card_of_injOn pick _ inject
      intro v hv
      obtain ⟨hvR, hvY⟩ := Finset.mem_inter.mp hv
      refine Finset.mem_erase.mpr ⟨?_, (pickBlock v hvR).1⟩
      intro heq
      have hrB : r ∈ pick v := by
        rw [heq]
        exact (pickBlock r hrR).2
      have hvr := eqInBlock (pickBlock v hvR).1 (pickBlock v hvR).2 hrB hvY (hR r hrR)
      exact hrY (hvr ▸ hvY)
    rw [Finset.card_erase_of_mem (pickBlock r hrR).1] at hbound
    have hpos := Finset.card_pos.mpr ⟨pick r, (pickBlock r hrR).1⟩
    omega
