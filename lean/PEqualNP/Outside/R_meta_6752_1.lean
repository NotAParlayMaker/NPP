import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_6752_1
    (fiberCharge :
      let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
        (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10),
        (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        2 ≤ (junk G C).card →
        let J := junk G C
        let U := Ustar G C
        ∀ X ⊆ U, X.Nonempty →
          (∀ h ∈ J, (X ∩ gammaE G C h).card ≠ 1) →
          (∀ e ∈ X, ∃ h ∈ J, e ∈ gammaE G C h) →
          X.card ≤ 2 * (centreless G C).card +
            (J.filter (fun h => (X ∩ gammaE G C h).Nonempty)).card +
              (orN G C \ lam G C).card)
    (partitionCount : ∀ {α : Type} [DecidableEq α] (S : Finset α)
      (P : α → Prop) [DecidablePred P],
      (S.filter P).card + (S.filter (fun a => ¬ P a)).card = S.card) :
    let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
      (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10),
      (7, 9), (8, 9)]
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
      let J := junk G C
      let U := Ustar G C
      2 ≤ J.card →
      ∀ X ⊆ U, X.Nonempty →
        (U \ X).card ≤ {h ∈ J | Disjoint X (gammaE G C h)}.card →
        (∀ h ∈ J, (X ∩ gammaE G C h).card ≠ 1) →
        (∀ e ∈ U, ∃ h ∈ J, e ∈ gammaE G C h) →
        X.card ≤ 2 * (centreless G C).card +
          (J.card - (U \ X).card) + (orN G C \ lam G C).card := by
  intro G C hsize hleast htop
  dsimp only
  intro hJ X hX hXne hDisj hNoSingleton hCover
  let P : ℕ → Prop := fun h => (X ∩ gammaE G C h).Nonempty
  have hCharge := fiberCharge C hsize hleast htop hJ X hX hXne hNoSingleton (by
    intro e he
    exact hCover e (hX he))
  have hPartition := partitionCount (junk G C) P
  have hInactive :
      (junk G C).filter (fun h => ¬ P h) =
        {h ∈ junk G C | Disjoint X (gammaE G C h)} := by
    ext h
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hh, hn⟩
      refine ⟨hh, ?_⟩
      rw [Finset.disjoint_left]
      intro e heX heGamma
      exact hn ⟨e, Finset.mem_inter.mpr ⟨heX, heGamma⟩⟩
    · rintro ⟨hh, hd⟩
      refine ⟨hh, ?_⟩
      intro hne
      obtain ⟨e, he⟩ := hne
      exact (Finset.disjoint_left.mp hd)
        (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp he).2
  rw [hInactive] at hPartition
  have hActive :
      ((junk G C).filter P).card ≤
        (junk G C).card - (Ustar G C \ X).card := by
    change ((junk G C).filter P).card +
        {h ∈ junk G C | Disjoint X (gammaE G C h)}.card = (junk G C).card at hPartition
    omega
  change X.card ≤ 2 * (centreless G C).card +
    ((junk G C).filter P).card + (orN G C \ lam G C).card at hCharge
  omega
