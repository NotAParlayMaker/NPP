import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset

-- Each selected line meets an outside line in at most one point.
theorem PEqualNP.Outside.L_meta_3495 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ (x9 x10 : Fin x2 → Prop), (∀ (x11 x12 : Fin x2), x3 x11 x12 → x9 x11 ∨ x10 x12) → (∀ (x12 : Fin x2), x9 x12 → ∃ x14 ∈ x7, x3 x12 x14) → (∀ x13 ∈ x7, ¬x10 x13) → (∀ (x14 : Fin x2), x9 x14 ↔ ∃ x15 ∈ x7, x3 x14 x15) ∧ ∀ (x14 : Fin x2), x10 x14 ↔ x14 ∉ x7 := by
  intro q N Inc _ degree joins S sparse A B covers points lines
  classical
  have outsidePoint (l : Fin N) (outside : l ∉ S) :
      ∃ p, Inc p l ∧ ¬ ∃ s ∈ S, Inc p s := by
    by_contra missing
    have chosen (p : {p : Fin N // Inc p l}) : ∃ s ∈ S, Inc p.val s := by
      by_contra notCovered
      exact missing ⟨p.val, p.property, notCovered⟩
    let pick (p : {p : Fin N // Inc p l}) : {s : Fin N // s ∈ S} :=
      ⟨Classical.choose (chosen p), (Classical.choose_spec (chosen p)).1⟩
    have hit (p : {p : Fin N // Inc p l}) : Inc p.val (pick p).val :=
      (Classical.choose_spec (chosen p)).2
    have injective : Function.Injective pick := by
      intro p r same
      apply Subtype.ext
      by_contra distinct
      obtain ⟨t, _, unique⟩ := joins p.val r.val distinct
      have hr := hit r
      have sameLine : (pick p).val = (pick r).val := congrArg Subtype.val same
      rw [← sameLine] at hr
      have hl := unique l ⟨p.property, r.property⟩
      have hs := unique (pick p).val ⟨hit p, hr⟩
      apply outside
      rw [hl.trans hs.symm]
      exact (pick p).property
    have count := Fintype.card_le_of_injective pick injective
    rw [degree l, Fintype.card_coe] at count
    omega
  constructor
  · intro p
    refine ⟨points p, ?_⟩
    rintro ⟨l, member, incident⟩
    exact (covers p l incident).resolve_right (lines l member)
  · intro l
    refine ⟨fun yes member => lines l member yes, ?_⟩
    intro outside
    obtain ⟨p, incident, notCovered⟩ := outsidePoint l outside
    exact (covers p l incident).resolve_left (fun hp => notCovered (points p hp))
