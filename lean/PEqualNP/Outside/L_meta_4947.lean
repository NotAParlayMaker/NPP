import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4947

def nums : List ℕ :=
  [7, 13, 19, 21, 25, 29, 35, 37, 39, 41, 67, 69, 71, 73, 77, 81, 83, 85,
   97, 101, 105, 131, 133, 135, 137, 141, 195, 201, 265, 273, 275, 281, 297, 329, 337, 549]

def incB (a b : Fin 13) : Bool :=
  decide (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9)

def missB (x1 : ℕ) (x2 w : Fin 13) : Bool :=
  (List.finRange 13).all fun p => !(x1.testBit (p - x2).val) || !(incB p w)

def checkPair (x1 : ℕ) (x2 : Fin 13) : Bool :=
  ((List.finRange 13).all fun v =>
    x1.testBit (v - x2).val || (List.finRange 13).any fun w => missB x1 x2 w && incB v w) &&
  !((List.finRange 13).any fun w =>
    (List.finRange 13).all fun p => !(x1.testBit (p - x2).val) || incB p w) &&
  !((List.finRange 13).any fun p =>
    (List.finRange 13).all fun w => !(missB x1 x2 w) || incB p w)

theorem all_ok : (nums.all fun x1 => (List.finRange 13).all fun x2 => checkPair x1 x2) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_4947

open PEqualNP.Outside.L_meta_4947 in
theorem PEqualNP.Outside.L_meta_4947 : ∀ (x1 : ℕ) (x2 : Fin (13 : ℕ)),   (x1 ∈       have x3 : List ℕ :=         have x3 : List ℕ :=           have x3 : List ℕ := [(281 : ℕ), (297 : ℕ), (329 : ℕ), (337 : ℕ), (549 : ℕ)];           (201 : ℕ) :: (265 : ℕ) :: (273 : ℕ) :: (275 : ℕ) :: x3;         have x4 : List ℕ := (133 : ℕ) :: (135 : ℕ) :: (137 : ℕ) :: (141 : ℕ) :: (195 : ℕ) :: x3;         (97 : ℕ) :: (101 : ℕ) :: (105 : ℕ) :: (131 : ℕ) :: x4;       have x4 : List ℕ :=         have x4 : List ℕ := (73 : ℕ) :: (77 : ℕ) :: (81 : ℕ) :: (83 : ℕ) :: (85 : ℕ) :: x3;         (41 : ℕ) :: (67 : ℕ) :: (69 : ℕ) :: (71 : ℕ) :: x4;       have x5 : List ℕ := (25 : ℕ) :: (29 : ℕ) :: (35 : ℕ) :: (37 : ℕ) :: (39 : ℕ) :: x4;       (7 : ℕ) :: (13 : ℕ) :: (19 : ℕ) :: (21 : ℕ) :: x5) →     have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | x1.testBit ↑(x4 - x2) = Bool.true};     have x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ));     have x6 : Fin (13 : ℕ) → Prop := fun (x6 : Fin (13 : ℕ)) => ∀ x7 ∈ x4, ¬x5 x7 x6;     (∀ x7 ∉ x4, ∃ (x9 : Fin (13 : ℕ)), x6 x9 ∧ x5 x7 x9) ∧ (¬∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x4, x5 x8 x7) ∧ ¬∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x6 x8 → x5 x7 x8 := by
  dsimp only
  intro x1 x2 hx1
  have hmem : x1 ∈ nums := hx1
  have h1 := List.all_eq_true.mp all_ok x1 hmem
  have h2 := List.all_eq_true.mp h1 x2 (List.mem_finRange x2)
  unfold checkPair at h2
  rcases Bool.and_eq_true_iff.mp h2 with ⟨h12, h3⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hc1, hc2⟩
  have hmiss (w : Fin 13) :
      missB x1 x2 w = true ↔
        ∀ p ∈ ({x4 : Fin 13 | x1.testBit ↑(x4 - x2) = true} : Finset (Fin 13)),
          ¬(p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) := by
    unfold missB incB
    rw [List.all_eq_true]
    constructor
    · intro h p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hb := h p (List.mem_finRange p)
      rw [hp'] at hb
      simpa using hb
    · intro h p _
      by_cases hp : x1.testBit (p - x2).val = true
      · have hnot := h p (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)
        simp [hp, hnot]
      · simp [hp]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hv' : x1.testBit (v - x2).val = false := by
      cases hb : x1.testBit (v - x2).val
      · rfl
      · exact False.elim (hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hb⟩))
    have hall := List.all_eq_true.mp hc1 v (List.mem_finRange v)
    rw [hv', Bool.false_or] at hall
    rcases List.any_eq_true.mp hall with ⟨w, _, hw⟩
    rcases Bool.and_eq_true_iff.mp hw with ⟨hm, hi⟩
    exact ⟨w, (hmiss w).mp hm, of_decide_eq_true hi⟩
  · rintro ⟨w, hw⟩
    have hany : ((List.finRange 13).any fun w =>
        (List.finRange 13).all fun p => !(x1.testBit (p - x2).val) || incB p w) = true := by
      refine List.any_eq_true.mpr ⟨w, List.mem_finRange w, List.all_eq_true.mpr ?_⟩
      intro p _
      by_cases hp : x1.testBit (p - x2).val = true
      · have hi : incB p w = true := decide_eq_true (hw p (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩))
        simp [hp, hi]
      · simp [hp]
    rw [hany] at hc2
    cases hc2
  · rintro ⟨p, hp⟩
    have hany : ((List.finRange 13).any fun p =>
        (List.finRange 13).all fun w => !(missB x1 x2 w) || incB p w) = true := by
      refine List.any_eq_true.mpr ⟨p, List.mem_finRange p, List.all_eq_true.mpr ?_⟩
      intro w _
      by_cases hm : missB x1 x2 w = true
      · have hi : incB p w = true := decide_eq_true (hp w ((hmiss w).mp hm))
        simp [hm, hi]
      · simp [hm]
    rw [hany] at h3
    cases h3
