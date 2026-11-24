import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2099_aux

private abbrev offsets : Finset (Fin 13) := {0, 1, 3, 9}

private abbrev inc (p l : Fin 13) : Prop := ∃ d ∈ offsets, p = l + d

private def pick (j : Fin 17) : Fin 26 :=
  Fin.ofNat 26 (if j.val < 5 then j.val else if j.val < 14 then j.val + 8 else j.val + 9)

private def masks : List ℕ :=
  [31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455, 8718, 9229,
    10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590, 29446, 33821,
    34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324, 58892, 63268,
    67610, 81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040]

private def avoidLines (A : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => ∀ p ∈ A, ¬ inc p l)

private def avoidPoints (B : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => ∀ l ∈ B, ¬ inc p l)

private abbrev selected (A B : Finset (Fin 13)) (j : Fin 17) : Prop :=
  (∃ p ∈ A, pick j = Fin.castAdd 13 p) ∨ ∃ l ∈ B, pick j = Fin.natAdd 13 l

private def required (A B : Finset (Fin 13)) : List (Fin 17) :=
  (List.finRange 17).filter (fun j => decide (selected A B j))

private def covers (A B : Finset (Fin 13)) : Bool :=
  masks.any (fun k => (required A B).all (fun j => k.testBit j.val))

private def pointCases : Finset (Finset (Fin 13)) :=
  Finset.univ.biUnion (fun l => (Finset.univ.filter (fun p => inc p l)).powerset)

private def lineCases : Finset (Finset (Fin 13)) :=
  Finset.univ.biUnion (fun p => (Finset.univ.filter (fun l => inc p l)).powerset)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem pointCheck :
    (pointCases.filter (fun A => covers A (avoidLines A) = false)).card = 0 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem lineCheck :
    (lineCases.filter (fun B => covers (avoidPoints B) B = false)).card = 0 := by
  decide +kernel

private theorem ofCheck {α : Type*} (cs : Finset α) (test : α → Bool) (s : α)
    (h : s ∈ cs) (hc : (cs.filter (fun a => test a = false)).card = 0) :
    test s = true := by
  cases ht : test s with
  | true => rfl
  | false =>
    have hm : s ∈ cs.filter (fun a => test a = false) := Finset.mem_filter.mpr ⟨h, ht⟩
    have hp : 0 < (cs.filter (fun a => test a = false)).card :=
      Finset.card_pos.mpr ⟨s, hm⟩
    omega

private theorem closed (A : Finset (Fin 13))
    (h : ∀ p ∉ A, ∃ l ∈ avoidLines A, inc p l) :
    avoidPoints (avoidLines A) = A := by
  ext p
  simp only [avoidPoints, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hp
    by_contra ha
    obtain ⟨l, hl, hi⟩ := h p ha
    exact hp l hl hi
  · intro hp l hl
    exact (Finset.mem_filter.mp hl).2 p hp

private theorem result (A : Finset (Fin 13))
    (h : ∀ p ∉ A, ∃ l ∈ avoidLines A, inc p l)
    (hsmall : (∃ l, ∀ p ∈ A, inc p l) ∨ ∃ p, ∀ l ∈ avoidLines A, inc p l) :
    ∃ k ∈ masks, ∀ j : Fin 17, selected A (avoidLines A) j → k.testBit j.val = true := by
  have hc : covers A (avoidLines A) = true := by
    rcases hsmall with ⟨l, hl⟩ | ⟨p, hp⟩
    · have hm : A ∈ pointCases := by
        refine Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Finset.mem_powerset.mpr ?_⟩
        exact fun p hm => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl p hm⟩
      exact ofCheck pointCases (fun S => covers S (avoidLines S)) A hm pointCheck
    · have hm : avoidLines A ∈ lineCases := by
        refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, Finset.mem_powerset.mpr ?_⟩
        exact fun l hm => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp l hm⟩
      have ht := ofCheck lineCases (fun T => covers (avoidPoints T) T) (avoidLines A) hm lineCheck
      rwa [closed A h] at ht
  obtain ⟨k, hk, ht⟩ := List.any_eq_true.mp hc
  refine ⟨k, hk, fun j hj => List.all_eq_true.mp ht j ?_⟩
  exact List.mem_filter.mpr ⟨by simp, decide_eq_true hj⟩

end PEqualNP.Outside.L_meta_2099_aux

theorem PEqualNP.Outside.L_meta_2099 :
    ∀ (x1 : Finset (Fin (13 : ℕ))),   have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};   have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => ∃ x5 ∈ x2, x3 = x4 + x5;   have x4 : Fin (13 : ℕ) → Prop := fun (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x1, ¬x3 x5 x4;   have x5 : Fin (17 : ℕ) → Fin (26 : ℕ) := fun (x5 : Fin (17 : ℕ)) => Fin.ofNat (26 : ℕ) (if ↑x5 < (5 : ℕ) then ↑x5 else if ↑x5 < (14 : ℕ) then ↑x5 + (8 : ℕ) else ↑x5 + (9 : ℕ));   (∀ x6 ∉ x1, ∃ (x8 : Fin (13 : ℕ)), x4 x8 ∧ x3 x6 x8) →     ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x1, x3 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x4 x8 → x3 x7 x8) →       ∃         x8 ∈           have x9 : List ℕ :=             have x9 : List ℕ :=               have x9 : List ℕ := [(92682 : ℕ), (97154 : ℕ), (117784 : ℕ), (122032 : ℕ), (126536 : ℕ), (131040 : ℕ)];               (58892 : ℕ) :: (63268 : ℕ) :: (67610 : ℕ) :: (81946 : ℕ) :: (88210 : ℕ) :: x9;             have x10 : List ℕ := (40973 : ℕ) :: (44105 : ℕ) :: (46341 : ℕ) :: (48577 : ℕ) :: (49180 : ℕ) :: (54324 : ℕ) :: x9;             (29446 : ℕ) :: (33821 : ℕ) :: (34841 : ℕ) :: (36885 : ℕ) :: (40081 : ℕ) :: x10;           have x10 : List ℕ :=             have x10 : List ℕ := (16414 : ℕ) :: (16910 : ℕ) :: (17436 : ℕ) :: (18458 : ℕ) :: (20502 : ℕ) :: (24590 : ℕ) :: x9;             (8718 : ℕ) :: (9229 : ℕ) :: (10251 : ℕ) :: (12295 : ℕ) :: (14723 : ℕ) :: x10;           have x11 : List ℕ := (4243 : ℕ) :: (4359 : ℕ) :: (5141 : ℕ) :: (6163 : ℕ) :: (8207 : ℕ) :: (8455 : ℕ) :: x10;           (31 : ℕ) :: (2075 : ℕ) :: (2195 : ℕ) :: (3097 : ℕ) :: (4119 : ℕ) :: x11,         ∀ (x9 : Fin (17 : ℕ)), ((∃ x10 ∈ x1, x5 x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ (x10 : Fin (13 : ℕ)), x5 x9 = Fin.natAdd (13 : ℕ) x10 ∧ x4 x10) → x8.testBit ↑x9 = Bool.true := by
  intro A offsets inc avoid pick hm hs
  have hm' : ∀ p ∉ A, ∃ l ∈ L_meta_2099_aux.avoidLines A, L_meta_2099_aux.inc p l := by
    intro p hp
    obtain ⟨l, hl, hi⟩ := hm p hp
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, hi⟩
  have hs' : (∃ l, ∀ p ∈ A, L_meta_2099_aux.inc p l) ∨
      ∃ p, ∀ l ∈ L_meta_2099_aux.avoidLines A, L_meta_2099_aux.inc p l := by
    rcases hs with h | ⟨p, hp⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, fun l hl => hp l (Finset.mem_filter.mp hl).2⟩
  obtain ⟨k, hk, he⟩ := L_meta_2099_aux.result A hm' hs'
  refine ⟨k, hk, ?_⟩
  intro j hj
  apply he j
  rcases hj with hp | ⟨l, hl, ha⟩
  · exact Or.inl hp
  · exact Or.inr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, hl⟩

