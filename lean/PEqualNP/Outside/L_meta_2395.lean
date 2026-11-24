import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2395

abbrev Inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def freePoints (Y : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun p => ∀ l ∈ Y, ¬ Inc p l

def freeLines (X : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ X, ¬ Inc p l

abbrev PointArc (X : Finset (Fin 13)) : Prop :=
  ∀ l, (X.filter fun p => Inc p l).card ≤ 2

abbrev LineArc (Y : Finset (Fin 13)) : Prop :=
  ∀ p, (Y.filter fun l => Inc p l).card ≤ 2

def low : Fin 4 ↪ Fin 13 := ⟨Fin.castAdd 9, by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 13 => i.val) h)⟩

def high : Fin 9 ↪ Fin 13 := ⟨Fin.natAdd 4, by
  intro a b h
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val h)⟩

def joinSets (A : Finset (Fin 4)) (B : Finset (Fin 9)) : Finset (Fin 13) :=
  A.map low ∪ B.map high

lemma split_set (S : Finset (Fin 13)) :
    ∃ A B, S = joinSets A B := by
  let A := Finset.univ.filter fun x : Fin 4 => low x ∈ S
  let B := Finset.univ.filter fun x : Fin 9 => high x ∈ S
  refine ⟨A, B, ?_⟩
  ext x
  constructor
  · refine Fin.addCases (m := 4) (n := 9) (motive := fun t => t ∈ S → t ∈ joinSets A B)
      (fun i : Fin 4 => ?_) (fun j : Fin 9 => ?_) x
    · intro hi
      apply Finset.mem_union.mpr
      have hAi : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      exact Or.inl (Finset.mem_map.mpr ⟨i, hAi, rfl⟩)
    · intro hj
      apply Finset.mem_union.mpr
      have hBj : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      exact Or.inr (Finset.mem_map.mpr ⟨j, hBj, rfl⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hl | hr
    · rcases Finset.mem_map.mp hl with ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    · rcases Finset.mem_map.mp hr with ⟨j, hj, rfl⟩
      exact (Finset.mem_filter.mp hj).2

lemma prefix_cases : ∀ A : Finset (Fin 4),
    A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = {2} ∨ A = {3} ∨
    A = {0, 1} ∨ A = {0, 2} ∨ A = {0, 3} ∨ A = {1, 2} ∨ A = {1, 3} ∨ A = {2, 3} ∨
    A = {0, 1, 2} ∨ A = {0, 1, 3} ∨ A = {0, 2, 3} ∨ A = {1, 2, 3} ∨
    A = {0, 1, 2, 3} := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 40000000 in
lemma freeLines_away_from_zero (X : Finset (Fin 13)) :
    PointArc X → ∃ l ∈ freeLines X, ¬ Inc 0 l := by
  obtain ⟨A, B, rfl⟩ := split_set X
  revert B
  rcases prefix_cases A with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

lemma card_mapped_filter (X : Finset (Fin 13)) (e : Fin 13 ↪ Fin 13)
    (P Q : Fin 13 → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P (e x) ↔ Q x) : ((X.map e).filter P).card = (X.filter Q).card := by
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  ext x
  simp [h x]

lemma inc_shift (a b t : Fin 13) : Inc (a + t) (b + t) ↔ Inc a b := by
  simp only [Inc, add_right_comm b t (1 : Fin 13), add_right_comm b t (3 : Fin 13), add_right_comm b t (9 : Fin 13), add_right_cancel_iff]

lemma freeLines_not_concurrent (X : Finset (Fin 13)) (hX : PointArc X) (p : Fin 13) :
    ∃ l ∈ freeLines X, ¬ Inc p l := by
  let e : Fin 13 ↪ Fin 13 := ⟨fun a => a + -p, fun _ _ h => add_right_cancel h⟩
  let T := X.map e
  have hMove (a b : Fin 13) : Inc (e a) b ↔ Inc a (b + p) := by
    change Inc (a + -p) b ↔ Inc a (b + p)
    simpa only [add_assoc, add_neg_cancel, add_zero] using inc_shift a (b + p) (-p)
  have hT : PointArc T := by
    intro b
    change ((X.map e).filter fun a => Inc a b).card ≤ 2
    rw [card_mapped_filter X e (fun a => Inc a b) (fun a => Inc a (b + p)) (fun a => hMove a b)]
    exact hX (b + p)
  obtain ⟨b, hb, h0⟩ := freeLines_away_from_zero T hT
  have he : e p = 0 := by change p + -p = 0; exact add_neg_cancel _
  refine ⟨b + p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · intro a ha hab
    exact (Finset.mem_filter.mp hb).2 _ (Finset.mem_map.mpr ⟨a, ha, rfl⟩) ((hMove a b).2 hab)
  · intro hp
    exact h0 (he ▸ (hMove p b).2 hp)

lemma inc_reverse : ∀ a b : Fin 13, Inc (-b) (-a) ↔ Inc a b := by decide

lemma freePoints_not_collinear (Y : Finset (Fin 13)) (hY : LineArc Y) (l : Fin 13) :
    ∃ p ∈ freePoints Y, ¬ Inc p l := by
  let e : Fin 13 ↪ Fin 13 := ⟨fun a => -a, fun _ _ h => neg_injective h⟩
  let X := Y.map e
  have hReverse (a b : Fin 13) : Inc (e a) b ↔ Inc (-b) a := by
    change Inc (-a) b ↔ Inc (-b) a
    simpa only [neg_neg] using inc_reverse (-b) a
  have hX : PointArc X := by
    intro b
    change ((Y.map e).filter fun a => Inc a b).card ≤ 2
    rw [card_mapped_filter Y e (fun a => Inc a b) (Inc (-b)) (fun a => hReverse a b)]
    exact hY (-b)
  obtain ⟨b, hb, hnot⟩ := freeLines_not_concurrent X hX (-l)
  refine ⟨-b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · intro a ha hab
    exact (Finset.mem_filter.mp hb).2 _ (Finset.mem_map.mpr ⟨a, ha, rfl⟩) ((hReverse a b).2 hab)
  · intro hl
    exact hnot ((hReverse l b).2 hl)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
lemma lines_meet_once : ∀ a b : Fin 13, a ≠ b → ∃ p : Fin 13,
    Inc p a ∧ Inc p b ∧ ∀ q : Fin 13, Inc q a → Inc q b → q = p := by
  decide

lemma another_line (X : Finset (Fin 13)) (hX : PointArc X) (a : Fin 13) :
    ∃ b ∈ freeLines X, b ≠ a := by
  obtain ⟨b, hb, hnb⟩ := freeLines_not_concurrent X hX a
  exact ⟨b, hb, fun h => hnb (Or.inl h.symm)⟩

lemma extend_pair (X : Finset (Fin 13)) (hX : PointArc X) (a b : Fin 13)
    (ha : a ∈ freeLines X) (hb : b ∈ freeLines X) (hab : a ≠ b) :
    ∃ Z : Finset (Fin 13), {a, b} ⊆ Z ∧ Z ⊆ freeLines X ∧ LineArc Z ∧ 3 ≤ Z.card := by
  obtain ⟨p, hpa, hpb, hunique⟩ := lines_meet_once a b hab
  obtain ⟨c, hc, hpc⟩ := freeLines_not_concurrent X hX p
  have hac : a ≠ c := fun h => hpc (h ▸ hpa)
  have hbc : b ≠ c := fun h => hpc (h ▸ hpb)
  let Z : Finset (Fin 13) := {a, b, c}
  have hcard : Z.card = 3 := Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  refine ⟨Z, ?_, ?_, ?_, by omega⟩
  · intro l hl
    simp [Z] at hl ⊢
    exact hl.elim Or.inl (fun h => Or.inr (Or.inl h))
  · intro l hl
    simp [Z] at hl
    rcases hl with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  · intro q
    change (Z.filter (Inc q)).card ≤ 2
    by_contra hbig
    have hthree : 3 ≤ (Z.filter (Inc q)).card := Nat.lt_of_not_ge hbig
    have heq : Z.filter (Inc q) = Z :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (hcard.symm ▸ hthree)
    have hall := Finset.filter_eq_self.mp heq
    have hqa := hall a (by simp [Z])
    have hqb := hall b (by simp [Z])
    have hqc := hall c (by simp [Z])
    exact hpc (hunique q hqa hqb ▸ hqc)

lemma extend_lines (X Y : Finset (Fin 13)) (hX : PointArc X) (hY : LineArc Y)
    (hfree : Y ⊆ freeLines X) :
    ∃ Z : Finset (Fin 13), Y ⊆ Z ∧ Z ⊆ freeLines X ∧ LineArc Z ∧ 3 ≤ Z.card := by
  by_cases hsize : 3 ≤ Y.card
  · exact ⟨Y, Finset.Subset.rfl, hfree, hY, hsize⟩
  have hsmall : Y.card = 0 ∨ Y.card = 1 ∨ Y.card = 2 := by omega
  rcases hsmall with h0 | h1 | h2
  · have he : Y = ∅ := Finset.card_eq_zero.mp h0
    obtain ⟨a, ha, _⟩ := freeLines_not_concurrent X hX 0
    obtain ⟨b, hb, hba⟩ := another_line X hX a
    obtain ⟨Z, _, hZX, hZ, hcard⟩ := extend_pair X hX a b ha hb hba.symm
    exact ⟨Z, he ▸ Finset.empty_subset _, hZX, hZ, hcard⟩
  · obtain ⟨a, he⟩ := Finset.card_eq_one.mp h1
    have ha : a ∈ freeLines X := hfree (by simp [he])
    obtain ⟨b, hb, hba⟩ := another_line X hX a
    obtain ⟨Z, hpair, hZX, hZ, hcard⟩ := extend_pair X hX a b ha hb hba.symm
    have hYZ : Y ⊆ Z := by
      rw [he]
      exact Finset.singleton_subset_iff.mpr (hpair (by simp))
    exact ⟨Z, hYZ, hZX, hZ, hcard⟩
  · obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp h2
    have ha : a ∈ freeLines X := hfree (by simp [he])
    have hb : b ∈ freeLines X := hfree (by simp [he])
    simpa only [he] using extend_pair X hX a b ha hb hab

end PEqualNP.Outside.L_meta_2395

open PEqualNP.Outside.L_meta_2395

theorem PEqualNP.Outside.L_meta_2395 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, ¬x1 x4 x6) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x2 | x1 x6 x5}.card ≤ (2 : ℕ)) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x1 x6 x7}.card ≤ (2 : ℕ)) → ∃ (x7 : Finset (Fin (13 : ℕ))), x2 ⊆ x7 ∧ (∀ x8 ∈ x3, ∀ x10 ∈ x7, ¬x1 x10 x8) ∧ (∀ x8 ∉ x7, ∃ (x10 : Fin (13 : ℕ)), (∀ x11 ∈ x7, ¬x1 x11 x10) ∧ x1 x8 x10) ∧ (¬∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x7, x1 x9 x8) ∧ ¬∃ (x8 : Fin (13 : ℕ)), ∀ (x9 : Fin (13 : ℕ)), (∀ x10 ∈ x7, ¬x1 x10 x9) → x1 x8 x9 := by
  intro _ X Y hdis hX hY
  classical
  have hYfree : Y ⊆ freeLines X := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => hdis p hp l hl⟩
  obtain ⟨Z, hYZ, hZX, hZ, hcard⟩ := extend_lines X Y hX hY hYfree
  refine ⟨freePoints Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl =>
      (Finset.mem_filter.mp (hZX hl)).2 p hp⟩
  · intro l hl p hp
    exact (Finset.mem_filter.mp hp).2 l (hYZ hl)
  · intro p hp
    have h : ¬ ∀ l ∈ Z, ¬ Inc p l := fun h => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    push Not at h
    obtain ⟨l, hl, hi⟩ := h
    exact ⟨l, fun q hq => (Finset.mem_filter.mp hq).2 l hl, hi⟩
  · rintro ⟨l, hall⟩
    obtain ⟨p, hp, hnot⟩ := freePoints_not_collinear Z hZ l
    exact hnot (hall p hp)
  · rintro ⟨p, hall⟩
    have hp : ∀ l ∈ Z, Inc p l := fun l hl =>
      hall l (fun q hq => (Finset.mem_filter.mp hq).2 l hl)
    have hbound := hZ p
    rw [Finset.filter_eq_self.mpr hp] at hbound
    omega
