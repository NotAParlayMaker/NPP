import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7647_aux

def M : List ℕ := [7, 8, 10, 21, 23, 27, 36, 40, 41, 49, 53, 54, 66, 67, 69, 79, 80, 82, 92, 93, 95]

def A : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816]

def E (y : Fin 14 → Bool) : Prop :=
  ∃ (p : Fin 14) (q : Fin 14), (A.getD p.val 0).testBit q.val = true ∧ y p = true ∧ y q = true

def R : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290,
  1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297,
  8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

set_option maxRecDepth 100000 in
theorem memA : ∀ p q : Fin 14, (14 * p.val + q.val ∈ M) ↔ (A.getD p.val 0).testBit q.val = true := by
  decide

set_option maxRecDepth 100000 in
theorem bits : ∀ p q : Fin 14, (A.getD p.val 0).testBit q.val = true → p.val < 7 ∧ 7 ≤ q.val := by
  decide

theorem flipE (x : Fin 14 → Bool) (h : ∀ y, x ≤ y → ¬ E y → y = x) (i : Fin 14)
    (hi : x i = false) : E (Function.update x i true) := by
  by_contra hne
  have hle : x ≤ Function.update x i true := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [Function.update_of_ne hj]
  have := congrFun (h _ hle hne) i
  simp [hi] at this

def lv (c : Fin 7 → Bool) (l : Fin 14) : Bool :=
  (List.finRange 7).all (fun p => !((A.getD p.val 0).testBit l.val && c p))

def g (c : Fin 7 → Bool) (i : Fin 14) : Bool := if h : i.val < 7 then c ⟨i.val, h⟩ else lv c i

theorem cast_eq (p : Fin 14) (h : p.val < 7) : Fin.castLE (by norm_num) (⟨p.val, h⟩ : Fin 7) = p :=
  Fin.ext rfl

theorem lineEq (x : Fin 14 → Bool) (hx : ¬ E x) (hf : ∀ i, x i = false → E (Function.update x i true))
    (i : Fin 14) (hi : 7 ≤ i.val) :
    x i = lv (fun j : Fin 7 => x (Fin.castLE (by norm_num) j)) i := by
  rw [Bool.eq_iff_iff]
  simp only [lv, List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true',
    Bool.and_eq_false_iff]
  constructor
  · intro hxi p
    by_cases hb : (A.getD p.val 0).testBit i.val = true
    · right
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hx ⟨Fin.castLE (by norm_num) p, i, hb, hc, hxi⟩
    · left; simpa using hb
  · intro H
    by_contra hxi
    simp only [Bool.not_eq_true] at hxi
    obtain ⟨p', q', hadj, hp', hq'⟩ := hf i hxi
    obtain ⟨h1, h2⟩ := bits p' q' hadj
    have hne : p' ≠ i := fun e => by rw [e] at h1; omega
    rw [Function.update_of_ne hne] at hp'
    by_cases hq : q' = i
    · rw [hq] at hadj
      rcases H ⟨p'.val, h1⟩ with h | h
      · have h' : (A.getD p'.val 0).testBit i.val = false := h
        rw [hadj] at h'; cases h'
      · rw [cast_eq p' h1, hp'] at h; cases h
    · rw [Function.update_of_ne hq] at hq'
      exact hx ⟨p', q', hadj, hp', hq'⟩

theorem ptEq (x : Fin 14 → Bool) (hx : ¬ E x) (hf : ∀ i, x i = false → E (Function.update x i true))
    (p : Fin 14) (hp : p.val < 7) (hxp : x p = false) :
    ∃ l : Fin 14, (A.getD p.val 0).testBit l.val = true ∧ x l = true := by
  obtain ⟨p', q', hadj, hp', hq'⟩ := hf p hxp
  obtain ⟨h1, h2⟩ := bits p' q' hadj
  have hne : q' ≠ p := fun e => by rw [e] at h2; omega
  rw [Function.update_of_ne hne] at hq'
  by_cases he : p' = p
  · subst he; exact ⟨q', hadj, hq'⟩
  · rw [Function.update_of_ne he] at hp'
    exact absurd ⟨p', q', hadj, hp', hq'⟩ hx

set_option maxRecDepth 100000 in
theorem finChk : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    (∀ p : Fin 7, (![b0, b1, b2, b3, b4, b5, b6] : Fin 7 → Bool) p = false →
      ∃ l : Fin 14, (A.getD p.val 0).testBit l.val = true ∧
        g ![b0, b1, b2, b3, b4, b5, b6] l = true) →
    ∃ k ∈ R, ∀ i : Fin 14, g ![b0, b1, b2, b3, b4, b5, b6] i = k.testBit i.val := by
  decide

theorem part2 (x : Fin 14 → Bool) (hx : ¬ E x) (h : ∀ y, x ≤ y → ¬ E y → y = x) :
    ∃ k ∈ R, (fun i : Fin 14 => k.testBit i.val) = x := by
  have hf : ∀ i, x i = false → E (Function.update x i true) := fun i hi => flipE x h i hi
  set c : Fin 7 → Bool := fun j => x (Fin.castLE (by norm_num) j) with hcdef
  have hxg : x = g c := by
    funext i
    unfold g
    split_ifs with hi
    · show x i = x (Fin.castLE _ ⟨i.val, hi⟩)
      rw [cast_eq i hi]
    · exact lineEq x hx hf i (by omega)
  have hc : c = ![c 0, c 1, c 2, c 3, c 4, c 5, c 6] := by
    funext j; fin_cases j <;> rfl
  have hpt : ∀ p : Fin 7, (![c 0, c 1, c 2, c 3, c 4, c 5, c 6] : Fin 7 → Bool) p = false →
      ∃ l : Fin 14, (A.getD p.val 0).testBit l.val = true ∧
        g ![c 0, c 1, c 2, c 3, c 4, c 5, c 6] l = true := by
    intro p hp
    rw [← hc] at hp ⊢
    obtain ⟨l, hl, hxl⟩ := ptEq x hx hf (Fin.castLE (by norm_num) p) (by rw [Fin.val_castLE]; exact p.isLt) hp
    refine ⟨l, hl, ?_⟩
    rw [← hxg]; exact hxl
  obtain ⟨k, hk, hrow⟩ := finChk _ _ _ _ _ _ _ hpt
  refine ⟨k, hk, ?_⟩
  funext i
  rw [hxg, hc]
  exact (hrow i).symm

theorem bridge (y : Fin 14 → Bool) :
    (∃ (p : Fin 14) (q : Fin 14), 14 * p.val + q.val ∈ M ∧ y p = true ∧ y q = true) ↔ E y := by
  unfold E
  simp only [memA]

end PEqualNP.Outside.L_meta_7647_aux

theorem PEqualNP.Outside.L_meta_7647 : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), (14 : ℕ) * ↑x2 + ↑x3 ∈ [(7 : ℕ), (8 : ℕ), (10 : ℕ), (21 : ℕ), (23 : ℕ), (27 : ℕ), (36 : ℕ), (40 : ℕ), (41 : ℕ), (49 : ℕ), (53 : ℕ), (54 : ℕ), (66 : ℕ), (67 : ℕ), (69 : ℕ), (79 : ℕ), (80 : ℕ), (82 : ℕ), (92 : ℕ), (93 : ℕ), (95 : ℕ)] ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∀ (x2 : Fin (14 : ℕ) → Bool),   ¬x1 x2 →     (∀ (x4 : Fin (14 : ℕ) → Bool), x2 ≤ x4 → ¬x1 x4 → x4 = x2) →       ∃         x5 ∈           have x6 : List ℕ :=             have x6 : List ℕ :=               have x6 : List ℕ := [(10656 : ℕ), (12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];               (8488 : ℕ) :: (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: x6;             have x7 : List ℕ := (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: x6;             (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x7;           have x7 : List ℕ :=             have x7 : List ℕ := (2338 : ℕ) :: (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: x6;             (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: x7;           have x8 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: (1220 : ℕ) :: x7;           (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x8,         (fun (x6 : Fin (14 : ℕ)) => x5.testBit ↑x6) = x2 := by
  intro x1 x2 hx hm
  have hx2 : ¬ PEqualNP.Outside.L_meta_7647_aux.E x2 := fun h => hx ((PEqualNP.Outside.L_meta_7647_aux.bridge x2).2 h)
  have hm2 : ∀ y, x2 ≤ y → ¬ PEqualNP.Outside.L_meta_7647_aux.E y → y = x2 := fun y hy hy2 => hm y hy (fun h => hy2 ((PEqualNP.Outside.L_meta_7647_aux.bridge y).1 h))
  exact PEqualNP.Outside.L_meta_7647_aux.part2 x2 hx2 hm2
