import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3529

-- The adjacency of the statement: point a (below 7) is adjacent to the line whose bit is set.
def A (a b : ℕ) : Bool := ([1408, 8832, 12544, 6272, 11264, 5632, 2816].getD a 0).testBit b

abbrev F (x : Fin 14 → Bool) : Prop := ∃ a b : Fin 14, A a b = true ∧ x a = true ∧ x b = true

def rows : List ℕ := [129, 130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064,
  2112, 4100, 4104, 4128, 8194, 8196, 8208, 127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290,
  1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297,
  8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

def T (r : Fin 58) (k : Fin 14) : Bool := (rows.getD r 0).testBit k

-- A point is adjacent only to lines: rows beyond the seventh are empty.
theorem A_point (a b : Fin 14) (h : A a b = true) : (a : ℕ) < 7 := by
  revert h; revert a b; decide

theorem edges_in_table : ∀ a b : Fin 14, A a b = true →
    ∃ r : Fin 58, (r : ℕ) < 21 ∧ (fun k => decide (k = a ∨ k = b)) = T r := by
  decide +kernel

-- The candidate maximal independent set with point part P.
def mk (P : Fin 7 → Bool) (k : Fin 14) : Bool :=
  if h : (k : ℕ) < 7 then P ⟨k, h⟩ else decide (∀ p : Fin 7, P p = true → A p k = false)

abbrev Good (z : Fin 14 → Bool) : Prop := ¬ F z ∧ ∀ v : Fin 14, z v = false → F (Function.update z v true)

theorem mis_in_table : ∀ P : Fin 7 → Bool, Good (mk P) →
    ∃ r : Fin 58, 21 ≤ (r : ℕ) ∧ mk P = T r := by
  decide +kernel

end PEqualNP.Outside.L_meta_3529

open PEqualNP.Outside.L_meta_3529

theorem PEqualNP.Outside.L_meta_3529 : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; have x2 : Fin (58 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : Fin (58 : ℕ)) (x3 : Fin (14 : ℕ)) =>   ((have x4 : List ℕ :=             have x4 : List ℕ :=               have x4 : List ℕ :=                 have x4 : List ℕ := [(12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];                 (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: (10656 : ℕ) :: x4;               (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: (8488 : ℕ) :: (8713 : ℕ) :: x4;             have x5 : List ℕ := (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x4;             (1220 : ℕ) :: (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: (2338 : ℕ) :: (2565 : ℕ) :: x5;           have x5 : List ℕ :=             have x5 : List ℕ :=               have x5 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: x4;               (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x5;             (2112 : ℕ) :: (4100 : ℕ) :: (4104 : ℕ) :: (4128 : ℕ) :: (8194 : ℕ) :: (8196 : ℕ) :: (8208 : ℕ) :: x5;           have x6 : List ℕ := (544 : ℕ) :: (576 : ℕ) :: (1025 : ℕ) :: (1040 : ℕ) :: (1056 : ℕ) :: (2056 : ℕ) :: (2064 : ℕ) :: x5;           (129 : ℕ) :: (130 : ℕ) :: (136 : ℕ) :: (257 : ℕ) :: (260 : ℕ) :: (320 : ℕ) :: (514 : ℕ) :: x6).getD         ↑x2 (0 : ℕ)).testBit     ↑x3; ∀ (x3 : Fin (14 : ℕ) → Bool), (Minimal x1 x3 → ∃ (x5 : Fin (58 : ℕ)), ↑x5 < (21 : ℕ) ∧ x3 = x2 x5) ∧ (Maximal (fun (x4 : Fin (14 : ℕ) → Bool) => ¬x1 x4) x3 → ∃ (x5 : Fin (58 : ℕ)), (21 : ℕ) ≤ ↑x5 ∧ x3 = x2 x5) := by
  dsimp only
  intro x
  constructor
  · intro hmin
    obtain ⟨a, b, hab, ha, hb⟩ := hmin.1
    let y : Fin 14 → Bool := fun k => decide (k = a ∨ k = b)
    have hy : F y := ⟨a, b, hab, by simp [y], by simp [y]⟩
    have hle : y ≤ x := by
      intro k
      by_cases e : k = a ∨ k = b
      · rcases e with rfl | rfl
        · rw [ha]; exact le_top
        · rw [hb]; exact le_top
      · have : y k = false := decide_eq_false e
        rw [this]; exact bot_le
    have hge : x ≤ y := hmin.2 hy hle
    have hxy : x = y := le_antisymm hge hle
    obtain ⟨r, hr, hT⟩ := edges_in_table a b hab
    exact ⟨r, hr, by rw [hxy]; exact hT⟩
  · intro hmax
    have hnF : ¬ F x := hmax.1
    -- adding a vertex outside x creates an edge
    have hgood : Good x := by
      refine ⟨hnF, fun v hv => ?_⟩
      by_contra hc
      have hle : x ≤ Function.update x v true := by
        intro k
        by_cases e : k = v
        · subst e; simp [hv]
        · simp [Function.update_of_ne e]
      have h1 := hmax.2 hc hle v
      have h2 : x v = true := Bool.le_iff_imp.mp h1 (by simp)
      rw [hv] at h2
      exact absurd h2 (by decide)
    -- x is determined by its points
    let P : Fin 7 → Bool := fun p => x ⟨p, by omega⟩
    have hx : x = mk P := by
      funext k
      unfold mk
      by_cases hk : (k : ℕ) < 7
      · simp [hk, P]
      · simp only [hk, dite_false]
        by_cases hxk : x k = true
        · rw [hxk]
          symm
          rw [decide_eq_true_iff]
          intro p hp
          by_contra hA
          apply hnF
          exact ⟨⟨p, by omega⟩, k, by simpa using hA, hp, hxk⟩
        · simp only [Bool.not_eq_true] at hxk
          rw [hxk]
          symm
          rw [decide_eq_false_iff_not]
          intro hall
          obtain ⟨a, b, hab, ha, hb⟩ := hgood.2 k hxk
          have ha7 := A_point a b hab
          have hak : a ≠ k := by intro e; rw [e] at ha7; exact hk ha7
          rw [Function.update_of_ne hak] at ha
          by_cases hbk : b = k
          · subst hbk
            have := hall ⟨a, ha7⟩ ha
            simp at this
            rw [this] at hab
            exact absurd hab (by simp)
          · rw [Function.update_of_ne hbk] at hb
            exact hnF ⟨a, b, hab, ha, hb⟩
    obtain ⟨r, hr, hT⟩ := mis_in_table P (hx ▸ hgood)
    exact ⟨r, hr, by rw [hx]; exact hT⟩
