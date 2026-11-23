import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1398_aux

-- The ten rows select first the five edges, then the five diagonals of the cycle.
-- Wire masks record the value of a formula on these rows in that order.
private abbrev Mask := BitVec 10

private def wire (i : Fin 5) : Mask := ![305,579,166,332,664] i

private def row (r : Fin 10) (i : Fin 5) : Bool := (wire i).getLsbD r.val

-- The lists certify the masks needed at depths zero, one and two.
private def pool : ℕ → List Mask
  | 0 => [305, 579, 166, 332, 664]
  | 1 => [1, 2, 4, 8, 16, 32, 64, 128, 166, 256, 305, 332, 381, 439, 494, 512, 579, 664, 702, 731, 743, 847, 883, 953, 988]
  | 2 => [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 60, 64, 65, 66, 68, 72, 80, 89, 96, 101, 128, 129, 130, 132, 136, 144, 147, 160, 166, 167, 174, 182, 192, 202, 230, 256, 257, 258, 260, 263, 264, 272, 288, 305, 307, 309, 313, 320, 332, 333, 334, 348, 354, 364, 369, 381, 383, 384, 404, 422, 424, 433, 439, 447, 460, 494, 495, 503, 509, 510, 511, 512, 513, 514, 516, 520, 526, 528, 544, 562, 576, 579, 583, 587, 595, 611, 640, 664, 665, 666, 668, 673, 678, 696, 702, 703, 707, 708, 728, 731, 735, 743, 751, 759, 763, 766, 767, 768, 777, 817, 835, 844, 847, 848, 863, 879, 883, 887, 891, 893, 895, 920, 951, 953, 955, 957, 958, 959, 975, 987, 988, 989, 990, 991, 999, 1006, 1007, 1011, 1015, 1017, 1019, 1020, 1021, 1022, 1023]
  | _ => []

private def allowed (k : ℕ) (v : Mask) : Bool :=
  if k < 3 then (pool k).contains v else if k = 3 then v != 31 else true

private def family (k : ℕ) : Set ((Fin 5 → Bool) → Bool) :=
  {f | ∃ v : Mask, allowed k v = true ∧ ∀ r : Fin 10, f (row r) = v.getLsbD r.val}

-- At depth three it suffices to exclude the five-edge mask, whose value is 31.
set_option maxRecDepth 8192 in
private lemma certificate (k : ℕ) (hk : k < 3) :
    (pool k).all (fun a => allowed (k+1) a &&
      (pool k).all (fun b => allowed (k+1) (a &&& b) && allowed (k+1) (a ||| b))) = true := by
  interval_cases k <;> decide +kernel

private lemma step {k : ℕ} {a b : Mask} (ha : allowed k a = true) (hb : allowed k b = true) :
    allowed (k+1) a = true ∧ allowed (k+1) (a &&& b) = true ∧ allowed (k+1) (a ||| b) = true := by
  by_cases hk : k < 3
  · have am : a ∈ pool k := by simpa [allowed,hk] using ha
    have bm : b ∈ pool k := by simpa [allowed,hk] using hb
    have h := List.all_eq_true.mp (certificate k hk) a am
    simp only [Bool.and_eq_true] at h
    have pair := List.all_eq_true.mp h.2 b bm
    simp only [Bool.and_eq_true] at pair
    exact ⟨h.1,pair⟩
  · have h₁ : ¬ k+1 < 3 := by omega
    have h₂ : k+1 ≠ 3 := by omega
    simp [allowed,h₁,h₂]

private lemma projections (i : Fin 5) : (fun x : Fin 5 → Bool => x i) ∈ family 0 := by
  refine ⟨wire i, ?_, fun _ => rfl⟩
  fin_cases i <;> decide

private lemma promote (k : ℕ) (f : (Fin 5 → Bool) → Bool) (hf : f ∈ family k) :
    f ∈ family (k+1) := by
  obtain ⟨v,hv,hr⟩ := hf
  exact ⟨v,(step hv hv).1,hr⟩

private lemma combine (k : ℕ) (f g : (Fin 5 → Bool) → Bool)
    (hf : f ∈ family k) (hg : g ∈ family k) :
    (fun x => f x && g x) ∈ family (k+1) ∧ (fun x => f x || g x) ∈ family (k+1) := by
  obtain ⟨a,ha,hf⟩ := hf
  obtain ⟨b,hb,hg⟩ := hg
  exact ⟨⟨a &&& b,(step ha hb).2.1,fun r => by simp [hf r,hg r]⟩,
    ⟨a ||| b,(step ha hb).2.2,fun r => by simp [hf r,hg r]⟩⟩

private lemma cycleRows : ∀ r : Fin 10,
    ((row r 0 && row r 1) || (row r 1 && row r 2) || (row r 2 && row r 3) ||
      (row r 3 && row r 4) || (row r 4 && row r 0)) = (31 : Mask).getLsbD r.val := by
  decide

end PEqualNP.Outside.L_meta_1398_aux

open PEqualNP.Outside.L_meta_1398_aux in
theorem PEqualNP.Outside.L_meta_1398 : ¬ (∀ T : ℕ → Set ((Fin 5 → Bool) → Bool), (∀ i : Fin 5, (fun x : Fin 5 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 5 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 5 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 5 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 5 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 5 → Bool => (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3) || (z 3 && z 4) || (z 4 && z 0)) ∈ T 3) := by
  intro h
  obtain ⟨v,hv,hr⟩ := h family projections promote combine
  have eq : v = 31 := BitVec.eq_of_getLsbD_eq_iff.mpr fun i hi =>
    (hr ⟨i,hi⟩).symm.trans (cycleRows ⟨i,hi⟩)
  subst v
  contradiction
