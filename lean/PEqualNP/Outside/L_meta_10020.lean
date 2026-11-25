import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_10020

abbrev Point := Fin 25
abbrev Line := Fin 30
abbrev Rectangle := Finset Point × Finset Line

def lineTable : List ℕ := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]

def avoids (p : Point) (j : Line) : Prop :=
  ((lineTable.getD p.val 0).testBit j.val) = false

def valid (R : Finset Point) (C : Finset Line) : Prop :=
  ∀ i ∈ R, ∀ j ∈ C, avoids i j

-- Each word stores the points outside one line.
def pointMask (j : Line) : ℕ := ([32472030, 31389629, 29224827, 24895223, 16236015, 16510910, 31973245, 31407867, 29293047, 25032655, 25083774, 16644861, 32241147, 30928855, 29319087, 28833534, 25128445, 16703451, 32358327, 31193967, 31317502, 29081565, 24640443, 16742263, 32435951, 33554400, 33553439, 33522687, 32538623, 1048575] : List ℕ).getD j.val 0

theorem mask_correct : ∀ (p : Point) (j : Line),
    avoids p j → (pointMask j).testBit p.val = true := by
  unfold avoids
  decide

def countBits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, word => countBits k word + (if word.testBit k then 1 else 0)

-- Three bits per table entry suffice for the population count of five bits.
def digit (word : ℕ) : ℕ :=
  (55157063682984551670960690248 >>> (3*(word % 32))) % 8

theorem digit_eq (word : ℕ) : digit word = countBits 5 word := by
  have table : ∀ i : Fin 32,
      (55157063682984551670960690248 >>> (3*i.val)) % 8 = countBits 5 i.val := by decide
  calc
    digit word = countBits 5 (word % 32) := table ⟨word % 32, Nat.mod_lt _ (by decide)⟩
    _ = countBits 5 word := by
      rw [show (32 : ℕ) = 2^5 by decide]
      simp only [countBits, Nat.testBit_mod_two_pow]
      norm_num

def totalBits (word : ℕ) : ℕ :=
  digit word + digit (word >>> 5) + digit (word >>> 10) + digit (word >>> 15) + digit (word >>> 20)

theorem totalBits_eq (word : ℕ) : totalBits word = countBits 25 word := by
  simp only [totalBits, digit_eq, countBits, Nat.testBit_shiftRight, Nat.reduceAdd, Nat.zero_add]
  omega

theorem countBits_eq (width word : ℕ) :
    ((Finset.range width).filter (fun i => word.testBit i = true)).card = countBits width word := by
  induction width with
  | zero => simp [countBits]
  | succ n ih =>
    by_cases h : word.testBit n = true <;>
      simp [Finset.range_add_one, Finset.filter_insert, countBits, h, ih]

theorem card_le_bits (R : Finset Point) (word : ℕ)
    (h : ∀ i ∈ R, word.testBit i.val = true) : R.card ≤ countBits 25 word := by
  rw [← countBits_eq]
  have sub : R.image Fin.val ⊆ (Finset.range 25).filter (fun i => word.testBit i = true) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr p.isLt, h p hp⟩
  simpa [Finset.card_image_of_injective _ Fin.val_injective] using Finset.card_le_card sub

-- At a branch, word is an upper bound on the permitted point set and
-- chosen is the number of lines already included. Both updates are exact.
def search : List Line → ℕ → ℕ → Bool
  | [], word, chosen => decide (totalBits word * chosen ≤ 54)
  | j :: js, word, chosen =>
    decide (totalBits word * (chosen + js.length + 1) ≤ 54) ||
      (search js (word &&& pointMask j) (chosen+1) && search js word chosen)

theorem search_sound (js : List Line) (word chosen : ℕ) (ok : search js word chosen = true)
    (R : Finset Point) (C : Finset Line) (hr : ∀ i ∈ R, word.testBit i.val = true)
    (hc : ∀ j ∈ C, j ∈ js) (free : valid R C) : R.card * (chosen + C.card) ≤ 54 := by
  induction js generalizing word chosen C with
  | nil =>
    have he : C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun j hj => by simpa using hc j hj)
    simp only [search, totalBits_eq, decide_eq_true_eq] at ok
    simpa [he] using (Nat.mul_le_mul_right chosen (card_le_bits R word hr)).trans ok
  | cons j js ih =>
    simp only [search, totalBits_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ok
    rcases ok with done | ⟨keep, skip⟩
    · have hc' : C.card ≤ (j :: js).length :=
        (Finset.card_le_card (show C ⊆ (j :: js).toFinset from
          fun i hi => List.mem_toFinset.mpr (hc i hi))).trans (List.toFinset_card_le _)
      exact (Nat.mul_le_mul (card_le_bits R word hr) (by simp only [List.length_cons] at hc'; omega)).trans done
    · by_cases hj : j ∈ C
      · have hrem (i) (hi : i ∈ C.erase j) : i ∈ js := by
          exact (List.mem_cons.mp (hc i (Finset.mem_of_mem_erase hi))).resolve_left
            (Finset.ne_of_mem_erase hi)
        have hword (i) (hi : i ∈ R) : (word &&& pointMask j).testBit i.val = true := by
          simp [Nat.testBit_and, hr i hi, mask_correct i j (free i hi j hj)]
        have hfree : valid R (C.erase j) := fun i hi l hl => free i hi l (Finset.mem_of_mem_erase hl)
        have smaller := ih (word &&& pointMask j) (chosen+1) keep (C.erase j)
          hword hrem hfree
        have hcard := Finset.card_erase_add_one hj
        rwa [show chosen+1+(C.erase j).card = chosen+C.card by omega] at smaller
      · have hrem (i) (hi : i ∈ C) : i ∈ js :=
          (List.mem_cons.mp (hc i hi)).resolve_left (fun e => hj (e ▸ hi))
        exact ih word chosen skip C hr hrem free

def eligible : List Line := [2, 3, 4, 7, 8, 9, 12, 13, 14, 17, 18, 19, 22, 23, 24, 26, 27, 28, 29]

theorem eligible_complete : ∀ j : Line, avoids 0 j → avoids 1 j → j ∈ eligible := by
  unfold avoids
  decide

set_option maxHeartbeats 0 in
theorem search_complete : search eligible 33554431 0 = true := by decide +kernel

def badAt (p q : Point) : Prop := ∃ (R : Finset Point) (C : Finset Line),
  p ∈ R ∧ q ∈ R ∧ valid R C ∧ 54 < R.card * C.card

theorem normalized : ¬ badAt 0 1 := by
  rintro ⟨R,C,h0,h1,hfree,hbig⟩
  have allBits : ∀ i : Point, (33554431 : ℕ).testBit i.val = true := by decide
  have smaller := search_sound eligible 33554431 0 search_complete R C
    (fun i _ => allBits i) (fun j hj => eligible_complete j (hfree 0 h0 j hj) (hfree 1 h1 j hj)) hfree
  exact (not_lt_of_ge (by simpa using smaller)) hbig

-- A primitive linear map cycles through the 24 nonzero points.
-- The second map is translation by the negative of point 1.
def turn (i : Point) : Point := ([0, 7, 14, 16, 23, 2, 9, 11, 18, 20, 4, 6, 13, 15, 22, 1, 8, 10, 17, 24, 3, 5, 12, 19, 21] : List Point).getD i.val 0
def turnLine (i : Line) : Line := ([25, 26, 27, 28, 29, 20, 23, 21, 24, 22, 15, 19, 18, 17, 16, 5, 6, 7, 8, 9, 0, 2, 4, 1, 3, 10, 12, 14, 11, 13] : List Line).getD i.val 0
def shift (i : Point) : Point := ([4, 0, 1, 2, 3, 9, 5, 6, 7, 8, 14, 10, 11, 12, 13, 19, 15, 16, 17, 18, 24, 20, 21, 22, 23] : List Point).getD i.val 0
def shiftLine (i : Line) : Line := ([4, 0, 1, 2, 3, 9, 5, 6, 7, 8, 14, 10, 11, 12, 13, 19, 15, 16, 17, 18, 24, 20, 21, 22, 23, 25, 26, 27, 28, 29] : List Line).getD i.val 0

theorem move_bad (f : Point → Point) (g : Line → Line) (hf : Function.Injective f)
    (hg : Function.Injective g) (pres : ∀ p j, avoids p j → avoids (f p) (g j))
    {p q : Point} (h : badAt p q) : badAt (f p) (f q) := by
  obtain ⟨R,C,hp,hq,hfree,hbig⟩ := h
  refine ⟨R.image f, C.image g, Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hq, ?_, ?_⟩
  · intro u hu v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    exact pres i j (hfree i hi j hj)
  · simpa [Finset.card_image_of_injective _ hf, Finset.card_image_of_injective _ hg] using hbig

theorem turn_inj : Function.Injective turn := by
  change ∀ p q : Point, turn p = turn q → p = q
  decide

theorem shift_inj : Function.Injective shift := by
  change ∀ p q : Point, shift p = shift q → p = q
  decide

theorem turn_bad {p q : Point} : badAt p q → badAt (turn p) (turn q) := by
  apply move_bad turn turnLine turn_inj
  · change ∀ i j : Line, turnLine i = turnLine j → i = j
    decide
  · unfold avoids
    decide

theorem shift_bad {p q : Point} : badAt p q → badAt (shift p) (shift q) := by
  apply move_bad shift shiftLine shift_inj
  · change ∀ i j : Line, shiftLine i = shiftLine j → i = j
    decide
  · unfold avoids
    decide

theorem iterate_bad (k : ℕ) {p q : Point} (h : badAt p q) :
    badAt (turn^[k] p) (turn^[k] q) := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [Function.iterate_succ_apply'] using turn_bad ih

theorem cycle : ∀ p : Point, p ≠ 0 → ∃ k : Fin 24, turn^[k.val] p = 1 := by decide

theorem zero_case {q : Point} (hq : q ≠ 0) (h : badAt 0 q) : False := by
  obtain ⟨k, hk⟩ := cycle q hq
  have fix : Function.IsFixedPt turn 0 := by decide
  exact normalized (by simpa only [hk, (fix.iterate k.val).eq] using iterate_bad k.val h)

theorem area (R : Finset Point) (C : Finset Line) (free : valid R C) : R.card*C.card ≤ 54 := by
  by_contra! large
  have colBound : C.card ≤ 30 := by simpa using Finset.card_le_univ C
  have many : 1 < R.card := by
    by_contra! few
    have h := Nat.mul_le_mul few colBound
    omega
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp many
  have h : badAt p q := ⟨R,C,hp,hq,free,large⟩
  by_cases pzero : p = 0
  · subst p
    exact zero_case ne.symm h
  · obtain ⟨k,hk⟩ := cycle p pzero
    have translated := shift_bad (iterate_bad k.val h)
    have distinct := fun (eq : shift (turn^[k.val] p) = shift (turn^[k.val] q)) =>
      ne ((turn_inj.iterate k.val) (shift_inj eq))
    rw [hk, show shift 1 = 0 by decide] at translated distinct
    exact zero_case (Ne.symm distinct) translated

/-- The six affine points of the conic x² - 2y² = 1 attain the area bound. -/
theorem area_attained : ∃ (R : Finset Point) (C : Finset Line),
    valid R C ∧ R.card * C.card = 54 := by
  refine ⟨{5, 12, 13, 17, 18, 20}, {1, 4, 7, 8, 10, 15, 22, 23, 25}, ?_⟩
  unfold valid avoids
  decide

def uncoveredByIncidence : Finset (Point × Line) :=
  Finset.univ.filter (fun z => (lineTable.getD z.1.val 0).testBit z.2.val = false)

theorem cover_card (L : List Rectangle) (good : ∀ r ∈ L, valid r.1 r.2) :
    (L.toFinset.biUnion (fun r => r.1 ×ˢ r.2)).card ≤ L.length * 54 := by
  induction L with
  | nil => simp
  | cons r rs ih =>
    have a := area r.1 r.2 (good r (by simp))
    have b := ih (fun d hd => good d (by simp [hd]))
    simp only [List.toFinset_cons, Finset.biUnion_insert, List.length_cons]
    apply (Finset.card_union_le ..).trans
    simpa [Finset.card_product, Nat.add_mul, Nat.add_comm] using (Nat.add_le_add a b)

end PEqualNP.Outside.L_meta_10020

open PEqualNP.Outside.L_meta_10020

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_10020 : ¬ (∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 10 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L,hlen,hgood,hcover⟩
  have total : uncoveredByIncidence.card = 600 := by decide
  have incl : uncoveredByIncidence ⊆ L.toFinset.biUnion (fun r => r.1 ×ˢ r.2) := by
    intro z hz
    obtain ⟨r,hr,hp,hj⟩ := hcover z.1 z.2 (Finset.mem_filter.mp hz).2
    exact Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr hr, Finset.mem_product.mpr ⟨hp,hj⟩⟩
  have h := (Finset.card_le_card incl).trans (cover_card L hgood)
  omega
