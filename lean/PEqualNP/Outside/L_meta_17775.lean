import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17775

def D : Fin 5 → Fin 21 := ![20, 0, 5, 7, 17]

def one (a : ℕ) : ℕ := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480].getD a 0

theorem one_spec : ∀ a y : Fin 21, (one a.val).testBit y.val = decide (∃ j : Fin 5, a + D j = y) := by
  decide

theorem one_lt : ∀ a : Fin 21, one a.val < 2 ^ 21 := by decide

def ofB (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ofB f n ||| (if f n then 2 ^ n else 0)

theorem testBit_ofB (f : ℕ → Bool) (j : ℕ) :
    ∀ n, (ofB f n).testBit j = (decide (j < n) && f j) := by
  intro n
  induction n with
  | zero => simp [ofB]
  | succ n ih =>
    rw [ofB, Nat.testBit_or, ih]
    by_cases h : j = n
    · subst h
      cases hf : f j <;> simp
    · have h1 : decide (j < n + 1) = decide (j < n) := by
        rw [decide_eq_decide]; omega
      have h2 : (if f n then 2 ^ n else 0).testBit j = false := by
        cases f n
        · simp
        · simp [Ne.symm h]
      rw [h1, h2, Bool.or_false]

def imgL (S : ℕ) : List (Fin 21) → ℕ
  | [] => 0
  | a :: l => if S.testBit a.val then imgL S l ||| one a.val else imgL S l

def img (S : ℕ) : ℕ := imgL S (List.finRange 21)

theorem testBit_imgL (S j : ℕ) : ∀ l : List (Fin 21),
    (imgL S l).testBit j = true ↔ ∃ a ∈ l, S.testBit a.val = true ∧ (one a.val).testBit j = true := by
  intro l
  induction l with
  | nil => simp [imgL]
  | cons a l ih =>
    rw [imgL]
    by_cases h : S.testBit a.val = true
    · rw [if_pos h, Nat.testBit_or, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨b, hb, h1, h2⟩ | h2)
        · exact ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩
        · exact ⟨a, List.mem_cons_self, h, h2⟩
      · rintro ⟨b, hb, h1, h2⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inr h2
        · exact Or.inl ⟨b, hb, h1, h2⟩
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨b, hb, h1, h2⟩
        exact ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩
      · rintro ⟨b, hb, h1, h2⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact absurd h1 h
        · exact ⟨b, hb, h1, h2⟩

theorem testBit_img (S : ℕ) (y : Fin 21) :
    (img S).testBit y.val = true ↔ ∃ b : Fin 21, S.testBit b.val = true ∧ ∃ j : Fin 5, b + D j = y := by
  rw [img, testBit_imgL]
  constructor
  · rintro ⟨a, _, h1, h2⟩
    rw [one_spec a y, decide_eq_true_eq] at h2
    exact ⟨a, h1, h2⟩
  · rintro ⟨a, h1, h2⟩
    refine ⟨a, List.mem_finRange a, h1, ?_⟩
    rw [one_spec a y, decide_eq_true_eq]
    exact h2

theorem img_high (S j : ℕ) (hj : 21 ≤ j) : (img S).testBit j = false := by
  rw [← Bool.not_eq_true, img, testBit_imgL]
  rintro ⟨a, _, _, h⟩
  have : one a.val < 2 ^ j :=
    lt_of_lt_of_le (one_lt a) (Nat.pow_le_pow_right (by omega) hj)
  rw [Nat.testBit_lt_two_pow this] at h
  exact Bool.false_ne_true h

def rot (c s : ℕ) : ℕ := ofB (fun y => c.testBit ((y + 21 - s) % 21)) 21

def inc : List ℕ → Bool
  | a :: b :: r => decide (a < b) && inc (b :: r)
  | _ => true

theorem inc_pairwise : ∀ l : List ℕ, inc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ _
  | a :: b :: r, h => by
    rw [inc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := inc_pairwise (b :: r) h.2
    refine List.pairwise_cons.mpr ⟨?_, ih⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 ((List.pairwise_cons.mp ih).1 x hx)

def reps : List ℕ := [16, 48, 80, 112, 144, 176, 208, 240, 272, 336, 304, 368,
  400, 464, 432, 496, 528, 656, 560, 688, 592, 720, 624, 752,
  65568, 65552, 65584, 65792, 65824, 65856, 65616, 65808, 65872, 65632, 65888, 65648,
  65840, 65904, 66048, 66176, 65696, 66080, 66208, 65680, 66064, 66192, 65712, 66096,
  66224, 784, 848, 65920, 66304, 66432, 65952, 66336, 66464, 65728, 65984, 65744,
  66112, 66128, 66320, 65936, 66240, 66368, 912, 976, 65760, 66016, 65776, 66144,
  66160, 816, 66352, 66400, 944, 880, 1040, 1072, 1104, 1296, 1360, 1136,
  1328, 1392, 1168, 1200, 1232, 1264, 1424, 1456, 1488, 1520, 131152, 131120,
  131184, 131600, 131664, 131216, 131280, 131728, 131792, 131248, 131312, 131632, 131696, 131760,
  131824, 66592, 66576, 66608, 131344, 131408, 132112, 132176, 132368, 132432, 196896, 197632,
  197664, 66816, 197888, 66848, 197920, 196928, 196688, 196880, 196944, 196704, 196960, 196656,
  197648, 66624, 197696, 66656, 132144, 66640, 66672, 131376, 196912, 66832, 197904, 66880,
  66912, 132400, 66896, 66864, 1552, 66688, 66720, 67072, 67104, 67200, 67232, 66704,
  66736, 1584, 67088, 67120, 1680, 1712, 67216, 67248, 131856, 131920, 132624, 1616,
  132688, 1808, 132880, 1872, 132944, 197120, 197376, 197248, 197504, 196768, 197024, 197760,
  197792, 197152, 198144, 198176, 197408, 66944, 198016, 198272, 67328, 67360, 67456, 66976,
  197056, 196752, 196816, 197136, 197184, 197200, 197392, 131472, 197008, 197312, 131984, 131536,
  196832, 197088, 132240, 197776, 66752, 197824, 132272, 66768, 66784, 197168, 67136, 198208,
  67168, 132656, 67152, 1648, 131888, 197424, 132496, 66960, 198032, 67264, 198336, 67392,
  67424, 1936, 1840, 1744, 1776, 322, 274, 338, 290, 354, 306, 370,
  418, 450, 402, 466, 482, 434, 498, 2114, 2128, 2130, 2146, 2160,
  2162, 530, 2578, 642, 546, 674, 658, 2178, 2210, 2224, 562, 2608,
  2194, 2690, 2594, 690, 578, 594, 2626, 2640, 2642, 706, 722, 2242,
  2274, 2256, 2288, 610, 626, 2754, 2658, 2768, 738, 65554, 67616, 67618,
  67600, 67632, 65586, 67602, 67634, 2306, 2370, 2322, 2384, 2386, 65826, 65858,
  65618, 65810, 65874, 67680, 65634, 67872, 67842, 67650, 2338, 67904, 2402, 67664,
  67696, 65650, 67856, 2352, 67888, 67858, 2354, 67920, 2416, 66050, 66178, 65698,
  66082, 66210, 66066, 65682, 66194, 67712, 67744, 67714, 67746, 67728, 67760, 66098,
  68128, 68112, 68144, 67730, 68098, 68224, 68226, 68130, 68240, 65714, 834, 786,
  850, 2818, 2882, 2834, 2896, 2898, 66306, 898, 66434, 65954, 802, 66338,
  930, 66466, 65730, 65986, 66114, 66130, 65938, 66242, 66370, 914, 962, 67776,
  67808, 2434, 67968, 67970, 67778, 2466, 68032, 2498, 67792, 67824, 66146, 66162,
  68352, 68384, 2864, 68368, 68400, 2450, 67984, 67986, 68162, 68288, 68290, 2850,
  68416, 866, 818, 2512, 882, 262224, 262226, 262338, 262352, 262354, 262242, 262370,
  262256, 262384, 262258, 262386, 1074, 1090, 1106, 1298, 1346, 1362, 1122, 1138,
  1378, 1330, 1394, 263186, 263202, 263298, 1186, 263330, 263216, 263312, 263344, 263218,
  1170, 263314, 1202, 263346, 263426, 262466, 262416, 262418, 262480, 262482, 263248, 263234,
  263250, 263440, 263442, 263490, 263504, 263506, 262434, 262562, 1410, 263554, 263458, 1442,
  263586, 262594, 262544, 262546, 262608, 262610, 262498, 262626, 263280, 263376, 263408, 263266,
  263282, 262448, 1426, 263568, 263570, 1218, 263522, 1458, 263632, 1234, 131170, 133154,
  133218, 133168, 133232, 131122, 131186, 133170, 133234, 264720, 264210, 264706, 264722, 262786,
  262690, 262818, 262800, 262802, 264322, 264226, 264354, 264240, 264336, 264368, 262704, 262706,
  264752, 264338, 264738, 264848, 262832, 393296, 393744, 393234, 131650, 262722, 131602, 262736,
  131666, 395266, 264258, 395330, 395280, 264272, 395344, 133648, 395792, 395282, 133634, 133698,
  264770, 133650, 264784, 133712, 131714, 393858, 393250, 131234, 393378, 131618, 393762, 131746,
  393890, 131266, 393410, 393360, 393424, 131218, 393362, 131778, 131730, 262864, 131282, 393314,
  395394, 133314, 264290, 133282, 131298, 393328, 395312, 133264, 395408, 133296, 264400, 133328,
  393776, 262754, 131634, 131682, 133680, 395824, 133266, 395410, 133762, 133826, 264802, 131250,
  264912, 131314, 68624, 68640, 3120, 68656, 66578, 66610, 68626, 68642, 3122, 68658,
  132354, 131394, 131346, 131410, 133378, 133442, 134160, 3152, 134224, 132114, 132162, 132178,
  3346, 134210, 3394, 3408, 3154, 196642, 131362, 196898, 132130, 197666, 66818, 197890,
  66850, 132386, 197922, 196930, 196626, 196690, 196882, 196946, 198752, 196706, 198912, 198944,
  198914, 198722, 133410, 131426, 198672, 198704, 199696, 199744, 68704, 134192, 68688, 3184,
  197650, 197698, 66658, 132146, 66642, 198928, 133424, 198960, 68864, 68866, 68880, 66834,
  199746, 68928, 3170, 3376, 68944, 3186, 265218, 265234, 265730, 3602, 265744, 265746,
  328320, 328322, 327840, 327714, 327842, 328832, 328864, 328706, 329216, 67106, 328834, 1666,
  67202, 1698, 329344, 66722, 327824, 327698, 328210, 327826, 328336, 328338, 329888, 329730,
  329858, 329762, 329890, 328752, 329776, 330752, 68752, 330784, 3248, 68768, 328240, 328722,
  1586, 329232, 67090, 330240, 330272, 330256, 330288, 330754, 3218, 66706, 3714, 69248,
  69250, 331264, 69152, 1682, 69136, 66738, 263938, 132866, 395010, 393538, 262928, 394000,
  393490, 262978, 131858, 262992, 131906, 264450, 395522, 264514, 395586, 394320, 396304, 265296,
  396368, 394258, 132674, 263746, 132626, 263760, 1618, 133904, 264976, 396048, 265474, 265488,
  264466, 134658, 134722, 1858, 1810, 3664, 1874, 131970, 328576, 197378, 458912, 458786,
  327968, 459040, 327970, 131490, 196770, 459904, 459936, 459778, 198146, 132642, 197154, 328480,
  459552, 328960, 328962, 132482, 329088, 66946, 132738, 198274, 329472, 67330, 1922, 329600,
  66978]

def codes : List ℕ := reps.map img

def good (c : ℕ) : Bool := (List.range 20).all fun s => decide (c < rot c (s + 1))

set_option maxRecDepth 100000 in
theorem reps_length : reps.length = 781 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem codes_inc : inc codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem codes_good : codes.all good = true := by decide +kernel

def pick (k : ℕ) : Finset (Fin 21) :=
  Finset.univ.filter fun a : Fin 21 => (reps.getD (k / 21) 0).testBit (a - Fin.ofNat 21 (k % 21)).val

theorem image_spec (k : ℕ) (y : Fin 21) :
    (∃ a ∈ pick k, ∃ j : Fin 5, a + D j = y) ↔
      (img (reps.getD (k / 21) 0)).testBit (y - Fin.ofNat 21 (k % 21)).val = true := by
  rw [testBit_img]
  constructor
  · rintro ⟨a, ha, j, hj⟩
    unfold pick at ha
    refine ⟨a - Fin.ofNat 21 (k % 21), (Finset.mem_filter.mp ha).2, j, ?_⟩
    rw [← hj]; abel
  · rintro ⟨b, hb, j, hj⟩
    refine ⟨b + Fin.ofNat 21 (k % 21), ?_, j, ?_⟩
    · unfold pick
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [add_sub_cancel_right]; exact hb
    · rw [add_right_comm, hj, sub_add_cancel]

theorem main : Function.Injective fun (k : Fin 16385) (y : Fin 21) =>
    ∃ a ∈ pick k.val, ∃ j : Fin 5, a + D j = y := by
  intro k l h
  have hi : k.val / 21 < codes.length := by
    rw [codes, List.length_map, reps_length]; omega
  have hj : l.val / 21 < codes.length := by
    rw [codes, List.length_map, reps_length]; omega
  have code : ∀ m : ℕ, ∀ hm : m < codes.length, codes[m] = img (reps.getD m 0) := by
    intro m hm
    have hm' : m < reps.length := by simpa [codes] using hm
    rw [List.getD_eq_getElem _ _ hm']
    simp [codes]
  set s : Fin 21 := Fin.ofNat 21 (k.val % 21) with hs
  set t : Fin 21 := Fin.ofNat 21 (l.val % 21) with ht
  have hb : ∀ y : Fin 21, (codes[k.val / 21]).testBit (y - s).val
      = (codes[l.val / 21]).testBit (y - t).val := by
    intro y
    rw [code _ hi, code _ hj, Bool.eq_iff_iff, hs, ht, ← image_spec, ← image_spec]
    exact iff_of_eq (congrFun h y)
  have hrot : ∀ (m m' : ℕ) (hm : m < codes.length) (hm' : m' < codes.length) (u v : Fin 21),
      (∀ y : Fin 21, (codes[m]).testBit (y - u).val = (codes[m']).testBit (y - v).val) →
      u ≠ v → codes[m] < codes[m'] := by
    intro m m' hm hm' u v hbit huv
    have hd : (u - v).val ≠ 0 := by
      intro hc
      have : u - v = 0 := Fin.ext hc
      exact huv (sub_eq_zero.mp this)
    have e : rot (codes[m]) (u - v).val = codes[m'] := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [rot, testBit_ofB]
      by_cases hj21 : j < 21
      · have key := hbit (⟨j, hj21⟩ + v)
        have e1 : (⟨j, hj21⟩ + v - v : Fin 21) = ⟨j, hj21⟩ := add_sub_cancel_right _ _
        have e2 : (⟨j, hj21⟩ + v - u : Fin 21) = ⟨j, hj21⟩ - (u - v) := by abel
        rw [e1, e2] at key
        have e3 : (⟨j, hj21⟩ - (u - v) : Fin 21).val = (j + 21 - (u - v).val) % 21 := by
          rw [Fin.val_sub]
          have := (u - v).isLt
          congr 1
          show 21 - (u - v).val + j = j + 21 - (u - v).val
          omega
        rw [e3] at key
        rw [decide_eq_true hj21, Bool.true_and]
        exact key
      · rw [decide_eq_false hj21, Bool.false_and, code _ hm', img_high _ _ (by omega)]
    have g := List.all_eq_true.mp codes_good (codes[m]) (List.getElem_mem hm)
    have := List.all_eq_true.mp g ((u - v).val - 1)
      (List.mem_range.mpr (by have := (u - v).isLt; omega))
    rw [decide_eq_true_eq] at this
    have e4 : (u - v).val - 1 + 1 = (u - v).val := by omega
    rw [e4, e] at this
    exact this
  have hst : s = t := by
    by_contra hne
    have h1 := hrot _ _ hi hj s t hb hne
    have h2 := hrot _ _ hj hi t s (fun y => (hb y).symm) (Ne.symm hne)
    omega
  have hidx : k.val / 21 = l.val / 21 := by
    have hc : codes[k.val / 21] = codes[l.val / 21] := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj21 : j < 21
      · have := hb (⟨j, hj21⟩ + s)
        rw [← hst] at this
        have e1 : (⟨j, hj21⟩ + s - s : Fin 21) = ⟨j, hj21⟩ := add_sub_cancel_right _ _
        rw [e1] at this
        exact this
      · rw [code _ hi, code _ hj, img_high _ _ (by omega), img_high _ _ (by omega)]
    have nd : codes.Nodup := (inc_pairwise _ codes_inc).imp fun h => Nat.ne_of_lt h
    exact (List.Nodup.getElem_inj_iff nd).mp hc
  have hmod : k.val % 21 = l.val % 21 := by
    have := congrArg Fin.val hst
    simpa [hs, ht, Fin.ofNat, Nat.mod_mod] using this
  apply Fin.ext
  omega

end PEqualNP.Outside.L_meta_17775

theorem PEqualNP.Outside.L_meta_17775 : (∃ (x1 : Fin (16385 : ℕ) → Finset (Fin (21 : ℕ))), Function.Injective fun (x2 : Fin (16385 : ℕ)) (x3 : Fin (21 : ℕ)) => ∃ x4 ∈ x1 x2, ∃ (x5 : Fin (5 : ℕ)), x4 + ![(20 : Fin (21 : ℕ)), (0 : Fin (21 : ℕ)), (5 : Fin (21 : ℕ)), (7 : Fin (21 : ℕ)), (17 : Fin (21 : ℕ))] x5 = x3) := by
  exact ⟨fun k => PEqualNP.Outside.L_meta_17775.pick k.val, PEqualNP.Outside.L_meta_17775.main⟩
