import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6897

abbrev Word := Fin 62 → Bool

def blank : Word := fun _ => false

def disj (a b : Word) : Word := fun i => a i || b i

def conj (a b : Word) : Word := fun i =>
  if i = 60 then a 58 && b 60 || a 60 && b 58
  else if i = 61 then a 59 && b 61 || a 61 && b 59
  else a i && b i

def square (a : Word) : Word := fun i => a i && (decide (i.val < 60) || a (i - 2))

lemma conj_self (a : Word) : conj a a = square a := by
  funext i
  by_cases h : i = 60
  · subst i
    change (a 58 && a 60 || a 60 && a 58) = (a 60 && (false || a 58))
    cases a 58 <;> cases a 60 <;> rfl
  by_cases h' : i = 61
  · subst i
    change (a 59 && a 61 || a 61 && a 59) = (a 61 && (false || a 59))
    cases a 59 <;> cases a 61 <;> rfl
  have hi : i.val < 60 := by
    have := i.isLt
    by_contra hn
    have hi : i.val = 60 ∨ i.val = 61 := by omega
    exact hi.elim (fun e => h (Fin.ext e)) (fun e => h' (Fin.ext e))
  simp [conj, square, h, h', hi]

lemma disj_self (a : Word) : disj a a = a := by
  funext i
  simp [disj]

def calcBy (w : List Word) (p q : ℕ) (b : Bool) : Word :=
  if b then conj (w.getD p blank) (w.getD q blank)
  else disj (w.getD p blank) (w.getD q blank)

lemma calc_swap (w : List Word) (p q : ℕ) (b : Bool) :
    calcBy w p q b = calcBy w q p b := by
  cases b
  · funext i; simp [calcBy, disj, Bool.or_comm]
  · funext i; simp [calcBy, conj, Bool.and_comm, Bool.or_comm]

def parent (w : List Word) (m i : ℕ) (y : Word) :=
  ∃ p < i, ∃ q < i, ∃ b : Bool, p ≠ q ∧ (b = true → m < i) ∧ calcBy w p q b = y

def valid (base : List Word) (goal : Word) (gs : List Word) :=
  goal ∈ gs ∧ ∀ i < gs.length,
    parent (base ++ gs) base.length (base.length + i) (gs.getD i blank)

def shiftDown (d i : ℕ) : ℕ := if i < d then i else i - 1

lemma shift_ne {d p q : ℕ} (hp : p ≠ d) (hq : q ≠ d) (hne : p ≠ q) :
    shiftDown d p ≠ shiftDown d q := by
  unfold shiftDown
  split <;> split <;> omega

lemma shift_lt {d k p : ℕ} (hk : k ≠ d) (hp : p ≠ d) (h : p < k) :
    shiftDown d p < shiftDown d k := by
  unfold shiftDown
  split <;> split <;> omega

lemma get_shift (w : List Word) {d i : ℕ} (h : i ≠ d) :
    (w.eraseIdx d).getD (shiftDown d i) blank = w.getD i blank := by
  simp only [shiftDown, List.getD_eq_getElem?_getD]
  by_cases hi : i < d
  · rw [if_pos hi, List.getElem?_eraseIdx_of_lt hi]
  · rw [if_neg hi, List.getElem?_eraseIdx_of_ge (show d ≤ i - 1 by omega),
      show i - 1 + 1 = i by omega]

lemma repair {base gs : List Word} {goal : Word} (hv : valid base goal gs)
    {d a : ℕ} (hd : d < gs.length) (hd0 : 0 < d) (ha : a < base.length + d)
    (he : (base ++ gs).getD a blank = gs.getD d blank)
    (hgoal : goal ∉ base)
    (hhelp : (∃ c < base.length + d, c ≠ a ∧ (base ++ gs).getD c blank = gs.getD d blank)
      ∨ ¬ (square (gs.getD d blank) ≠ gs.getD d blank ∧ square (gs.getD d blank) ∈ gs)) :
    valid base goal (gs.eraseIdx d) := by
  let w := base ++ gs
  let D := base.length + d
  have cutW : base ++ gs.eraseIdx d = w.eraseIdx D := by
    simp [w, D, List.eraseIdx_append_of_length_le]
  have sameD : w.getD D blank = gs.getD d blank := by
    dsimp [w, D]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have eqA : w.getD a blank = w.getD D blank := he.trans sameD.symm
  have shrink : (gs.eraseIdx d).length + 1 = gs.length := List.length_eraseIdx_add_one hd
  constructor
  · apply List.mem_eraseIdx_iff_getElem.mpr
    have hchoose := List.mem_iff_getElem.mp hv.1
    obtain ⟨i, hi, heq⟩ := hchoose
    by_cases hi' : i = d
    · subst i
      have eqD : w.getD D blank = goal := by
        rw [sameD, List.getD_eq_getElem _ _ hd, heq]
      have hwa : w.getD a blank = goal := eqA.trans eqD
      by_cases h : a < base.length
      · change (base ++ gs).getD a blank = goal at hwa
        rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h] at hwa
        exact (hgoal (hwa ▸ List.getElem_mem h)).elim
      · change (base ++ gs).getD a blank = goal at hwa
        rw [List.getD_append_right _ _ _ _ (by omega)] at hwa
        have hlt : a - base.length < gs.length := by omega
        rw [List.getD_eq_getElem _ _ hlt] at hwa
        exact ⟨a - base.length, hlt, by omega, hwa⟩
    · exact ⟨i, hi, hi', heq⟩
  intro i hi
  let j := if i < d then i else i + 1
  have hj : j < gs.length := by dsimp [j]; split <;> omega
  have hjd : j ≠ d := by dsimp [j]; split <;> omega
  have align : shiftDown D (base.length + j) = base.length + i := by
    dsimp [j, D, shiftDown]
    split <;> split <;> omega
  have yEq : (gs.eraseIdx d).getD i blank = gs.getD j blank := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx, j]
    split <;> rfl
  have choose (p q : ℕ) (b : Bool) (hp : p < base.length + j) (hq : q < base.length + j)
      (hdp : p ≠ D) (hdq : q ≠ D) (hn : p ≠ q)
      (hb : b = true → 0 < i) (heq : calcBy w p q b = gs.getD j blank) :
      parent (base ++ gs.eraseIdx d) base.length (base.length + i) ((gs.eraseIdx d).getD i blank) := by
    refine ⟨shiftDown D p, align ▸ shift_lt (by dsimp [D]; omega) hdp hp,
      shiftDown D q, align ▸ shift_lt (by dsimp [D]; omega) hdq hq, b,
      shift_ne hdp hdq hn, (fun h => by have := hb h; omega), ?_⟩
    simpa only [cutW, yEq, calcBy, get_shift w hdp, get_shift w hdq] using heq
  obtain ⟨p, hp, q, hq, b, hneq, hb, hc⟩ := hv.2 j hj
  change calcBy w p q b = _ at hc
  have anyOp : b = true → 0 < i := by
    intro h
    have hn := hb h
    dsimp [j] at hn
    split at hn <;> omega
  have redirect (u : ℕ) (hu : u < base.length + j) (hD : D < base.length + j) (hn : u ≠ D)
      (hy : calcBy w D u b = gs.getD j blank) :
      parent (base ++ gs.eraseIdx d) base.length (base.length + i) ((gs.eraseIdx d).getD i blank) := by
    by_cases hua : u = a
    · subst u
      rcases hhelp with ⟨c, hcd, hca, hcval⟩ | hsquare
      · have hec : w.getD c blank = w.getD D blank := hcval.trans sameD.symm
        apply choose c a b (by omega) (by omega) (by omega) (by omega) hca anyOp
        simpa only [calcBy, hec] using hy
      · have sameResult : gs.getD j blank = gs.getD d blank := by
          cases b
          · simpa only [calcBy, Bool.false_eq_true, if_false, eqA, disj_self, sameD] using hy.symm
          · have hs : square (gs.getD d blank) = gs.getD j blank := by
              simpa only [calcBy, if_true, eqA, conj_self, sameD] using hy
            apply Classical.byContradiction
            intro hne
            apply hsquare
            refine ⟨fun h => hne (hs.symm.trans h), ?_⟩
            rw [hs, List.getD_eq_getElem _ _ hj]
            exact List.getElem_mem hj
        obtain ⟨r, hr, s, hs, c, hdist, _, hval⟩ := hv.2 d hd
        have hij : 0 < i := by
          dsimp [j, D] at hD
          split at hD <;> omega
        exact choose r s c (by omega) (by omega) (by omega) (by omega) hdist
          (fun _ => hij) (sameResult ▸ hval)
    · apply choose a u b (by omega) hu (by omega) hn (fun h => hua h.symm) anyOp
      simpa only [calcBy, eqA] using hy
  by_cases hpd : p = D
  · subst p
    exact redirect q hq hp hneq.symm hc
  by_cases hqd : q = D
  · subst q
    exact redirect p hp hq hneq ((calc_swap w D p b).trans hc)
  exact choose p q b hp hq hpd hqd hneq anyOp hc

def positions (w : List Word) (v : Word) : List ℕ :=
  (List.range w.length).filter fun i => w.getD i blank == v

lemma positions_count (w : List Word) (v : Word) : (positions w v).length = w.count v := by
  have hm : (List.range w.length).map (fun i => w.getD i blank) = w := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hi']
  calc
    (positions w v).length = (List.range w.length).countP (fun i => w.getD i blank == v) := by
      rw [positions, List.countP_eq_length_filter]
    _ = ((List.range w.length).map fun i => w.getD i blank).count v := by
      rw [List.count_eq_countP, List.countP_map]
      rfl
    _ = w.count v := by rw [hm]

lemma positions_data (w : List Word) (v : Word) (i : ℕ) (hi : i < (positions w v).length) :
    let j := (positions w v)[i]
    j < w.length ∧ w.getD j blank = v := by
  have hm := List.getElem_mem (l := positions w v) hi
  simpa only [positions, List.mem_filter, List.mem_range, beq_iff_eq] using hm

lemma positions_order (w : List Word) (v : Word) {i j : ℕ}
    (hi : i < (positions w v).length) (hj : j < (positions w v).length) (hij : i < j) :
    (positions w v)[i] < (positions w v)[j] := by
  have hr : (List.range w.length).Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro a b _ _ hab
    simpa only [List.getElem_range] using hab
  exact List.pairwise_iff_getElem.mp (hr.sublist List.filter_sublist) i j hi hj hij

def inputWords : List Word := List.map (fun x : ℕ => fun i : Fin 62 => x.testBit i.val)
  [2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696,
    54820275478360064, 3870282840506368, 133412159488, 1911954591369396745,
    218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114,
    270286071509155872, 288160007408582916]

def targetWord : Word := fun i => decide (i.val < 21)

lemma target_outside : targetWord ∉ inputWords := by decide +kernel

lemma input_separates : ∀ a b : Fin inputWords.length, a ≠ b →
    ∃ k : Fin 62, (inputWords.getD a.val blank) k = true ∧
      (inputWords.getD b.val blank) k = false := by
  decide +kernel

lemma alias_in_gates (gs : List Word) {p q : ℕ} (hpq : p < q)
    (hval : (inputWords ++ gs).getD p blank = (inputWords ++ gs).getD q blank) :
    inputWords.length ≤ q := by
  by_contra! hq
  have hp : p < inputWords.length := hpq.trans hq
  rw [List.getD_append _ _ _ _ hp, List.getD_append _ _ _ _ hq] at hval
  obtain ⟨k, hk, hl⟩ := input_separates ⟨p,hp⟩ ⟨q,hq⟩ (fun e =>
    hpq.ne (congrArg Fin.val e))
  have clash := hk.symm.trans ((congrFun hval k).trans hl)
  contradiction

lemma positive_alias {gs : List Word} (hv : valid inputWords targetWord gs)
    {d a : ℕ} (hd : d < gs.length) (ha : a < inputWords.length + d)
    (he : (inputWords ++ gs).getD a blank = gs.getD d blank) : 0 < d := by
  by_contra! hd0
  have hd' : d = 0 := by omega
  subst d
  simp only [Nat.add_zero] at ha
  obtain ⟨p, hp, q, hq, b, hpq, hb, eq⟩ := hv.2 0 hd
  simp only [Nat.add_zero] at hp hq hb
  have bf : b = false := by
    cases b <;> simp_all
  simp only [bf, calcBy, Bool.false_eq_true, if_false] at eq
  rw [List.getD_append _ _ _ _ hp, List.getD_append _ _ _ _ hq] at eq
  rw [List.getD_append _ _ _ _ ha, ← eq] at he
  by_cases hpa : p = a
  · obtain ⟨k,hk,hl⟩ := input_separates ⟨q,hq⟩ ⟨a,ha⟩ (fun h =>
      hpq (hpa.trans (congrArg Fin.val h).symm))
    have hh := congrFun he k
    simp [disj, hk, hl] at hh
  · obtain ⟨k,hk,hl⟩ := input_separates ⟨p,hp⟩ ⟨a,ha⟩ (fun h => hpa (congrArg Fin.val h))
    have hh := congrFun he k
    simp [disj, hk, hl] at hh

lemma improve (gs : List Word) (hv : valid inputWords targetWord gs) :
    ∃ out : List Word, out.length ≤ gs.length ∧ valid inputWords targetWord out ∧
      ∀ v : Word, (inputWords ++ out).count v ≤ 2 ∧
        (1 < (inputWords ++ out).count v → square v ≠ v ∧ square v ∈ out) := by
  classical
  let P (n : ℕ) := ∃ ws : List Word, ws.length = n ∧ valid inputWords targetWord ws
  have hex : ∃ n, P n := ⟨gs.length, gs, rfl, hv⟩
  obtain ⟨out, hout, hvalid⟩ := Nat.find_spec hex
  have hmin : ∀ ws : List Word, valid inputWords targetWord ws → out.length ≤ ws.length :=
    fun ws h => hout.trans_le (Nat.find_min' hex ⟨ws, rfl, h⟩)
  refine ⟨out, hmin gs hv, hvalid, ?_⟩
  intro v
  let w := inputWords ++ out
  let is := positions w v
  have shorter (p q : ℕ) (hpq : p < q) (hq : q < w.length)
      (hpval : w.getD p blank = v) (hqval : w.getD q blank = v)
      (hcase : (∃ c < q, c ≠ p ∧ w.getD c blank = v) ∨ ¬ (square v ≠ v ∧ square v ∈ out)) : False := by
    have hbase := alias_in_gates out hpq (hpval.trans hqval.symm)
    let d := q - inputWords.length
    have hd : d < out.length := by
      dsimp [w] at hq
      simp only [List.length_append] at hq
      dsimp [d]
      omega
    have e : inputWords.length + d = q := by dsimp [d]; omega
    have hdval : out.getD d blank = v := by
      dsimp [w] at hqval
      rwa [List.getD_append_right _ _ _ _ hbase] at hqval
    have ha : p < inputWords.length + d := by omega
    have halias := hpval.trans hdval.symm
    have hnew := repair hvalid hd (positive_alias hvalid hd ha halias) ha halias target_outside
      (by simpa only [e, hdval] using hcase)
    have hle := hmin _ hnew
    have hs := List.length_eraseIdx_add_one hd
    omega
  constructor
  · by_contra! hbig
    have h2 : 2 < is.length := by simpa [is, positions_count, w] using hbig
    have h0 : 0 < is.length := by omega
    have h1 : 1 < is.length := by omega
    have a := positions_data w v 0 h0
    have b := positions_data w v 1 h1
    have c := positions_data w v 2 h2
    have ac := positions_order w v h0 h2 (by decide : (0 : ℕ) < 2)
    have bc := positions_order w v h1 h2 (by decide : (1 : ℕ) < 2)
    have ab := positions_order w v h0 h1 (by decide : (0 : ℕ) < 1)
    exact shorter _ _ ac c.1 a.2 c.2 (Or.inl ⟨_, bc, ab.ne.symm, b.2⟩)
  · intro hcount
    by_contra hs
    have h1 : 1 < is.length := by simpa [is, positions_count, w] using hcount
    have h0 : 0 < is.length := by omega
    have a := positions_data w v 0 h0
    have b := positions_data w v 1 h1
    have ab := positions_order w v h0 h1 (by decide : (0 : ℕ) < 1)
    exact shorter _ _ ab b.1 a.2 b.2 (Or.inr hs)

end PEqualNP.Outside.L_meta_6897

set_option maxHeartbeats 600000 in
open PEqualNP.Outside.L_meta_6897 in
theorem PEqualNP.Outside.L_meta_6897 :
have x1 : List (Fin (62 : ℕ) → Bool) := List.map (fun (x1 : ℕ) (x2 : Fin (62 : ℕ)) => x1.testBit ↑x2) [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]; have x2 : List (Fin (62 : ℕ) → Bool) → Prop := fun (x2 : List (Fin (62 : ℕ) → Bool)) =>   (fun (x3 : Fin (62 : ℕ)) => Decidable.decide (↑x3 < (21 : ℕ))) ∈ x2 ∧     ∀ x3 < x2.length,       ∃ (x5 : ℕ) (x6 : ℕ),         x5 ≠ x6 ∧           x5 < (14 : ℕ) + x3 ∧             x6 < (14 : ℕ) + x3 ∧               have x7 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x5 fun (x7 : Fin (62 : ℕ)) => Bool.false;               have x8 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x6 fun (x8 : Fin (62 : ℕ)) => Bool.false;               ((x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => x7 x9 || x8 x9) ∨ (0 : ℕ) < x3 ∧ (x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => if x9 = (60 : Fin (62 : ℕ)) then x7 (58 : Fin (62 : ℕ)) && x8 (60 : Fin (62 : ℕ)) || x7 (60 : Fin (62 : ℕ)) && x8 (58 : Fin (62 : ℕ)) else if x9 = (61 : Fin (62 : ℕ)) then x7 (59 : Fin (62 : ℕ)) && x8 (61 : Fin (62 : ℕ)) || x7 (61 : Fin (62 : ℕ)) && x8 (59 : Fin (62 : ℕ)) else x7 x9 && x8 x9; ∀ (x3 : List (Fin (62 : ℕ) → Bool)),   x2 x3 →     ∃ (x5 : List (Fin (62 : ℕ) → Bool)),       x5.length ≤ x3.length ∧         x2 x5 ∧           ∀ (x6 : Fin (62 : ℕ) → Bool),             have x7 : ℕ := List.count x6 (x1 ++ x5);             x7 ≤ (2 : ℕ) ∧ ((1 : ℕ) < x7 → ∃ x9 ∈ x5, x9 ≠ x6 ∧ x9 = fun (x10 : Fin (62 : ℕ)) => x6 x10 && (Decidable.decide (↑x10 < (60 : ℕ)) || x6 (x10 - (2 : Fin (62 : ℕ))))) := by
  intro base admissible gs hv
  have baseLen : base.length = 14 := rfl
  have baseEq : base = inputWords := rfl
  have bridge (cs : List Word) : admissible cs ↔ valid base targetWord cs := by
    constructor
    · rintro ⟨ht, hg⟩
      refine ⟨ht, fun i hi => ?_⟩
      obtain ⟨a, b, hne, ha, hb, hop⟩ := hg i hi
      rw [← baseLen] at ha hb
      rcases hop with hor | ⟨hpos, hand⟩
      · exact ⟨a, ha, b, hb, false, hne, by simp, hor.symm⟩
      · exact ⟨a, ha, b, hb, true, hne, (fun _ => by omega), hand.symm⟩
    · rintro ⟨ht, hg⟩
      refine ⟨ht, fun i hi => ?_⟩
      obtain ⟨a, ha, b, hb, op, hne, hpos, eq⟩ := hg i hi
      rw [baseLen] at ha hb
      refine ⟨a, b, hne, ha, hb, ?_⟩
      cases op
      · exact Or.inl eq.symm
      · have h := hpos rfl
        exact Or.inr ⟨by omega, eq.symm⟩
  have hinput := (bridge gs).mp hv
  rw [baseEq] at hinput
  obtain ⟨out, hle, ok, hfreq⟩ := improve gs hinput
  refine ⟨out, hle, (bridge out).mpr (baseEq.symm ▸ ok), fun v => ?_⟩
  rw [baseEq]
  exact ⟨(hfreq v).1, fun ht => ⟨square v, (hfreq v).2 ht |>.2,
    (hfreq v).2 ht |>.1, rfl⟩⟩
