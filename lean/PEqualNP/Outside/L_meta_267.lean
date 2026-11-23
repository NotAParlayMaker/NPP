import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta267

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One bit for each two-vertex assignment, in lexicographic order.
private abbrev T := BitVec 15
private def ins : List T := [31, 481, 3618, 12868, 21640, 26896]
private def target : T := 28707

private def plus (ws : List T) (a : T) : List T :=
  ws ++ ws.map (fun x => x ||| a)

private def base : List T := (ins.foldl plus [0, -1]).eraseDups

private def meets (a b : T) : Bool := a &&& b == a
private def safePart (a : T) : T := if meets a target then a else 0

-- This is the largest union of sources that avoids all forbidden bits.
private def allowed (ws : List T) (bad : T) : T :=
  ws.foldr (fun a acc => if a &&& bad == 0 then a ||| acc else acc) 0

private def ands (ws : List T) : List T :=
  ws.flatMap (fun a => ws.map (fun b => a &&& b))

-- Independent conjunctions can both be maximized by fixing their left operands.
private def independentFound (ws options : List T) (need : T) : Bool :=
  let products := (options.map (fun v => v &&& allowed ws (v &&& ~~~target))).eraseDups
  products.any (fun x => products.any (fun y => meets need (x ||| y)))

-- For v AND (u OR (x AND y)), the maximal safe u leaves only the residual positives to x AND y.
private def dependentFound (ws options : List T) (need : T) : Bool :=
  options.any (fun v =>
    meets need v &&
    (let bad := v &&& ~~~target
     let remaining := need &&& ~~~(allowed ws bad)
     options.any (fun x => meets remaining x &&
       meets remaining (allowed ws (x &&& bad)))))

private def checkFirst (a : T) : Bool :=
  let ab := (plus base a).eraseDups
  let ws := a :: -1 :: ins
  let need := target &&& ~~~(safePart a)
  !(independentFound ws ab need || dependentFound ws ab need)

private def bit (i : Fin 15) (a : T) : Bool := a[i.val]
private def Sub (a b : T) : Prop := ∀ i, bit i a = true → bit i b = true

private theorem meets_iff (a b : T) : meets a b = true ↔ Sub a b := by
  simp only [meets, beq_iff_eq]
  constructor
  · intro h i hi
    have e := congrArg (bit i) h
    change a[i.val] = true at hi
    simpa only [bit, BitVec.getElem_and, hi, Bool.true_and] using e
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    rw [BitVec.getElem_and]
    cases e : a[i] with
    | false => simp
    | true =>
      have eb : b[i] = true := h ⟨i, hi⟩ e
      simp [eb]

private theorem sub_refl (a : T) : Sub a a := fun _ h => h
private theorem sub_trans {a b c : T} (h : Sub a b) (k : Sub b c) : Sub a c :=
  fun i hi => k i (h i hi)
private theorem sub_zero (a : T) : Sub 0 a := by simp [Sub, bit]
private theorem sub_or_left (a b : T) : Sub a (a ||| b) := by
  intro i h
  exact (show bit i a = true ∨ bit i b = true → bit i (a ||| b) = true by
    simp only [bit, BitVec.getElem_or, Bool.or_eq_true, imp_self]) (Or.inl h)
private theorem sub_or_right (a b : T) : Sub b (a ||| b) := by
  rw [BitVec.or_comm]
  exact sub_or_left _ _
private theorem sub_or {a b c : T} (h : Sub a c) (k : Sub b c) : Sub (a ||| b) c := by
  intro i hi
  rcases (by simpa only [bit, BitVec.getElem_or, Bool.or_eq_true] using hi :
    bit i a = true ∨ bit i b = true) with ha | hb
  · exact h i ha
  · exact k i hb

private theorem and_sub_left (a b : T) : Sub (a &&& b) a := by
  intro i hi
  exact (show bit i a = true ∧ bit i b = true by
    simpa only [bit, BitVec.getElem_and, Bool.and_eq_true] using hi).1

private theorem and_sub_right (a b : T) : Sub (a &&& b) b := by
  rw [BitVec.and_comm]
  exact and_sub_left _ _

private theorem sub_and {a b c : T} (h : Sub a b) (k : Sub a c) : Sub a (b &&& c) := by
  intro i hi
  simpa only [bit, BitVec.getElem_and, Bool.and_eq_true] using And.intro (h i hi) (k i hi)

private theorem sub_not_iff (a b : T) : a &&& ~~~b = 0 ↔ Sub a b := by
  constructor
  · intro ha i hi
    have e := congrArg (bit i) ha
    simp only [bit, BitVec.getElem_and, BitVec.getElem_not] at e
    change a[i.val] = true at hi
    simpa [bit, hi] using e
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases e : a[i] with
    | false => simp
    | true =>
      have eb : b[i] = true := h ⟨i, hi⟩ e
      simp [eb]

private theorem sub_intersection_zero {a b c : T} (hsub : Sub a b) (h : b &&& c = 0) :
    a &&& c = 0 := by
  have hsub' := (meets_iff _ _).2 hsub
  simp only [meets, beq_iff_eq] at hsub'
  rw [← hsub', BitVec.and_assoc, h]
  simp

private theorem allowed_bound (ws : List T) (bad : T) (a : T)
    (ha : a ∈ ws) (h : a &&& bad = 0) : Sub a (allowed ws bad) := by
  induction ws with
  | nil => simp at ha
  | cons b ws ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simpa [allowed, h] using sub_or_left a (allowed ws bad)
    · by_cases hb : b &&& bad = 0
      · simpa [allowed, hb] using sub_trans (ih ha) (sub_or_right b (allowed ws bad))
      · simpa only [allowed, List.foldr_cons, beq_iff_eq, ite_eq_right hb] using ih ha

private theorem plus_bound (ws : List T) (a bad val : T)
    (hw : ∀ z ∈ ws, z &&& bad = 0 → Sub z val) (ha : a &&& bad = 0 → Sub a val) :
    ∀ z ∈ plus ws a, z &&& bad = 0 → Sub z val := by
  intro z hz hz0
  rcases List.mem_append.mp hz with hz | hz
  · exact hw z hz hz0
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    rw [BitVec.and_or_distrib_right] at hz0
    obtain ⟨hy0, ha0⟩ := BitVec.or_eq_zero_iff.mp hz0
    exact sub_or (hw y hy hy0) (ha ha0)

private theorem foldl_bound (xs ws : List T) (bad val : T)
    (hw : ∀ z ∈ ws, z &&& bad = 0 → Sub z val)
    (hx : ∀ z ∈ xs, z &&& bad = 0 → Sub z val) :
    ∀ z ∈ xs.foldl plus ws, z &&& bad = 0 → Sub z val := by
  induction xs generalizing ws with
  | nil => exact hw
  | cons a xs ih =>
    exact ih (plus ws a) (plus_bound ws a bad val hw (hx a (by simp)))
      (fun z hz => hx z (by simp [hz]))

private theorem base_bound (bad val : T)
    (hn : (-1 : T) &&& bad = 0 → Sub (-1) val)
    (hi : ∀ z ∈ ins, z &&& bad = 0 → Sub z val) :
    ∀ z ∈ base, z &&& bad = 0 → Sub z val := by
  intro z hz
  have hinit : ∀ y ∈ ([0, -1] : List T), y &&& bad = 0 → Sub y val := by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · intro _; exact sub_zero _
    · exact hn
  exact foldl_bound ins [0, -1] bad val hinit hi z (by simpa [base] using hz)

private theorem option_bound (a bad z : T) (hz : z ∈ plus base a) (h : z &&& bad = 0) :
    Sub z (allowed (a :: -1 :: ins) bad) := by
  refine plus_bound base a bad _ ?_ ?_ z hz h
  · exact base_bound bad _ (allowed_bound _ bad _ (by simp))
      (fun x hx => allowed_bound _ bad _ (by simp [hx]))
  · exact allowed_bound _ bad _ (by simp)

private theorem sub_or_mono {a b c d : T} (ha : Sub a c) (hb : Sub b d) :
    Sub (a ||| b) (c ||| d) :=
  sub_or (sub_trans ha (sub_or_left _ _)) (sub_trans hb (sub_or_right _ _))

private theorem safePart_self {a : T} (h : Sub a target) : safePart a = a := by
  simp [safePart, meets_iff _ _ |>.2 h]

private theorem safePart_zero {a : T} (h : ¬ Sub a target) : safePart a = 0 := by
  have hn : meets a target = false := Bool.eq_false_iff.mpr (fun ht => h ((meets_iff _ _).1 ht))
  simp [safePart, hn]

private theorem safePart_sub (a : T) : Sub (safePart a) target := by
  by_cases h : Sub a target
  · simpa only [safePart_self h] using h
  · rw [safePart_zero h]; exact sub_zero _

private theorem ands_iff (ws : List T) (z : T) :
    z ∈ ands ws ↔ ∃ x ∈ ws, ∃ y ∈ ws, z = x &&& y := by
  simp [ands, eq_comm]

private theorem zero_option (a : T) : (0 : T) ∈ plus base a :=
  List.mem_append_left _ (by decide : (0 : T) ∈ base)

private theorem safePart_ands {a b : T} (hb : b ∈ ands (plus base a)) :
    safePart b ∈ ands (plus base a) := by
  by_cases h : Sub b target
  · simpa only [safePart_self h] using hb
  · rw [safePart_zero h, ands_iff]
    exact ⟨0, zero_option a, 0, zero_option a, by simp⟩

private theorem product_dom (a x y : T) (hy : y ∈ plus base a)
    (hs : Sub (x &&& y) target) :
    Sub (x &&& y) (x &&& allowed (a :: -1 :: ins) (x &&& ~~~target)) := by
  apply sub_and (and_sub_left _ _)
  apply sub_trans (and_sub_right _ _)
  apply option_bound a _ _ hy
  have h := (sub_not_iff _ _).2 hs
  rwa [← BitVec.and_assoc, BitVec.and_comm y x]

private theorem independent_hit (a need p q : T)
    (hp : p ∈ ands (plus base a)) (hq : q ∈ ands (plus base a))
    (ps : Sub p target) (qs : Sub q target) (h : Sub need (p ||| q)) :
    independentFound (a :: -1 :: ins) (plus base a).eraseDups need = true := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (ands_iff _ _).1 hp
  obtain ⟨u, hu, v, hv, rfl⟩ := (ands_iff _ _).1 hq
  simp only [independentFound, List.any_eq_true, List.mem_eraseDups, List.mem_map, meets_iff]
  exact ⟨_, ⟨x, by simpa using hx, rfl⟩, _, ⟨u, by simpa using hu, rfl⟩,
     sub_trans h (sub_or_mono (product_dom a x y hy ps) (product_dom a u v hv qs))⟩

private theorem dependent_hit (a need x y u v : T)
    (hx : x ∈ plus base a) (hy : y ∈ plus base a)
    (hu : u ∈ plus base a) (hv : v ∈ plus base a)
    (hs : Sub (((x &&& y) ||| u) &&& v) target)
    (hc : Sub need (((x &&& y) ||| u) &&& v)) :
    dependentFound (a :: -1 :: ins) (plus base a).eraseDups need = true := by
  let bad := v &&& ~~~target
  let remaining := need &&& ~~~(allowed (a :: -1 :: ins) bad)
  have hu0 : u &&& bad = 0 := by
    have h0 := (sub_not_iff _ _).2 hs
    rw [BitVec.and_assoc, BitVec.and_or_distrib_right] at h0
    exact (BitVec.or_eq_zero_iff.mp h0).2
  have huBelow := option_bound a bad u hu hu0
  have remX : Sub remaining (x &&& y) := by
    intro i hi
    have hr : bit i need = true ∧ bit i (allowed (a :: -1 :: ins) bad) = false := by
      simpa only [remaining, bit, BitVec.getElem_and, BitVec.getElem_not, Bool.and_eq_true,
        Bool.not_eq_true'] using hi
    have hu' : bit i u = false := by
      cases h : bit i u with
      | false => rfl
      | true => exact False.elim (by rw [huBelow i h] at hr; simp at hr)
    have hcv := and_sub_left _ _ i (hc i hr.1)
    change u[i.val] = false at hu'
    simpa only [bit, BitVec.getElem_or, hu', Bool.or_false] using hcv
  have hy0 : y &&& (x &&& bad) = 0 := by
    have h0 := (sub_not_iff _ _).2 hs
    rw [BitVec.and_assoc, BitVec.and_or_distrib_right] at h0
    rw [← BitVec.and_assoc, BitVec.and_comm y x]
    exact (BitVec.or_eq_zero_iff.mp h0).1
  simp only [dependentFound, List.any_eq_true, Bool.and_eq_true, List.mem_eraseDups, meets_iff]
  exact ⟨v, hv, sub_trans hc (and_sub_right _ _), x, hx,
    sub_trans remX (and_sub_left _ _),
    sub_trans (sub_trans remX (and_sub_right _ _)) (option_bound a _ _ hy hy0)⟩

private theorem plus_iff (ws : List T) (b z : T) :
    z ∈ plus ws b ↔ ∃ x ∈ ws, z = x ∨ z = x ||| b := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact ⟨z, h, Or.inl rfl⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      exact ⟨x, hx, Or.inr rfl⟩
  · rintro ⟨x, hx, rfl | rfl⟩
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨x, hx, rfl⟩)

private theorem sub_and_mono {a b c d : T} (h : Sub a c) (k : Sub b d) :
    Sub (a &&& b) (c &&& d) :=
  sub_and (sub_trans (and_sub_left _ _) h) (sub_trans (and_sub_right _ _) k)

private theorem inter_join (u v b : T) :
    (u ||| b) &&& (v ||| b) = b ||| (u &&& v) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases u[i] <;> cases v[i] <;> cases b[i] <;> rfl

private theorem sub_crop {l u b : T} (h : l = u ∨ l = u ||| b) :
    Sub u l ∧ Sub l (u ||| b) := by
  rcases h with rfl | rfl
  · exact ⟨sub_refl _, sub_or_left _ _⟩
  · exact ⟨sub_or_left _ _, sub_refl _⟩

private theorem no_witness_for_checked (a b c : T) (check : checkFirst a = true)
    (hb : b ∈ ands (plus base a)) (hc : c ∈ ands (plus (plus base a) b))
    (cover : Sub (target &&& ~~~(safePart a)) (safePart b ||| safePart c)) : False := by
  let need := target &&& ~~~(safePart a)
  change (!(independentFound (a :: -1 :: ins) (plus base a).eraseDups need ||
    dependentFound (a :: -1 :: ins) (plus base a).eraseDups need)) = true at check
  have noInd : independentFound (a :: -1 :: ins) (plus base a).eraseDups need ≠ true := by
    intro h
    rw [h] at check
    simp at check
  have noDep : dependentFound (a :: -1 :: ins) (plus base a).eraseDups need ≠ true := by
    intro h
    rw [h] at check
    simp at check
  have direct (u v : T) (hu : u ∈ plus base a) (hv : v ∈ plus base a)
      (h : Sub (u &&& v) target) (hc' : Sub need (safePart b ||| (u &&& v))) : False :=
    noInd (independent_hit a need (safePart b) (u &&& v) (safePart_ands hb)
      ((ands_iff _ _).2 ⟨u, hu, v, hv, rfl⟩) (safePart_sub _) h hc')
  by_cases hs : Sub c target
  · rw [safePart_self hs] at cover
    obtain ⟨l, hl, r, hr, rfl⟩ := (ands_iff _ _).1 hc
    obtain ⟨u, hu, hlu⟩ := (plus_iff _ _ _).1 hl
    obtain ⟨v, hv, hrv⟩ := (plus_iff _ _ _).1 hr
    have hd := sub_and_mono (sub_crop hlu).1 (sub_crop hrv).1
    have hsafe := sub_trans hd hs
    -- A safe penultimate conjunction can be moved directly into the output union.
    by_cases hsB : Sub b target
    · have ht := sub_and_mono (sub_crop hlu).2 (sub_crop hrv).2
      rw [inter_join] at ht
      rw [safePart_self hsB] at cover
      have hcover := sub_trans cover (sub_or_mono (sub_refl b) ht)
      rw [← BitVec.or_assoc, BitVec.or_self] at hcover
      exact direct u v hu hv hsafe (by simpa only [safePart_self hsB] using hcover)
    · have coverC : Sub need (l &&& r) := by simpa [safePart_zero hsB] using cover
      obtain ⟨x, hx, y, hy, hbxy⟩ := (ands_iff _ _).1 hb
      rcases hlu with hlu | hlu <;> rcases hrv with hrv | hrv
      · rw [hlu, hrv] at hs cover
        exact direct u v hu hv hs cover
      · rw [hlu, hrv, hbxy, BitVec.and_comm u, BitVec.or_comm v] at hs coverC
        exact noDep (dependent_hit a need x y v u hx hy hv hu hs coverC)
      · rw [hlu, hrv, hbxy, BitVec.or_comm u] at hs coverC
        exact noDep (dependent_hit a need x y u v hx hy hu hv hs coverC)
      · rw [hlu, hrv, inter_join] at hs
        exact hsB (sub_trans (sub_or_left _ _) hs)
  · rw [safePart_zero hs] at cover
    exact direct 0 0 (zero_option a) (zero_option a) (by simpa using sub_zero target)
      (by simpa using cover)

private theorem output_bound (a b c : T) (h : target ∈ plus (plus (plus base a) b) c) :
    Sub (target &&& ~~~(safePart a)) (safePart b ||| safePart c) := by
  let bad := ~~~target
  let rest := safePart b ||| safePart c
  let val := safePart a ||| rest
  have safe (z : T) (hz : z &&& bad = 0) : safePart z = z := by
    have meet := (meets_iff z target).mpr ((sub_not_iff z target).mp hz)
    simp [safePart, meet]
  have noOne : ¬ (-1 : T) &&& bad = 0 := by decide
  have noInput (x : T) (hx : x ∈ ins) : ¬ x &&& bad = 0 := by
    simp only [ins, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have ha : a &&& bad = 0 → Sub a val := by
    intro hz
    rw [← safe a hz]
    exact sub_or_left _ _
  have hb : b &&& bad = 0 → Sub b val := by
    intro hz
    conv_lhs => rw [← safe b hz]
    exact sub_trans (sub_or_left _ _) (sub_or_right _ _)
  have hc : c &&& bad = 0 → Sub c val := by
    intro hz
    conv_lhs => rw [← safe c hz]
    exact sub_trans (sub_or_right _ _) (sub_or_right _ _)
  have hbase : ∀ z ∈ base, z &&& bad = 0 → Sub z val :=
    base_bound _ _ (fun hz => (noOne hz).elim) (fun x hx hz => (noInput x hx hz).elim)
  have ht := plus_bound _ c _ _ (plus_bound _ b _ _ (plus_bound _ a _ _ hbase ha) hb) hc
    target h (by decide)
  intro i hi
  have pair : bit i target = true ∧ (!(bit i (safePart a))) = true := by
    simpa only [bit, BitVec.getElem_and, BitVec.getElem_not, Bool.and_eq_true] using hi
  have hor : bit i (safePart a) = true ∨ bit i rest = true := by
    simpa only [val, bit, BitVec.getElem_or, Bool.or_eq_true] using ht i pair.1
  exact hor.resolve_left (by simpa using pair.2)

private def normClosed (ws : List T) : Prop :=
  ∀ a ∈ ws, ∀ b ∈ ws, a ||| b ∈ ws

private theorem norm_memPlus {ws : List T} {a b : T} (h : b ∈ ws) :
    b ∈ plus ws a := List.mem_append_left _ h

private theorem norm_memPlusOr {ws : List T} {a b : T} (h : b ∈ ws) :
    b ||| a ∈ plus ws a :=
  List.mem_append_right _ (List.mem_map_of_mem h)

private theorem norm_plusClosed {ws : List T} (h : normClosed ws) (a : T) :
    normClosed (plus ws a) := by
  intro x hx y hy
  simp only [plus, List.mem_append, List.mem_map] at hx hy
  rcases hx with hx | ⟨x, hx, rfl⟩ <;> rcases hy with hy | ⟨y, hy, rfl⟩
  · exact norm_memPlus (h x hx y hy)
  · simpa only [BitVec.or_assoc] using norm_memPlusOr (a := a) (h x hx y hy)
  · have eq : (x ||| a) ||| y = (x ||| y) ||| a := by ac_rfl
    rw [eq]
    exact norm_memPlusOr (h x hx y hy)
  · have eq : (x ||| a) ||| (y ||| a) = (x ||| y) ||| a := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_or]
      cases a.getLsbD i <;> simp
    rw [eq]
    exact norm_memPlusOr (h x hx y hy)

private theorem norm_memPlusNew {ws : List T} {a : T} (hz : (0 : T) ∈ ws) :
    a ∈ plus ws a := by
  have eq : (0 : T) ||| a = a := BitVec.zero_or
  have h := norm_memPlusOr (a := a) hz
  rwa [eq] at h

private theorem norm_foldClosed (xs ws : List T) (h : normClosed ws) :
    normClosed (xs.foldl plus ws) := by
  induction xs generalizing ws with
  | nil => exact h
  | cons x xs ih => exact ih _ (norm_plusClosed h x)

private theorem norm_memFold {b : T} (xs : List T) (ws : List T) (h : b ∈ ws) :
    b ∈ xs.foldl plus ws := by
  induction xs generalizing ws with
  | nil => exact h
  | cons x xs ih => exact ih _ (norm_memPlus h)

private theorem norm_inputMemFold {b : T} (xs : List T) (ws : List T) (hz : (0 : T) ∈ ws)
    (h : b ∈ xs) : b ∈ xs.foldl plus ws := by
  induction xs generalizing ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hb
    · exact norm_memFold xs _ (norm_memPlusNew hz)
    · exact ih _ (norm_memPlus hz) hb

private theorem norm_baseClosed : normClosed base := by
  have initClosed : normClosed [0, -1] := by
    intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  intro a ha b hb
  apply List.mem_eraseDups.mpr
  exact norm_foldClosed _ _ initClosed a (List.mem_eraseDups.mp ha) b (List.mem_eraseDups.mp hb)

private theorem norm_baseZero : (0 : T) ∈ base :=
  List.mem_eraseDups.mpr (norm_memFold ins _ (by simp))

private theorem norm_baseOnes : (-1 : T) ∈ base :=
  List.mem_eraseDups.mpr (norm_memFold ins _ (by simp))

private theorem norm_baseInput (a : T) (ha : a ∈ ins) : a ∈ base :=
  List.mem_eraseDups.mpr (norm_inputMemFold ins _ (by simp) ha)

private theorem norm_memAnds {ws : List T} {a b : T} (ha : a ∈ ws) (hb : b ∈ ws) :
    a &&& b ∈ ands ws :=
  List.mem_flatMap.mpr ⟨a, ha, List.mem_map_of_mem hb⟩

private theorem norm_andInAnds {ws : List T} (ho : (-1 : T) ∈ ws)
    (xs : List T) (h : ∀ x ∈ xs, x ∈ ws) (len : xs.length ≤ 2) :
    xs.foldr (· &&& ·) (-1) ∈ ands ws := by
  have self {x : T} (hx : x ∈ ws) : x ∈ ands ws := by
    simpa only [BitVec.and_self] using norm_memAnds hx hx
  rw [show (-1 : T) = BitVec.allOnes 15 from BitVec.neg_one_eq_allOnes]
  cases xs with
  | nil => rw [List.foldr_nil, ← BitVec.neg_one_eq_allOnes]; exact self ho
  | cons a xs =>
    have ha := h a (by simp)
    cases xs with
    | nil => simpa only [List.foldr_cons, List.foldr_nil, BitVec.and_allOnes] using self ha
    | cons b xs =>
      have hb := h b (by simp)
      cases xs with
      | nil => simpa only [List.foldr_cons, List.foldr_nil, BitVec.and_allOnes] using norm_memAnds ha hb
      | cons c xs => simp at len

private theorem norm_orInClosed {ws : List T} (hcl : normClosed ws) (hz : (0 : T) ∈ ws)
    (xs : List T) (h : ∀ x ∈ xs, x ∈ ws) : xs.foldr (· ||| ·) 0 ∈ ws := by
  induction xs with
  | nil => exact hz
  | cons x xs ih =>
    exact hcl _ (h x (by simp)) _ (ih (fun y hy => h y (by simp [hy])))

private def normValue (w : List T) (g : Gate) : T :=
  let vals := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => vals.foldr (· &&& ·) (-1)
  | .or => vals.foldr (· ||| ·) 0
  | _ => 0

private def normRun (gs : List Gate) (w : List T) : List T :=
  gs.foldl (fun ws g => ws ++ [normValue ws g]) w

private def normAnd (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

private theorem norm_and_iff (g : Gate) : normAnd g = true ↔ g.op = .and := by
  cases hop : g.op <;> simp [normAnd, hop]

private abbrev normGateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem norm_gateCases {g : Gate} (h : normGateOK g) : g.op = .and ∨ g.op = .or := by
  simpa using h.1

private def normReach : ℕ → List T → T → Prop
  | 0, ws, t => t ∈ ws
  | k + 1, ws, t => ∃ a ∈ ands ws, normReach k (plus ws a) t

private theorem norm_getDIn {ws w : List T}
    (hz : (0 : T) ∈ ws) (hw : ∀ t ∈ w, t ∈ ws) (i : ℕ) : w.getD i 0 ∈ ws := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hw _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hz

private theorem norm_reachMem (k : ℕ) (ws : List T) (hz : (0 : T) ∈ ws) (t : T)
    (ht : t ∈ ws) : normReach k ws t := by
  induction k generalizing ws with
  | zero => exact ht
  | succ k ih =>
    refine ⟨0, ?_, ih _ (norm_memPlus hz) (norm_memPlus ht)⟩
    simpa only [BitVec.and_self] using norm_memAnds hz hz

private theorem norm_runReached (gs : List Gate) (ws w : List T) (k j : ℕ)
    (mono : ∀ g ∈ gs, normGateOK g) (closed : normClosed ws)
    (hz : (0 : T) ∈ ws) (ho : (-1 : T) ∈ ws) (hw : ∀ t ∈ w, t ∈ ws)
    (bound : gs.countP normAnd ≤ k) :
    normReach k ws ((normRun gs w).getD j 0) := by
  induction gs generalizing ws w k with
  | nil => exact norm_reachMem k ws hz _ (norm_getDIn hz hw j)
  | cons g gs ih =>
    have hg := mono g (by simp)
    have hm (g' : Gate) (hg' : g' ∈ gs) : normGateOK g' := mono g' (by simp [hg'])
    have hvals : ∀ a ∈ g.inputs.map (fun i => w.getD i 0), a ∈ ws := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      exact norm_getDIn hz hw i
    change normReach k ws ((normRun gs (w ++ [normValue w g])).getD j 0)
    rcases norm_gateCases hg with hop | hop
    · have hcount : (g :: gs).countP normAnd = gs.countP normAnd + 1 :=
        List.countP_cons_of_pos ((norm_and_iff g).mpr hop)
      have hv : normValue w g ∈ ands ws := by
        simpa only [normValue, hop] using norm_andInAnds ho _ hvals (by simpa using hg.2)
      cases k with
      | zero => omega
      | succ k =>
        refine ⟨normValue w g, hv, ih _ _ k hm (norm_plusClosed closed _)
          (norm_memPlus hz) (norm_memPlus ho) ?_ (by omega)⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact norm_memPlus (hw t ht)
        · have htv : t = normValue w g := List.mem_singleton.mp ht
          rw [htv]
          exact norm_memPlusNew hz
    · have hcount : (g :: gs).countP normAnd = gs.countP normAnd :=
        List.countP_cons_of_neg (by simp [normAnd, hop])
      have hv : normValue w g ∈ ws := by
        simpa only [normValue, hop] using norm_orInClosed closed hz _ hvals
      refine ih ws _ k hm closed hz ho ?_ (by omega)
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hw t ht
      · rwa [List.mem_singleton.mp ht]

private theorem norm_countBound (C : Circuit) (A : Finset ℕ) (hA : A.card ≤ 3)
    (h : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and → j ∈ A) :
    C.gates.countP normAnd ≤ 3 := by
  let ix := (Finset.univ : Finset (Fin C.gates.length)).filter
    (fun i => normAnd (C.gates.get i) = true)
  have hcard : C.gates.countP normAnd = ix.card := by
    conv_lhs => rw [← List.ofFn_getElem (xs := C.gates)]
    rw [List.countP_ofFn]
    simp [ix, List.get_eq_getElem]
  have le : ix.card ≤ A.card := by
    refine Finset.card_le_card_of_injOn (s := ix) (t := A) (fun i => (i : ℕ)) ?_ ?_
    · intro i hi
      apply h i (C.gates.get i)
      · simp [List.get_eq_getElem]
      · exact (norm_and_iff _).mp (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact Fin.ext hij
  omega

private def normInput (k : Fin 15) (i : Fin 6) : Bool := (ins.getD i 0).getLsbD k

private theorem norm_andBits (vs : List T) (k : Fin 15) :
    (vs.foldr (· &&& ·) (-1)).getLsbD k = (vs.map (fun x => x.getLsbD k)).all id := by
  induction vs with
  | nil =>
    have ones : (-1 : T) = BitVec.allOnes 15 := BitVec.neg_one_eq_allOnes
    simp only [List.foldr_nil, List.map_nil, List.all_nil, ones,
      BitVec.getLsbD_allOnes, k.isLt, decide_true]
  | cons a vs ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id, ih]

private theorem norm_orBits (vs : List T) (k : Fin 15) :
    (vs.foldr (· ||| ·) 0).getLsbD k = (vs.map (fun x => x.getLsbD k)).any id := by
  induction vs with
  | nil => simp
  | cons a vs ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id, ih]

private theorem norm_readBit (w : List T) (i : ℕ) (k : Fin 15) :
    (w.getD i 0).getLsbD k = (w.map fun x => x.getLsbD k).getD i false := by
  rw [← show (0 : T).getLsbD k = false by simp, List.getD_map]

private theorem norm_stepBit (w : List T) (g : Gate) (hg : normGateOK g) (k : Fin 15) :
    (normValue w g).getLsbD k =
      g.op.eval (g.inputs.map fun i => (w.map fun x => x.getLsbD k).getD i false) := by
  rcases norm_gateCases hg with hop | hop
  · simp only [normValue, hop, GateOp.eval, norm_andBits, List.map_map, Function.comp_def, norm_readBit]
  · simp only [normValue, hop, GateOp.eval, norm_orBits, List.map_map, Function.comp_def, norm_readBit]

private theorem norm_runBits (gs : List Gate) (w : List T) (k : Fin 15)
    (mono : ∀ g ∈ gs, normGateOK g) :
    (normRun gs w).map (fun x => x.getLsbD k) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map (fun x => x.getLsbD k)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [normRun, List.foldl_cons, List.foldl_cons, ← normRun]
    rw [ih _ (fun g' h' => mono g' (List.mem_cons_of_mem _ h'))]
    rw [List.map_append, List.map_singleton, norm_stepBit _ _ (mono g (by simp))]

private theorem norm_evalBit (C : Circuit) (mono : Monotone2 C) (k : Fin 15) :
    ((normRun C.gates ins).getD C.output 0).getLsbD k = C.eval (List.ofFn (normInput k)) := by
  have hins : List.ofFn (fun i : Fin 6 => ins.getD i 0) = ins := by decide
  have inputBits : (ins.map (fun x => x.getLsbD k)) = List.ofFn (normInput k) := by
    conv_lhs => rw [← hins, List.map_ofFn]
    rfl
  rw [norm_readBit, norm_runBits _ _ _ mono, inputBits]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem norm_targetBits :
    ∀ k : Fin 15, target.getLsbD k = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] :
        List (ℕ × ℕ)) ∧ normInput k u = true ∧ normInput k v = true := by decide

private theorem norm_outTarget (C : Circuit) (mono : Monotone2 C)
    (good : ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] :
          List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) :
    (normRun C.gates ins).getD C.output 0 = target := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [norm_evalBit C mono ⟨i, hi⟩]
  exact Bool.eq_iff_iff.mpr ((good (normInput ⟨i, hi⟩)).trans (norm_targetBits ⟨i, hi⟩).symm)

private theorem normalize267 (C : Circuit) (mono : Monotone2 C)
    (hA : ∃ A : Finset ℕ, A.card ≤ 3 ∧
      ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and → j ∈ A)
    (good : ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] :
          List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) :
    ∃ a ∈ ands base, ∃ b ∈ ands (plus base a), ∃ c ∈ ands (plus (plus base a) b),
      target ∈ plus (plus (plus base a) b) c := by
  obtain ⟨A, hcard, hA⟩ := hA
  have reach := norm_runReached C.gates base ins 3 C.output mono norm_baseClosed
    norm_baseZero norm_baseOnes norm_baseInput (norm_countBound C A hcard hA)
  rwa [norm_outTarget C mono good] at reach

private def act (p : Fin 15 → Fin 15) (x : T) : T :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => x.getLsbD (p i).val))).cast (by simp)

@[simp] private theorem act_bit (p : Fin 15 → Fin 15) (x : T) (i : ℕ) (hi : i < 15) :
    (act p x).getLsbD i = x.getLsbD (p ⟨i, hi⟩).val := by
  simp only [act, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have hlen : i < (List.ofFn (fun j => x.getLsbD (p j).val)).length := by simpa using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp only [Option.getD_some, List.getElem_ofFn]

private theorem act_zero (p : Fin 15 → Fin 15) : act p 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [act_bit _ _ _ hi]
  simp

private theorem act_ones (p : Fin 15 → Fin 15) : act p (-1) = -1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : (-1 : T) = BitVec.allOnes 15 := by decide
  rw [hm, act_bit _ _ _ hi]
  simp only [BitVec.getLsbD_allOnes, hi, Fin.isLt, decide_true]

private theorem act_or (p : Fin 15 → Fin 15) (x y : T) :
    act p (x ||| y) = act p x ||| act p y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [act_bit, hi, BitVec.getLsbD_or]

private theorem act_and (p : Fin 15 → Fin 15) (x y : T) :
    act p (x &&& y) = act p x &&& act p y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [act_bit, hi, BitVec.getLsbD_and]

private theorem sym_mem_plus {ws : List T} {x a : T} :
    x ∈ plus ws a ↔ x ∈ ws ∨ ∃ u ∈ ws, u ||| a = x := by
  simp only [plus, List.mem_append, List.mem_map]

private theorem sym_plus_closed {ws : List T}
    (h : ∀ x ∈ ws, ∀ y ∈ ws, x ||| y ∈ ws) (a : T) :
    ∀ x ∈ plus ws a, ∀ y ∈ plus ws a, x ||| y ∈ plus ws a := by
  intro x hx y hy
  rcases sym_mem_plus.mp hx with hx₀ | ⟨x, hx₀, rfl⟩ <;>
    rcases sym_mem_plus.mp hy with hy₀ | ⟨y, hy₀, rfl⟩
  · exact sym_mem_plus.mpr (Or.inl (h x hx₀ y hy₀))
  · exact sym_mem_plus.mpr (Or.inr ⟨x ||| y, h x hx₀ y hy₀, by ac_rfl⟩)
  · exact sym_mem_plus.mpr (Or.inr ⟨x ||| y, h x hx₀ y hy₀, by ac_rfl⟩)
  · apply sym_mem_plus.mpr
    refine Or.inr ⟨x ||| y, h x hx₀ y hy₀, ?_⟩
    calc
      (x ||| y) ||| a = (x ||| y) ||| (a ||| a) := by rw [BitVec.or_self]
      _ = (x ||| a) ||| (y ||| a) := by ac_rfl

private theorem sym_fold_closed (xs ws : List T)
    (h : ∀ x ∈ ws, ∀ y ∈ ws, x ||| y ∈ ws) :
    ∀ x ∈ xs.foldl plus ws, ∀ y ∈ xs.foldl plus ws, x ||| y ∈ xs.foldl plus ws := by
  induction xs generalizing ws with
  | nil => exact h
  | cons a xs ih => exact ih _ (sym_plus_closed h a)

private theorem sym_fold_keep (xs ws : List T) {x : T} (hx : x ∈ ws) :
    x ∈ xs.foldl plus ws := by
  induction xs generalizing ws with
  | nil => exact hx
  | cons a xs ih => exact ih _ (sym_mem_plus.mpr (Or.inl hx))

private theorem sym_fold_gen (xs ws : List T) (hz : 0 ∈ ws) {x : T} (hx : x ∈ xs) :
    x ∈ xs.foldl plus ws := by
  induction xs generalizing ws with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact sym_fold_keep xs _ (sym_mem_plus.mpr (Or.inr ⟨0, hz, BitVec.zero_or⟩))
    · exact ih _ (sym_mem_plus.mpr (Or.inl hz)) hx

private theorem sym_base_closed : ∀ x ∈ base, ∀ y ∈ base, x ||| y ∈ base := by
  simp only [base, List.mem_eraseDups]
  apply sym_fold_closed
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

private theorem act_mem_base (p : Fin 15 → Fin 15)
    (pIns : ∀ a ∈ ins, act p a ∈ ins) {x : T} (hx : x ∈ base) : act p x ∈ base := by
  have mapFold (xs ws : List T) (hxs : ∀ a ∈ xs, act p a ∈ base)
      (hws : ∀ a ∈ ws, act p a ∈ base) {a : T} (ha : a ∈ xs.foldl plus ws) :
      act p a ∈ base := by
    induction xs generalizing ws with
    | nil => exact hws _ ha
    | cons u xs ih =>
      apply ih (plus ws u) (fun a ha => hxs a (List.mem_cons_of_mem _ ha)) _ ha
      intro y hy
      rcases sym_mem_plus.mp hy with hy | ⟨b, hb, rfl⟩
      · exact hws y hy
      · rw [act_or]
        exact sym_base_closed _ (hws b hb) _ (hxs u List.mem_cons_self)
  apply mapFold ins [0, -1] _ _ (List.mem_eraseDups.mp hx)
  · intro a ha
    apply List.mem_eraseDups.mpr
    exact sym_fold_gen ins _ (by simp) (pIns a ha)
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    apply List.mem_eraseDups.mpr
    rcases ha with rfl | rfl
    · rw [act_zero]
      exact sym_fold_keep ins _ (by simp)
    · rw [act_ones]
      exact sym_fold_keep ins _ (by simp)

private theorem act_mem_plus (p : Fin 15 → Fin 15) {ws vs : List T}
    (h : ∀ x ∈ ws, act p x ∈ vs) {a x : T} (hx : x ∈ plus ws a) :
    act p x ∈ plus vs (act p a) := by
  apply sym_mem_plus.mpr
  rcases sym_mem_plus.mp hx with hx | ⟨u, hu, rfl⟩
  · exact Or.inl (h x hx)
  · exact Or.inr ⟨act p u, h u hu, (act_or p u a).symm⟩

private theorem act_mem_ands (p : Fin 15 → Fin 15) {ws vs : List T}
    (h : ∀ x ∈ ws, act p x ∈ vs) {x : T} (hx : x ∈ ands ws) :
    act p x ∈ ands vs := by
  rcases List.mem_flatMap.mp hx with ⟨a, ha, hx⟩
  rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩
  apply List.mem_flatMap.mpr
  exact ⟨act p a, h a ha, List.mem_map.mpr ⟨act p b, h b hb, (act_and p a b).symm⟩⟩

private theorem act_normal (p : Fin 15 → Fin 15)
    (pIns : ∀ x ∈ ins, act p x ∈ ins) (pTarget : act p target = target)
    {a b c : T} (ha : a ∈ ands base) (hb : b ∈ ands (plus base a))
    (hc : c ∈ ands (plus (plus base a) b)) (hTarget : target ∈ plus (plus (plus base a) b) c) :
    act p a ∈ ands base ∧ act p b ∈ ands (plus base (act p a)) ∧
    act p c ∈ ands (plus (plus base (act p a)) (act p b)) ∧
    target ∈ plus (plus (plus base (act p a)) (act p b)) (act p c) := by
  have hb0 (x : T) (hx : x ∈ base) : act p x ∈ base := act_mem_base p pIns hx
  have hb1 (x) (hx : x ∈ plus base a) := act_mem_plus p hb0 hx
  have hb2 (x) (hx : x ∈ plus (plus base a) b) := act_mem_plus p hb1 hx
  refine ⟨act_mem_ands p hb0 ha, act_mem_ands p hb1 hb, act_mem_ands p hb2 hc, ?_⟩
  rw [← pTarget]
  exact act_mem_plus p hb2 hTarget

private def reps : List T :=
  [0, 32767, 31, 511, 4095, 12895, 13311, 16383, 30719, 1, 3, 4, 5, 7, 12, 13, 15,
    28, 29, 63, 95, 102, 127, 204, 223, 238, 255, 476, 479, 510, 607, 1023, 1759, 2047,
    4060, 4063, 4127, 4169, 4191, 4683, 4703, 12319, 12383, 12891, 12927, 4607, 4799,
    5119, 13023, 13055, 12703, 12799, 13242, 13247, 13279, 13310, 8191, 14335, 15871,
    16351, 29695, 30591]

private def pairs : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4),
    (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

private def orders : List (List (Fin 15)) :=
  let blocks : List (List (Fin 6)) :=
    [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
  let all := blocks.flatMap fun a => blocks.flatMap fun b =>
    [a ++ b.map (· + 3), a.map (· + 3) ++ b]
  all.map fun order => pairs.map fun (u, v) =>
    let a := order.getD u.val 0
    let b := order.getD v.val 0
    Fin.ofNat 15 (pairs.idxOf (min a b, max a b))

private def invertOrder (q : List (Fin 15)) : List (Fin 15) :=
  (List.finRange 15).map fun i => Fin.ofNat 15 (q.idxOf i)

private def orderMap (q : List (Fin 15)) (i : Fin 15) : Fin 15 := q.getD i.val 0

private def validOrder (q : List (Fin 15)) : Bool :=
  let f := orderMap q
  let g := orderMap (invertOrder q)
  (List.finRange 15).all (fun i => f (g i) == i) &&
    ins.all (fun x => ins.contains (act g x)) && act g target == target

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem validOrders : orders.all validOrder = true := by decide +kernel

private def orbitMasks : List T :=
  orders.flatMap fun q => reps.map (act (orderMap q))

private def packMasks : List T → Nat
  | [] => 0
  | x :: xs => ((1 : Nat) <<< x.toNat) ||| packMasks xs

private theorem mem_packMasks (xs : List T) (a : T) :
    (packMasks xs).testBit a.toNat = true ↔ a ∈ xs := by
  induction xs with
  | nil => simp [packMasks]
  | cons x xs ih =>
    have inj : x.toNat = a.toNat ↔ a = x :=
      ⟨fun h => (BitVec.eq_of_toNat_eq h).symm, fun h => by rw [h]⟩
    simp only [packMasks, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq, inj, ih, List.mem_cons]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem symCoverage : packMasks (ands base) = packMasks orbitMasks := by
  decide +kernel

private theorem sym_reduce {a : T} (ha : a ∈ ands base) :
    ∃ f : Fin 15 → Fin 15, (∀ x ∈ ins, act f x ∈ ins) ∧ act f target = target ∧
      act f a ∈ reps := by
  have h : a ∈ orbitMasks := by
    apply (mem_packMasks _ _).mp
    rw [← symCoverage]
    exact (mem_packMasks _ _).mpr ha
  obtain ⟨q, hq, hImage⟩ := List.mem_flatMap.mp h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hImage
  have hv := List.all_eq_true.mp validOrders q hq
  simp only [validOrder, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    beq_iff_eq] at hv
  obtain ⟨⟨inverse, pIns⟩, pTarget⟩ := hv
  refine ⟨orderMap (invertOrder q), pIns, pTarget, ?_⟩
  have roundTrip : act (orderMap (invertOrder q)) (act (orderMap q) r) = r := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [act_bit _ _ _ hi, act_bit _ _ _ (orderMap (invertOrder q) ⟨i, hi⟩).isLt]
    rw [inverse _ (List.mem_finRange _)]
  simpa only [roundTrip] using hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem reps_check : reps.all checkFirst = true := by decide +kernel

end PEqualNP.Outside.Meta267

open PEqualNP.Outside.Meta267 in
theorem PEqualNP.Outside.L_meta_267 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C, ⟨mono, hA⟩, good⟩
  obtain ⟨a, ha, b, hb, c, hc, hout⟩ := normalize267 C mono hA good
  obtain ⟨p, hpIns, hpTarget, hpRep⟩ := sym_reduce ha
  obtain ⟨_, hpb, hpc, hpout⟩ := act_normal p hpIns hpTarget ha hb hc hout
  exact no_witness_for_checked _ _ _ (List.all_eq_true.mp reps_check _ hpRep)
    hpb hpc (output_bound _ _ _ hpout)
