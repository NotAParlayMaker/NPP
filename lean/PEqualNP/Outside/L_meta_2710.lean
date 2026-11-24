import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2710

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private def route (f : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map f⟩

private lemma routed (gs : List Gate) (f : ℕ → ℕ) (d : ℕ) (xs ys : List Bool)
    (hlen : ys.length = xs.length + d)
    (hnew : ∀ i, xs.length ≤ i → f i = i + d)
    (hsafe : ∀ i, i < xs.length → f i < ys.length ∨ ys.length + gs.length ≤ f i)
    (heq : ∀ i, ys.getD (f i) false = xs.getD i false) :
    ∀ i, ((gs.map (route f)).foldl step ys).getD (f i) false =
      (gs.foldl step xs).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact heq
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hr : ((route f g).inputs.map fun i => ys.getD i false) =
        g.inputs.map (fun i => xs.getD i false) := by
      simp only [route, List.map_map, Function.comp_def]
      exact List.map_congr_left (fun i _ => heq i)
    have hx : (step xs g).length = xs.length + 1 := by simp [step]
    have hy : (step ys (route f g)).length = ys.length + 1 := by simp [step]
    apply ih (step xs g) (step ys (route f g))
    · omega
    · intro i hi
      exact hnew i (by omega)
    · intro i hi
      by_cases hold : i < xs.length
      · rcases hsafe i hold with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by simp only [List.length_cons] at h; omega)
      · left
        rw [hnew i (by omega)]
        omega
    · intro i
      by_cases hold : i < xs.length
      · rcases hsafe i hold with h | h
        · change (ys ++ [_]).getD (f i) false = (xs ++ [_]).getD i false
          rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ hold, heq]
        · have hb : ys.length ≤ f i := by omega
          have hf : (step ys (route f g)).length ≤ f i := by
            simp only [List.length_cons] at h
            omega
          rw [List.getD_eq_default _ _ hf]
          change false = (xs ++ [_]).getD i false
          rw [List.getD_append _ _ _ _ hold, ← heq, List.getD_eq_default _ _ hb]
      · change (ys ++ [_]).getD (f i) false = (xs ++ [_]).getD i false
        rw [List.getD_append_right _ _ _ _ (by rw [hnew i (by omega)]; omega),
          List.getD_append_right _ _ _ _ (by omega), hnew i (by omega), hr]
        have hsub : i + d - ys.length = i - xs.length := by omega
        rw [hsub]
        rfl

private lemma runLen (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

private lemma getPrefix (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (gs.foldl step xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private def mux (x : Fin 26 → Bool) (i : Fin 20) : Bool :=
  if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else
    if i.val < 14 then i.val + 8 else i.val + 9))
  else decide (i.val ≠ 18) && (x 16 || x 18) ||
    decide (i.val ≠ 17) && (x 19 || x 23)

private def wire (i : ℕ) : ℕ :=
  if i < 5 then i else if i < 14 then i + 8 else i + 9

private def prep : List Gate :=
  [⟨.or, [16,18]⟩, ⟨.or, [19,23]⟩, ⟨.or, [26,27]⟩]

private def big (x : Fin 26 → Bool) : Bool :=
  (x 16 || x 18) || (x 19 || x 23)

private def point (x : Fin 26 → Bool) (p : Fin 13) : Bool :=
  x (Fin.castAdd 13 p) && (if p = 6 then big x else
    ((x (Fin.natAdd 13 p) || x (Fin.natAdd 13 (p - 1))) ||
      (x (Fin.natAdd 13 (p - 3)) || x (Fin.natAdd 13 (p - 9)))))

private def suffix : List Gate :=
  [⟨.or, [18,17]⟩, ⟨.or, [15,22]⟩, ⟨.or, [28,29]⟩, ⟨.and, [5,30]⟩,
   ⟨.or, [27,31]⟩, ⟨.and, [6,26]⟩, ⟨.or, [32,33]⟩, ⟨.or, [20,19]⟩,
   ⟨.or, [17,24]⟩, ⟨.or, [35,36]⟩, ⟨.and, [7,37]⟩, ⟨.or, [34,38]⟩,
   ⟨.or, [21,20]⟩, ⟨.or, [18,25]⟩, ⟨.or, [40,41]⟩, ⟨.and, [8,42]⟩,
   ⟨.or, [39,43]⟩, ⟨.or, [22,21]⟩, ⟨.or, [19,13]⟩, ⟨.or, [45,46]⟩,
   ⟨.and, [9,47]⟩, ⟨.or, [44,48]⟩, ⟨.or, [23,22]⟩, ⟨.or, [20,14]⟩,
   ⟨.or, [50,51]⟩, ⟨.and, [10,52]⟩, ⟨.or, [49,53]⟩, ⟨.or, [24,23]⟩,
   ⟨.or, [21,15]⟩, ⟨.or, [55,56]⟩, ⟨.and, [11,57]⟩, ⟨.or, [54,58]⟩,
   ⟨.or, [25,24]⟩, ⟨.or, [22,16]⟩, ⟨.or, [60,61]⟩, ⟨.and, [12,62]⟩,
   ⟨.or, [59,63]⟩]

private def suffixResult (x : Fin 26 → Bool) (t : Bool) : Bool :=
  ((((((((t || point x 5) || point x 6) || point x 7) || point x 8) || point x 9) || point x 10) || point x 11) || point x 12)

private abbrev incident (p l : Fin 13) : Prop :=
  ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l + d

private def extra (x : Fin 26 → Bool) : Bool :=
  decide (∃ p l : Fin 13, 5 ≤ p.val ∧ incident p l ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)

private lemma incCases (p l : Fin 13) :
    incident p l ↔ l = p ∨ l = p - 1 ∨ l = p - 3 ∨ l = p - 9 := by
  fin_cases p <;> fin_cases l <;> decide

private lemma pointTrue (x : Fin 26 → Bool) (p : Fin 13) :
    point x p = true ↔ ∃ l, incident p l ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  by_cases hp : p = 6
  · subst p
    simp [point, big, incCases, Bool.and_eq_true, Bool.or_eq_true, or_and_right, exists_or]
    tauto
  · simp [point, hp, incCases, Bool.and_eq_true, Bool.or_eq_true, or_and_right, exists_or]
    tauto

private lemma highPoints (P : Fin 13 → Prop) :
    (∃ p : Fin 13, 5 ≤ p.val ∧ P p) ↔ P 5 ∨ P 6 ∨ P 7 ∨ P 8 ∨ P 9 ∨ P 10 ∨ P 11 ∨ P 12 := by
  constructor
  · rintro ⟨p, hp, h⟩
    fin_cases p <;> first | omega | tauto
  · rintro (h | h | h | h | h | h | h | h)
    · exact ⟨5, by decide, h⟩
    · exact ⟨6, by decide, h⟩
    · exact ⟨7, by decide, h⟩
    · exact ⟨8, by decide, h⟩
    · exact ⟨9, by decide, h⟩
    · exact ⟨10, by decide, h⟩
    · exact ⟨11, by decide, h⟩
    · exact ⟨12, by decide, h⟩

private lemma reorderOr (T A B C D E F G H : Prop) :
    ((((((((T ∨ A) ∨ B) ∨ C) ∨ D) ∨ E) ∨ F) ∨ G) ∨ H) ↔
      (A ∨ B ∨ C ∨ D ∨ E ∨ F ∨ G ∨ H) ∨ T := by
  tauto

private lemma suffixFormula (x : Fin 26 → Bool) (t : Bool) :
    suffixResult x t = (extra x || t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [suffixResult, Bool.or_eq_true, pointTrue, extra, decide_eq_true_eq]
  rw [show (∃ p l : Fin 13, 5 ≤ p.val ∧ incident p l ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ↔
      (∃ p : Fin 13, 5 ≤ p.val ∧ ∃ l : Fin 13, incident p l ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) from
        ⟨fun ⟨p,l,h,h'⟩ => ⟨p,h,l,h'⟩, fun ⟨p,h,l,h'⟩ => ⟨p,l,h,h'⟩⟩,
    highPoints]
  exact reorderOr _ _ _ _ _ _ _ _ _

set_option maxRecDepth 4096 in
private lemma prepRead (x : Fin 26 → Bool) (i : Fin 20) :
    (prep.foldl step (List.ofFn x)).getD (wire i.val) false = mux x i := by
  fin_cases i <;> simp [prep, step, wire, mux, GateOp.eval, List.getD_eq_getElem?_getD] <;> rfl

set_option maxRecDepth 4096 in
private lemma prepBig (x : Fin 26 → Bool) :
    (prep.foldl step (List.ofFn x)).getD 28 false = big x := by
  simp [prep, step, big, GateOp.eval, List.getD_eq_getElem?_getD,
    List.getElem?_append, List.getElem?_ofFn]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private lemma evalSuffix (x : Fin 26 → Bool) (t : Bool) :
    (suffix.foldl step (List.ofFn x ++ [big x,t])).getD 64 false = suffixResult x t := by
  simp [suffix, suffixResult, step, point, big, GateOp.eval, List.getD_eq_getElem?_getD,
    List.getElem?_append, List.getElem?_ofFn, Fin.castAdd, Fin.natAdd]

private lemma prepMono : Monotone2 ⟨prep,0⟩ := by
  intro g hg
  change g ∈ prep at hg
  simp only [prep, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

private lemma suffixMono : Monotone2 ⟨suffix,0⟩ := by
  intro g hg
  change g ∈ suffix at hg
  simp only [suffix, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private lemma wireBound (i : ℕ) : wire i ≤ i + 9 := by
  unfold wire
  split_ifs <;> omega

private lemma wireLarge {i : ℕ} (hi : 20 ≤ i) : wire i = i + 9 := by
  simp [wire, show ¬i < 5 by omega, show ¬i < 14 by omega]

private lemma getOfFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i,hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

set_option maxHeartbeats 1000000 in
private lemma complete (C : Circuit) (hC : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 40 ∧
      ∀ x : Fin 26 → Bool, circuitFun 26 D x = (extra x || circuitFun 20 C (mux x)) := by
  let out := if C.output < 20 + C.size then wire C.output else 29 + C.size + 37
  let d := C.size + 1
  let f (i : ℕ) := if i < 26 then i else if i = 26 then 28 else if i = 27 then out else i + d
  let core := C.gates.map (route wire)
  let D : Circuit := ⟨prep ++ core ++ suffix.map (route f), f 64⟩
  have pLen : prep.length = 3 := rfl
  have sLen : suffix.length = 37 := rfl
  have cLen : core.length = C.size := by simp [core, Circuit.size]
  have monoRoute (g : Gate) (hg : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧
      g.inputs.length ≤ 2) (m : ℕ → ℕ) :
      (route m g).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧
        (route m g).inputs.length ≤ 2 := by simpa [route] using hg
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ prep ++ core ++ suffix.map (route f) at hg
    simp only [List.mem_append] at hg
    rcases hg with (hp | hc) | hs
    · exact prepMono g hp
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      exact monoRoute a (hC a ha) wire
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
      exact monoRoute a (suffixMono a ha) f
  · change (prep ++ core ++ suffix.map (route f)).length ≤ _
    simp [pLen, cLen, sLen] <;> omega
  · intro x
    let px := List.ofFn x
    let qx := prep.foldl step px
    let tx := List.ofFn (mux x)
    let ys := core.foldl step qx
    let t := circuitFun 20 C (mux x)
    let sx := px ++ [big x, t]
    have hp : px.length = 26 := List.length_ofFn
    have hq : qx.length = 29 := by rw [show qx.length = _ from runLen prep px, hp, pLen]
    have ht : tx.length = 20 := List.length_ofFn
    have hy : ys.length = 29 + C.size := by rw [show ys.length = _ from runLen core qx, hq, cLen]
    have hxs : sx.length = 28 := by simp [sx, hp]
    have hcore : ∀ i, ys.getD (wire i) false = (C.gates.foldl step tx).getD i false := by
      apply routed C.gates wire 9 tx qx
      · omega
      · intro i hi
        exact wireLarge (by omega)
      · intro i hi
        exact Or.inl (by have := wireBound i; omega)
      · intro i
        by_cases hi : i < 20
        · rw [show tx.getD i false = mux x ⟨i,hi⟩ from getOfFn (mux x) i hi]
          exact prepRead x ⟨i,hi⟩
        · rw [wireLarge (by omega), List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by omega)]
    have hreadOut : ys.getD out false = t := by
      by_cases ho : C.output < 20 + C.size
      · rw [show out = wire C.output by simp [out, ho], hcore]
        rfl
      · rw [show out = 29 + C.size + 37 by simp [out, ho],
          List.getD_eq_default _ _ (by omega)]
        change false = (C.gates.foldl step tx).getD C.output false
        rw [List.getD_eq_default _ _ (by rw [runLen, ht]; exact Nat.le_of_not_lt ho)]
    have hreadPrefix {i : ℕ} (hi : i < 26) : ys.getD i false = px.getD i false := by
      change (core.foldl step qx).getD i false = _
      rw [getPrefix _ _ _ (by omega)]
      exact getPrefix prep px i (by omega)
    have hbig : ys.getD 28 false = big x := by
      change (core.foldl step qx).getD 28 false = _
      rw [getPrefix _ _ _ (by omega)]
      exact prepBig x
    have fLarge {i : ℕ} (hi : 28 ≤ i) : f i = i + d := by
      simp [f, show ¬i < 26 by omega, show i ≠ 26 by omega, show i ≠ 27 by omega]
    have sSafe (i : ℕ) (hi : i < sx.length) :
        f i < ys.length ∨ ys.length + suffix.length ≤ f i := by
      by_cases hlow : i < 26
      · left
        rw [show f i = i by simp [f,hlow]]
        omega
      · have h : i = 26 ∨ i = 27 := by omega
        rcases h with rfl | rfl
        · left
          rw [show f 26 = 28 by simp [f]]
          omega
        · rw [show f 27 = out by simp [f]]
          by_cases ho : C.output < 20 + C.size
          · left
            rw [show out = wire C.output by simp [out,ho]]
            have := wireBound C.output
            omega
          · right
            rw [show out = 29 + C.size + 37 by simp [out,ho], hy, sLen]
    have seeds (i : ℕ) : ys.getD (f i) false = sx.getD i false := by
      by_cases hlow : i < 26
      · rw [show f i = i by simp [f,hlow], hreadPrefix hlow]
        exact (List.getD_append _ _ _ _ (by omega)).symm
      · by_cases h26 : i = 26
        · subst i
          rw [show f 26 = 28 by simp [f], hbig]
          change big x = (px ++ [big x,t]).getD 26 false
          rw [List.getD_append_right _ _ _ _ (by omega), hp]
          rfl
        · by_cases h27 : i = 27
          · subst i
            rw [show f 27 = out by simp [f], hreadOut]
            change t = (px ++ [big x,t]).getD 27 false
            rw [List.getD_append_right _ _ _ _ (by omega), hp]
            rfl
          · rw [fLarge (by omega), List.getD_eq_default _ _ (by dsimp [d]; omega),
              List.getD_eq_default _ _ (by omega)]
    have execute := routed suffix f d sx ys (by dsimp [d]; omega)
      (fun i hi => fLarge (by omega)) sSafe seeds 64
    change ((prep ++ core ++ suffix.map (route f)).foldl step px).getD (f 64) false = _
    simp only [List.foldl_append]
    change ((suffix.map (route f)).foldl step ys).getD (f 64) false = (extra x || t)
    rw [execute, evalSuffix, suffixFormula]

end PEqualNP.Outside.L_meta_2710


theorem PEqualNP.Outside.L_meta_2710 :
    have x1 : (Fin (26 : ℕ) → Bool) → Fin (20 : ℕ) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) => if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ))); let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x3.size + (40 : ℕ) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 x6 = (Decidable.decide (∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x7 ∧ x2 x7 x8 ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) || PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x3 (x1 x6)) := by
  exact PEqualNP.Outside.L_meta_2710.complete
