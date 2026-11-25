import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6810

theorem cover531_splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
    (h : ((∃! i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, ¬ P (Fin.natAdd m j))) ∨
      ((∀ i : Fin m, ¬ P (Fin.castAdd n i)) ∧ (∃! j : Fin n, P (Fin.natAdd m j)))) :
    ∃! i, P i := by
  rcases h with ⟨⟨i, hi, hunique⟩, hnone⟩ | ⟨hnone, ⟨j, hj, hunique⟩⟩
  · refine ⟨Fin.castAdd n i, hi, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.castAdd n i) ?_ ?_ k
    · intro k hk
      exact congrArg (Fin.castAdd n) (hunique k hk)
    · intro k hk
      exact (hnone k hk).elim
  · refine ⟨Fin.natAdd m j, hj, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.natAdd m j) ?_ ?_ k
    · intro k hk
      exact (hnone k hk).elim
    · intro k hk
      exact congrArg (Fin.natAdd m) (hunique k hk)

theorem cover531_formulaRectanglesStrong {n : ℕ}
    (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → φ.eval x = true ∧ x (label i) = true) ∧
        (∀ i y, Y i y → φ.eval y = false ∧ y (label i) = false) := by
  induction φ with
  | lit v c =>
      change c = true at mono
      subst c
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, fun _ => v, ?_, ?_, ?_⟩
      · intro x y hx hy
        change ∃! _i : Fin 1, x v = true ∧ y v = false
        exact ⟨0, ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx,
          by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy⟩,
          fun i _ => Subsingleton.elim i 0⟩
      · intro i x hx
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx, hx⟩
      · intro i y hy
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy, hy⟩
  | and a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ b.eval x = true) (fun i x => XB i x ∧ a.eval x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ a.eval y = true)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hx' : a.eval x = true ∧ b.eval x = true := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true_iff] using hx
        apply cover531_splitUnique
        cases ha : a.eval y with
        | false =>
            left
            constructor
            · simpa [X, Y, hx'.2] using totalA x y hx'.1 ha
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
        | true =>
            right
            have hb : b.eval y = false := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hy
            constructor
            · intro i hi
              have hLeft : YA i y := by simpa [Y] using hi.2
              have hFalse := (yA i y hLeft).1
              simp [ha] at hFalse
            · simpa [X, Y, hx'.1, ha, Fin.addCases_right] using totalB x y hx'.2 hb
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x ∧ b.eval x = true := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = true := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = true := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
  | or a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ a.eval x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ b.eval y = false) (fun i y => YB i y ∧ a.eval y = false)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hy' : a.eval y = false ∧ b.eval y = false := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_false_iff] using hy
        apply cover531_splitUnique
        cases ha : a.eval x with
        | false =>
            right
            have hb : b.eval x = true := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hx
            constructor
            · intro i hi
              have hLeft : XA i x := by simpa [X] using hi.1
              have hTrue := (xA i x hLeft).1
              simp [ha] at hTrue
            · simpa [X, Y, hy'.1, ha, Fin.addCases_right] using totalB x y hb hy'.2
        | true =>
            left
            constructor
            · simpa [X, Y, hy'.2] using totalA x y ha hy'.1
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = false := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y ∧ b.eval y = false := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = false := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩

theorem cover531_formulaRectangles {n : ℕ} (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x y, φ.eval x = true → φ.eval y = false → X i x → Y i y →
          x (label i) = true ∧ y (label i) = false) := by
  obtain ⟨X, Y, label, total, goodX, goodY⟩ := cover531_formulaRectanglesStrong φ mono
  exact ⟨X, Y, label, total, fun i x y _ _ hx hy => ⟨(goodX i x hx).2, (goodY i y hy).2⟩⟩

def inp {N : ℕ} (P Q : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.append (fun i : Fin N => decide (i ∈ P)) (fun i : Fin N => decide (i ∈ Q))

theorem inp_left {N : ℕ} (P Q : Finset (Fin N)) (i : Fin N) :
    inp P Q (Fin.castAdd N i) = decide (i ∈ P) := by
  unfold inp
  rw [Fin.append_left]

theorem inp_right {N : ℕ} (P Q : Finset (Fin N)) (j : Fin N) :
    inp P Q (Fin.natAdd N j) = decide (j ∈ Q) := by
  unfold inp
  rw [Fin.append_right]

theorem cast_ne_nat {N : ℕ} (i j : Fin N) : Fin.castAdd N i ≠ Fin.natAdd N j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem nat_inj {N : ℕ} (i j : Fin N) : Fin.natAdd N i = Fin.natAdd N j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have := congrArg Fin.val h
    simp at this
    exact this
  · intro h
    rw [h]

theorem cast_inj {N : ℕ} (i j : Fin N) : Fin.castAdd N i = Fin.castAdd N j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have := congrArg Fin.val h
    simp at this
    exact this
  · intro h
    rw [h]

theorem inp_single {N : ℕ} (p l : Fin N) (v : Fin (N + N)) (h : inp {p} {l} v = true) :
    v = Fin.castAdd N p ∨ v = Fin.natAdd N l := by
  induction v using Fin.addCases with
  | left i =>
    left
    rw [inp_left] at h
    simp at h
    rw [h]
  | right j =>
    right
    rw [inp_right] at h
    simp at h
    rw [h]

set_option maxHeartbeats 4000000 in
theorem main (N q : ℕ) (L : Fin N → Finset (Fin N))
    (φ : PEqualNP.MetaComplexity.DMFormula (N + N))
    (hcard : ∀ l : Fin N, (L l).card = q + 1)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula (N + N) => Prop)
      (fun (_ : Fin (N + N)) (c : Bool) => c = true) (fun _ _ p q => p ∧ q)
      (fun _ _ p q => p ∧ q) φ)
    (h0 : φ.eval (inp Finset.univ ∅) = false)
    (h1 : ∀ p l : Fin N, p ∈ L l → φ.eval (inp {p} {l}) = true)
    (h2 : ∀ p l : Fin N, p ∈ L l →
      φ.eval (inp ((L l).erase p) (Finset.univ.filter fun l' => p ∈ L l' ∧ l' ≠ l)) = false) :
    N * q ≤ φ.leaves := by
  classical
  obtain ⟨X, Y, label, partitions, labels⟩ := cover531_formulaRectangles φ mono
  let Inc := {pr : Fin N × Fin N // pr.1 ∈ L pr.2}
  let row (e : Inc) : Fin (N + N) → Bool := inp {e.1.1} {e.1.2}
  have rowPos (e : Inc) : φ.eval (row e) = true := h1 e.1.1 e.1.2 e.2
  let yF (e : Inc) : Fin (N + N) → Bool :=
    inp ((L e.1.2).erase e.1.1) (Finset.univ.filter fun l' => e.1.1 ∈ L l' ∧ l' ≠ e.1.2)
  have yFneg (e : Inc) : φ.eval (yF e) = false := h2 e.1.1 e.1.2 e.2
  let route (e : Inc) (y : Fin (N + N) → Bool) (hy : φ.eval y = false) : Fin φ.leaves :=
    Classical.choose (partitions (row e) y (rowPos e) hy)
  have routeMem (e : Inc) (y : Fin (N + N) → Bool) (hy : φ.eval y = false) :
      X (route e y hy) (row e) ∧ Y (route e y hy) y :=
    (Classical.choose_spec (partitions (row e) y (rowPos e) hy)).1
  have routeUnique (e : Inc) (y : Fin (N + N) → Bool) (hy : φ.eval y = false)
      (i : Fin φ.leaves) (hi : X i (row e) ∧ Y i y) : i = route e y hy :=
    (Classical.choose_spec (partitions (row e) y (rowPos e) hy)).2 i hi
  let selected (e : Inc) (y : Fin (N + N) → Bool) (hy : φ.eval y = false) :=
    label (route e y hy)
  have selProp (e : Inc) (y : Fin (N + N) → Bool) (hy : φ.eval y = false) :
      (selected e y hy = Fin.castAdd N e.1.1 ∨ selected e y hy = Fin.natAdd N e.1.2) ∧
        y (selected e y hy) = false := by
    have result := labels (route e y hy) (row e) y (rowPos e) hy
      (routeMem e y hy).1 (routeMem e y hy).2
    exact ⟨inp_single e.1.1 e.1.2 _ result.1, result.2⟩
  have sel0 (e : Inc) : selected e (inp Finset.univ ∅) h0 = Fin.natAdd N e.1.2 := by
    rcases selProp e (inp Finset.univ ∅) h0 with ⟨hs | hs, hf⟩
    · rw [hs, inp_left] at hf
      simp at hf
    · exact hs
  have selLine (e e' : Inc) (hl : e'.1.2 = e.1.2) (hp : e'.1.1 ≠ e.1.1) :
      selected e' (yF e) (yFneg e) = Fin.natAdd N e'.1.2 := by
    rcases selProp e' (yF e) (yFneg e) with ⟨hs | hs, hf⟩
    · rw [hs] at hf
      simp only [yF, inp_left] at hf
      have hm : e'.1.1 ∈ L e.1.2 := hl ▸ e'.2
      simp [hp, hm] at hf
    · exact hs
  have selPoint (e e' : Inc) (hp : e'.1.1 = e.1.1) (hl : e'.1.2 ≠ e.1.2) :
      selected e' (yF e) (yFneg e) = Fin.castAdd N e'.1.1 := by
    rcases selProp e' (yF e) (yFneg e) with ⟨hs | hs, hf⟩
    · exact hs
    · rw [hs] at hf
      simp only [yF, inp_right] at hf
      have hm : e.1.1 ∈ L e'.1.2 := hp ▸ e'.2
      simp [hl, hm] at hf
  let R (i : Fin φ.leaves) (pe : Fin (N + N) × Inc) : ℚ :=
    if pe.1 = label i ∧ X i (row pe.2) then 1 else 0
  let col (v : Fin (N + N)) (y : Fin (N + N) → Bool) : Fin (N + N) × Inc → ℚ :=
    Finset.univ.sum fun i : Fin φ.leaves => if Y i y ∧ label i = v then R i else 0
  let span := Submodule.span ℚ (Set.range R)
  have colInSpan (v : Fin (N + N)) (y : Fin (N + N) → Bool) : col v y ∈ span := by
    apply Submodule.sum_mem
    intro i _
    split
    · exact Submodule.subset_span ⟨i, rfl⟩
    · exact span.zero_mem
  have colValue (v : Fin (N + N)) (y : Fin (N + N) → Bool) (hy : φ.eval y = false)
      (p : Fin (N + N) × Inc) :
      col v y p = if p.1 = v ∧ selected p.2 y hy = v then 1 else 0 := by
    simp only [col, Finset.sum_apply]
    rw [Finset.sum_eq_single (route p.2 y hy)]
    · by_cases same : label (route p.2 y hy) = v
      · simp [R, selected, same, (routeMem p.2 y hy).1, (routeMem p.2 y hy).2]
      · simp [selected, same]
    · intro i _ other
      by_cases inColumn : Y i y ∧ label i = v
      · have noRow : ¬ X i (row p.2) := fun hx => other (routeUnique p.2 y hy i ⟨hx, inColumn.1⟩)
        simp [inColumn, R, noRow]
      · simp [inColumn]
    · simp
  -- the choice made on the diagonal pair
  let isA (e : Inc) : Prop := selected e (yF e) (yFneg e) = Fin.castAdd N e.1.1
  have notA (e : Inc) (h : ¬ isA e) : selected e (yF e) (yFneg e) = Fin.natAdd N e.1.2 := by
    rcases (selProp e (yF e) (yFneg e)).1 with hs | hs
    · exact absurd hs h
    · exact hs
  let kept (e : Inc) : Prop :=
    isA e ∨ (¬ isA e ∧ ∃ l' : Fin N, l' < e.1.2 ∧ ∃ h : e.1.1 ∈ L l', ¬ isA ⟨(e.1.1, l'), h⟩)
  let K := {e : Inc // kept e}
  let g (k : K) : Fin (N + N) × Inc → ℚ :=
    if isA k.1 then col (Fin.natAdd N k.1.1.2) (inp Finset.univ ∅) -
        col (Fin.natAdd N k.1.1.2) (yF k.1)
    else col (Fin.castAdd N k.1.1.1) (yF k.1)
  have gInSpan (k : K) : g k ∈ span := by
    by_cases h : isA k.1
    · simp only [g, h, if_true]
      exact span.sub_mem (colInSpan _ _) (colInSpan _ _)
    · simp only [g, h, if_false]
      exact colInSpan _ _
  have gA (k : K) (e : Inc) (he : isA e) :
      g k (Fin.natAdd N e.1.2, e) = if k.1 = e then 1 else 0 := by
    by_cases hk : isA k.1
    · have hk' : selected k.1 (yF k.1) (yFneg k.1) = Fin.castAdd N k.1.1.1 := hk
      simp only [g, hk, if_true, Pi.sub_apply]
      rw [colValue _ _ h0, colValue _ _ (yFneg k.1), sel0]
      by_cases hl : e.1.2 = k.1.1.2
      · rw [if_pos ⟨by rw [hl], by rw [hl]⟩]
        by_cases hke : k.1 = e
        · subst hke
          have hs : selected k.1 (yF k.1) (yFneg k.1) ≠ Fin.natAdd N k.1.1.2 := by
            rw [hk']
            exact cast_ne_nat _ _
          rw [if_neg (fun h => hs h.2), if_pos rfl]
          norm_num
        · have hp : e.1.1 ≠ k.1.1.1 := by
            intro hp
            apply hke
            exact Subtype.ext (Prod.ext hp.symm hl.symm)
          have hs := selLine k.1 e hl hp
          rw [if_pos ⟨by rw [hl], by rw [hs, hl]⟩, if_neg hke]
          norm_num
      · have hne : Fin.natAdd N e.1.2 ≠ Fin.natAdd N k.1.1.2 := fun h => hl ((nat_inj _ _).1 h)
        have hke : k.1 ≠ e := by
          intro h
          apply hl
          rw [h]
        rw [if_neg (fun h => hne h.1), if_neg (fun h => hne h.1), if_neg hke]
        norm_num
    · simp only [g, hk, if_false]
      rw [colValue _ _ (yFneg k.1)]
      have hke : k.1 ≠ e := by
        intro h
        apply hk
        rw [h]
        exact he
      have hne : Fin.natAdd N e.1.2 ≠ Fin.castAdd N k.1.1.1 := fun h => cast_ne_nat _ _ h.symm
      rw [if_neg (fun h => hne h.1), if_neg hke]
  have gB (k : K) (e : Inc) :
      g k (Fin.castAdd N e.1.1, e) =
        if ¬ isA k.1 ∧ k.1.1.1 = e.1.1 ∧ k.1 ≠ e then 1 else 0 := by
    by_cases hk : isA k.1
    · simp only [g, hk, if_true, Pi.sub_apply]
      rw [colValue _ _ h0, colValue _ _ (yFneg k.1)]
      have hne : Fin.castAdd N e.1.1 ≠ Fin.natAdd N k.1.1.2 := cast_ne_nat _ _
      rw [if_neg (fun h => hne h.1), if_neg (fun h => hne h.1), if_neg (fun h => h.1 trivial)]
      norm_num
    · simp only [g, hk, if_false]
      rw [colValue _ _ (yFneg k.1)]
      by_cases hp : e.1.1 = k.1.1.1
      · by_cases hke : k.1 = e
        · subst hke
          have hs : selected k.1 (yF k.1) (yFneg k.1) ≠ Fin.castAdd N k.1.1.1 := by
            rw [notA k.1 hk]
            exact fun h => cast_ne_nat _ _ h.symm
          rw [if_neg (fun h => hs h.2), if_neg (fun h => h.2.2 rfl)]
        · have hl : e.1.2 ≠ k.1.1.2 := by
            intro hl
            apply hke
            exact Subtype.ext (Prod.ext hp.symm hl.symm)
          have hs := selPoint k.1 e hp hl
          rw [if_pos ⟨by rw [hp], by rw [hs, hp]⟩, if_pos ⟨not_false, hp.symm, hke⟩]
      · rw [if_neg (fun h => hp ((cast_inj _ _).1 h.1)), if_neg (fun h => hp h.2.1.symm)]
  -- independence
  have independent : LinearIndependent ℚ g := by
    rw [Fintype.linearIndependent_iff]
    intro c relation
    have atCoord (pe : Fin (N + N) × Inc) :
        (Finset.univ.sum fun k : K => c k * g k pe) = 0 := by
      have := congrFun relation pe
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    intro k
    by_cases hk : isA k.1
    · have h := atCoord (Fin.natAdd N k.1.1.2, k.1)
      simp only [gA _ k.1 hk] at h
      have h' : (Finset.univ.sum fun k' : K => c k' * (if k'.1 = k.1 then (1 : ℚ) else 0)) =
          c k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro k' _ hne
          have : k'.1 ≠ k.1 := fun h => hne (Subtype.ext h)
          simp [this]
        · simp
      rw [← h', h]
    · -- minimal line at the point of k among the non-A incidences
      let p := k.1.1.1
      let S : Finset (Fin N) := Finset.univ.filter fun l' => ∃ h : p ∈ L l', ¬ isA ⟨(p, l'), h⟩
      have kS : k.1.1.2 ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨k.1.2, hk⟩
      have Sne : S.Nonempty := ⟨_, kS⟩
      have lstarS := Finset.min'_mem S Sne
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at lstarS
      obtain ⟨hstar, nstar⟩ := lstarS
      let estar : Inc := ⟨(p, S.min' Sne), hstar⟩
      have notKept : ¬ kept estar := by
        rintro (h | ⟨_, l', hl', hm, hn⟩)
        · exact nstar h
        · have : l' ∈ S := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hm, hn⟩
          have := Finset.min'_le S l' this
          exact absurd hl' (not_lt.mpr this)
      have neStar (k' : K) : k'.1 ≠ estar := fun h => notKept (h ▸ k'.2)
      have e1 := atCoord (Fin.castAdd N estar.1.1, estar)
      have e2 := atCoord (Fin.castAdd N k.1.1.1, k.1)
      simp only [gB] at e1 e2
      have diff : (Finset.univ.sum fun k' : K =>
          c k' * (if ¬ isA k'.1 ∧ k'.1.1.1 = estar.1.1 ∧ k'.1 ≠ estar then (1 : ℚ) else 0)) -
          (Finset.univ.sum fun k' : K =>
          c k' * (if ¬ isA k'.1 ∧ k'.1.1.1 = k.1.1.1 ∧ k'.1 ≠ k.1 then (1 : ℚ) else 0)) = c k := by
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single k]
        · have : k.1 ≠ estar := neStar k
          simp [hk, this, estar, p]
        · intro k' _ hne
          have hne' : k'.1 ≠ k.1 := fun h => hne (Subtype.ext h)
          have hs : estar.1.1 = k.1.1.1 := rfl
          simp [hne', neStar k', hs]
        · simp
      rw [← diff, e1, e2, sub_zero]
  -- rank bound
  have : Module.Finite ℚ ↥span := Module.Finite.span_of_finite ℚ (Set.finite_range R)
  let lifted (k : K) : ↥span := ⟨g k, gInSpan k⟩
  have liftedIndependent : LinearIndependent ℚ lifted := by
    apply LinearIndependent.of_comp span.subtype
    change LinearIndependent ℚ g
    exact independent
  have lower : Fintype.card K ≤ Module.finrank ℚ ↥span :=
    liftedIndependent.fintype_card_le_finrank
  have upper : Module.finrank ℚ span ≤ φ.leaves := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range R)) ≤ φ.leaves
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    simpa only [Fintype.card_fin] using Fintype.card_range_le R
  -- counting
  have cardInc : Fintype.card Inc = N * (q + 1) := by
    let eqv : Inc ≃ (Σ l : Fin N, {p : Fin N // p ∈ L l}) :=
      { toFun := fun e => ⟨e.1.2, ⟨e.1.1, e.2⟩⟩
        invFun := fun s => ⟨(s.2.1, s.1), s.2.2⟩
        left_inv := fun e => rfl
        right_inv := fun s => rfl }
    rw [Fintype.card_congr eqv, Fintype.card_sigma]
    simp only [Fintype.card_coe, hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  have cardDrop : Fintype.card {e : Inc // ¬ kept e} ≤ N := by
    have inj : Function.Injective (fun e : {e : Inc // ¬ kept e} => e.1.1.1) := by
      intro a b hab
      simp only at hab
      have ka := a.2
      have kb := b.2
      simp only [kept, not_or, not_and, not_exists, not_not] at ka kb
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext hab
      rcases lt_trichotomy a.1.1.2 b.1.1.2 with hlt | heq | hgt
      · exfalso
        have hm : b.1.1.1 ∈ L a.1.1.2 := hab ▸ a.1.2
        have hsame : (⟨(b.1.1.1, a.1.1.2), hm⟩ : Inc) = a.1 :=
          Subtype.ext (Prod.ext hab.symm rfl)
        have := kb.2 kb.1 a.1.1.2 hlt hm
        rw [hsame] at this
        exact ka.1 this
      · exact heq
      · exfalso
        have hm : a.1.1.1 ∈ L b.1.1.2 := hab ▸ b.1.2
        have hsame : (⟨(a.1.1.1, b.1.1.2), hm⟩ : Inc) = b.1 :=
          Subtype.ext (Prod.ext hab rfl)
        have := ka.2 ka.1 b.1.1.2 hgt hm
        rw [hsame] at this
        exact kb.1 this
    simpa using Fintype.card_le_of_injective _ inj
  have split : Fintype.card {e : Inc // ¬ kept e} = Fintype.card Inc - Fintype.card K :=
    Fintype.card_subtype_compl _
  have kle : Fintype.card K ≤ Fintype.card Inc := Fintype.card_subtype_le _
  have total : N * (q + 1) = N * q + N := by ring
  omega

end PEqualNP.Outside.L_meta_6810

theorem PEqualNP.Outside.L_meta_6810 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Finset (Fin x1)) (x4 : PEqualNP.MetaComplexity.DMFormula (x1 + x1)),   (∀ (x5 : Fin x1), (x3 x5).card = x2 + (1 : ℕ)) →     PEqualNP.MetaComplexity.DMFormula.rec (fun (x6 : Fin (x1 + x1)) (x7 : Bool) => x7 = Bool.true) (fun (x6 x7 : PEqualNP.MetaComplexity.DMFormula (x1 + x1)) (x8 x9 : Prop) => x8 ∧ x9) (fun (x6 x7 : PEqualNP.MetaComplexity.DMFormula (x1 + x1)) (x8 x9 : Prop) => x8 ∧ x9) x4 →       (have x7 : Finset (Fin x1) → Finset (Fin x1) → Bool := fun (x7 x8 : Finset (Fin x1)) => x4.eval (Fin.append (fun (x9 : Fin x1) => Decidable.decide (x9 ∈ x7)) fun (x9 : Fin x1) => Decidable.decide (x9 ∈ x8));         x7 Finset.univ ∅ = Bool.false ∧ ∀ (x8 x9 : Fin x1), x9 ∈ x3 x8 → x7 {x9} {x8} = Bool.true ∧ x7 ((x3 x8).erase x9) {x11 : Fin x1 | x9 ∈ x3 x11 ∧ x11 ≠ x8} = Bool.false) →         x1 * x2 ≤ x4.leaves := by
  intro N q L φ hcard mono hf
  obtain ⟨h0, h12⟩ := hf
  exact PEqualNP.Outside.L_meta_6810.main N q L φ hcard mono h0
    (fun p l h => (h12 l p h).1) (fun p l h => (h12 l p h).2)
