import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2864
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      have := (hleg g (by simp)).1
      simpa using this
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem le_append (L1 L2 M1 M2 : List Bool) (hl : L1.length = L2.length)
    (hL : ∀ i, L1.getD i false = true → L2.getD i false = true)
    (hM : ∀ i, M1.getD i false = true → M2.getD i false = true) :
    ∀ i, (L1 ++ M1).getD i false = true → (L2 ++ M2).getD i false = true := by
  intro i
  by_cases h : i < L1.length
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (by omega)]; exact hL i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    exact hM _

def W (C : Circuit) (n i : ℕ) (x y : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x ++ List.ofFn y)).getD i false

theorem monoW (C : Circuit) (hC : Monotone2 C) (n i : ℕ) (x x' y y' : Fin n → Bool)
    (hx : ∀ v, x v = true → x' v = true) (hy : ∀ v, y v = true → y' v = true) :
    W C n i x y = true → W C n i x' y' = true :=
  mono2 C.gates hC (List.ofFn x ++ List.ofFn y) (List.ofFn x' ++ List.ofFn y')
    (by simp only [List.length_append, List.length_ofFn])
    (le_append _ _ _ _ (by simp only [List.length_ofFn]) (ofFn_mono n x x' hx)
      (ofFn_mono n y y' hy)) i

theorem squeeze (a b c : Bool) (h1 : a = true → b = true) (h2 : b = true → c = true)
    (h3 : a = c) : b = a := by
  revert h1 h2 h3
  cases a <;> cases b <;> cases c <;> decide

theorem indepR (C : Circuit) (hC : Monotone2 C) (n i : ℕ)
    (h : ∀ x : Fin n → Bool, W C n i x (fun _ => false) = W C n i x (fun _ => true)) :
    ∀ x y, W C n i x y = W C n i x (fun _ => false) := by
  intro x y
  exact squeeze _ _ _ (monoW C hC n i x x _ y (fun _ h => h) (fun _ h => by simp at h))
    (monoW C hC n i x x y _ (fun _ h => h) (fun _ _ => rfl)) (h x)

theorem indepL (C : Circuit) (hC : Monotone2 C) (n i : ℕ)
    (h : ∀ y : Fin n → Bool, W C n i (fun _ => false) y = W C n i (fun _ => true) y) :
    ∀ x y, W C n i x y = W C n i (fun _ => false) y := by
  intro x y
  exact squeeze _ _ _ (monoW C hC n i _ x y y (fun _ h => by simp at h) (fun _ h => h))
    (monoW C hC n i x _ y y (fun _ _ => rfl) (fun _ h => h)) (h y)

theorem rep (n : ℕ) (b : Bool) : List.replicate n b = List.ofFn (fun _ : Fin n => b) := by
  simp

theorem sound_inc (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (C : Circuit) (hx1 : 0 < x1)
    (hsound : ∀ (x9 : Fin (x2 + x2) → Bool),
      Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = true } ≤ x1 →
      (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = true ∧
        x9 (Fin.natAdd x2 x12) = true) → circuitFun (x2 + x2) C x9 = false)
    (p l : Fin x2)
    (hacc : circuitFun (x2 + x2) C
      (fun z => decide (z = Fin.castAdd x2 p ∨ z = Fin.natAdd x2 l)) = true) : x3 p l := by
  by_contra hpl
  have := hsound (fun z => decide (z = Fin.castAdd x2 p ∨ z = Fin.natAdd x2 l)) ?_ ?_
  · rw [this] at hacc; exact absurd hacc (by simp)
  · have hc : Fintype.card { x10 : Fin x2 // decide (Fin.natAdd x2 x10 = Fin.castAdd x2 p ∨
        Fin.natAdd x2 x10 = Fin.natAdd x2 l) = true } ≤ 1 := by
      apply Fintype.card_le_one_iff.mpr
      intro a b
      apply Subtype.ext
      have ha := a.2
      have hb := b.2
      have hp := p.2
      simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at ha hb
      exact Fin.ext (by omega)
    omega
  · rintro ⟨a, b, hab, ha, hb⟩
    have hp := p.2
    have ha2 := a.2
    have hb2 := b.2
    simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at ha hb
    have e1 : a = p := Fin.ext (by omega)
    have e2 : b = l := Fin.ext (by omega)
    subst e1 e2
    exact hpl hab

theorem rect (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (C : Circuit) (hx1 : 0 < x1)
    (hpl : ∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10)
    (hsound : ∀ (x9 : Fin (x2 + x2) → Bool),
      Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = true } ≤ x1 →
      (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = true ∧
        x9 (Fin.natAdd x2 x12) = true) → circuitFun (x2 + x2) C x9 = false)
    (f g : (Fin x2 → Bool) → Bool) :
    (∀ (x17 x18 : Fin x2), (f (fun z => decide (z = x17)) && g (fun z => decide (z = x18))) = true →
      circuitFun (x2 + x2) C (fun x20 => decide (x20 = Fin.castAdd x2 x17 ∨
        x20 = Fin.natAdd x2 x18)) = true) →
    ∀ (x18 x19 x20 x21 : Fin x2), (f (fun z => decide (z = x18)) && g (fun z => decide (z = x20))) = true →
      (f (fun z => decide (z = x19)) && g (fun z => decide (z = x21))) = true → x18 = x19 ∨ x20 = x21 := by
  intro H a b c d h1 h2
  by_contra hne
  rw [not_or] at hne
  simp only [Bool.and_eq_true] at h1 h2
  have i1 := sound_inc x1 x2 x3 C hx1 hsound a c (H a c (by simp [h1.1, h1.2]))
  have i2 := sound_inc x1 x2 x3 C hx1 hsound a d (H a d (by simp [h1.1, h2.2]))
  have i3 := sound_inc x1 x2 x3 C hx1 hsound b c (H b c (by simp [h2.1, h1.2]))
  have i4 := sound_inc x1 x2 x3 C hx1 hsound b d (H b d (by simp [h2.1, h2.2]))
  obtain ⟨z, _, hz⟩ := hpl a b hne.1
  exact hne.2 ((hz c ⟨i1, i3⟩).trans (hz d ⟨i2, i4⟩).symm)

end PEqualNP.Outside.L_meta_2864

open PEqualNP.Outside.L_meta_2864 in
theorem PEqualNP.Outside.L_meta_2864 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) →       PEqualNP.MetaComplexity.Monotone2 x5 →         (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) →           ∀ (x10 x11 : ℕ),             ¬((∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.false)).getD x12 Bool.false ≠ (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.true)).getD x12 Bool.false) ∨ ∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x14)).getD x12 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x14)).getD x12 Bool.false) →               have x13 : ℕ → (Fin x2 → Bool) → (Fin x2 → Bool) → Bool := fun (x13 : ℕ) (x14 x15 : Fin x2 → Bool) => (x5.wires (List.ofFn x14 ++ List.ofFn x15)).getD x13 Bool.false;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               (∃ x15 ∈ [x10, x11], ∀ (x16 x17 : Fin x2 → Bool), (x13 x10 x16 x17 && x13 x11 x16 x17) = x13 x15 x16 x17) ∨ ∃ (x15 : (Fin x2 → Bool) → Bool) (x16 : (Fin x2 → Bool) → Bool), (∀ (x17 x18 : Fin x2 → Bool), (x13 x10 x17 x18 && x13 x11 x17 x18) = (x15 x17 && x16 x18)) ∧ ((∀ (x17 x18 : Fin x2), (x15 (x14 x17) && x16 (x14 x18)) = Bool.true → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 x17 ∨ x20 = Fin.natAdd x2 x18)) = Bool.true) → ∀ (x18 x19 x20 x21 : Fin x2), (x15 (x14 x18) && x16 (x14 x20)) = Bool.true → (x15 (x14 x19) && x16 (x14 x21)) = Bool.true → x18 = x19 ∨ x20 = x21) := by
  intro x1 x2 x3 x4 x5 hx1 hpl hmono hsound x10 x11 hnot
  rw [not_or] at hnot
  obtain ⟨hnA, hnB⟩ := hnot
  have hR : ∃ w ∈ [x10, x11], ∀ x : Fin x2 → Bool,
      W x5 x2 w x (fun _ => false) = W x5 x2 w x (fun _ => true) := by
    by_contra hc
    apply hnA
    intro w hw
    by_contra hc2
    apply hc
    refine ⟨w, hw, fun x => ?_⟩
    have := not_exists.mp hc2 x
    rw [not_not, rep, rep] at this
    exact this
  have hL : ∃ w ∈ [x10, x11], ∀ y : Fin x2 → Bool,
      W x5 x2 w (fun _ => false) y = W x5 x2 w (fun _ => true) y := by
    by_contra hc
    apply hnB
    intro w hw
    by_contra hc2
    apply hc
    refine ⟨w, hw, fun y => ?_⟩
    have := not_exists.mp hc2 y
    rw [not_not, rep, rep] at this
    exact this
  obtain ⟨wa, hwa, hA⟩ := hR
  obtain ⟨wb, hwb, hB⟩ := hL
  have iA := indepR x5 hmono x2 wa hA
  have iB := indepL x5 hmono x2 wb hB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwa hwb
  intro x13 x14
  by_cases h01 : x10 = x11
  · subst h01
    left
    exact ⟨x10, by simp, fun _ _ => Bool.and_self _⟩
  by_cases hab : wa = wb
  · subst hab
    have hc : ∀ x y, W x5 x2 wa x y = W x5 x2 wa (fun _ => false) (fun _ => false) := by
      intro x y
      rw [iA x y, iB x (fun _ => false)]
    left
    rcases hwa with rfl | rfl
    · cases hv : W x5 x2 wa (fun _ => false) (fun _ => false)
      · refine ⟨wa, by simp, fun x y => ?_⟩
        show (W x5 x2 wa x y && W x5 x2 x11 x y) = W x5 x2 wa x y
        rw [hc x y, hv]; rfl
      · refine ⟨x11, by simp, fun x y => ?_⟩
        show (W x5 x2 wa x y && W x5 x2 x11 x y) = W x5 x2 x11 x y
        rw [hc x y, hv]; rfl
    · cases hv : W x5 x2 wa (fun _ => false) (fun _ => false)
      · refine ⟨wa, by simp, fun x y => ?_⟩
        show (W x5 x2 x10 x y && W x5 x2 wa x y) = W x5 x2 wa x y
        rw [hc x y, hv]; simp
      · refine ⟨x10, by simp, fun x y => ?_⟩
        show (W x5 x2 x10 x y && W x5 x2 wa x y) = W x5 x2 x10 x y
        rw [hc x y, hv]; simp
  right
  have hR := rect x1 x2 x3 x5 hx1 hpl hsound
  rcases hwa with rfl | rfl <;> rcases hwb with rfl | rfl
  · exact absurd rfl hab
  · refine ⟨fun x => W x5 x2 wa x (fun _ => false), fun y => W x5 x2 wb (fun _ => false) y,
      fun x y => ?_,
      hR (fun x => W x5 x2 wa x (fun _ => false)) (fun y => W x5 x2 wb (fun _ => false) y)⟩
    show (W x5 x2 wa x y && W x5 x2 wb x y) = _
    rw [iA x y, iB x y]
  · refine ⟨fun x => W x5 x2 wa x (fun _ => false), fun y => W x5 x2 wb (fun _ => false) y,
      fun x y => ?_,
      hR (fun x => W x5 x2 wa x (fun _ => false)) (fun y => W x5 x2 wb (fun _ => false) y)⟩
    show (W x5 x2 wb x y && W x5 x2 wa x y) = _
    rw [iA x y, iB x y, Bool.and_comm]
  · exact absurd rfl hab
