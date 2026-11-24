import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2864_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (w : List Bool) : C.wires w = C.gates.foldl step w := rfl

theorem getD_append_lt (l r : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ r).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_append_len (l : List Bool) (v : Bool) :
    (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (h : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none h]

theorem eval_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hg with h1 | h1
  · rw [h1]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hall b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact h i (hall _ ⟨i, hi, rfl⟩)
  · rw [Set.mem_singleton_iff] at h1
    rw [h1]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hb⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ W W' : List Bool, W.length = W'.length →
      (∀ i, W.getD i false = true → W'.getD i false = true) →
      ∀ i, (gs.foldl step W).getD i false = true → (gs.foldl step W').getD i false = true := by
  induction gs with
  | nil => intro W W' _ h; exact h
  | cons g gs ih =>
    intro W W' hlen h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · intro i hi
      have hv := eval_mono g (hgs g List.mem_cons_self) (fun k => W.getD k false)
        (fun k => W'.getD k false) h
      rcases lt_trichotomy i W.length with h1 | h1 | h1
      · simp only [step] at hi ⊢
        rw [getD_append_lt _ _ _ h1] at hi
        rw [getD_append_lt _ _ _ (by omega)]
        exact h i hi
      · subst h1
        simp only [step] at hi ⊢
        rw [getD_append_len] at hi
        rw [hlen, getD_append_len]
        exact hv hi
      · simp only [step] at hi
        rw [getD_of_length_le _ _ (by simp; omega)] at hi
        exact absurd hi (by simp)

theorem wire_mono (C : Circuit) (hC : Monotone2 C) (u v : List Bool) (hlen : u.length = v.length)
    (h : ∀ i, u.getD i false = true → v.getD i false = true) (W : ℕ) :
    (C.wires u).getD W false = true → (C.wires v).getD W false = true := by
  rw [wires_eq, wires_eq]
  exact fold_mono C.gates (fun g hg => (hC g hg).1) u v hlen h W

theorem getD_app (N : ℕ) (a b : List Bool) (ha : a.length = N) (i : ℕ) :
    (a ++ b).getD i false = if i < N then a.getD i false else b.getD (i - N) false := by
  split_ifs with hi
  · exact getD_append_lt _ _ _ (by omega)
  · simp only [List.getD]
    rw [List.getElem?_append_right (by omega), ha]

theorem rep_getD (N : ℕ) (b : Bool) (i : ℕ) :
    (List.replicate N b).getD i false = (decide (i < N) && b) := by
  by_cases hi : i < N
  · simp [List.getD, hi]
  · rw [getD_of_length_le _ _ (by simp; omega)]
    simp [hi]

theorem ofFn_const (N : ℕ) (b : Bool) : List.ofFn (fun _ : Fin N => b) = List.replicate N b := by
  apply List.ext_getElem <;> simp

/-- With the points fixed, a wire that does not change from all lines off to all lines on does
not depend on the lines at all (monotonicity). -/
theorem noL (N : ℕ) (C : Circuit) (hC : Monotone2 C) (W : ℕ)
    (h : ∀ x : Fin N → Bool, (C.wires (List.ofFn x ++ List.replicate N false)).getD W false =
      (C.wires (List.ofFn x ++ List.replicate N true)).getD W false)
    (x y : Fin N → Bool) :
    (C.wires (List.ofFn x ++ List.ofFn y)).getD W false =
      (C.wires (List.ofFn x ++ List.ofFn (fun _ : Fin N => false))).getD W false := by
  rw [ofFn_const]
  have h1 := wire_mono C hC (List.ofFn x ++ List.replicate N false) (List.ofFn x ++ List.ofFn y)
    (by simp) (by
      intro i hi
      rw [getD_app N _ _ (by simp)] at hi ⊢
      split_ifs at hi ⊢ with hiN
      · exact hi
      · rw [rep_getD] at hi; simp at hi) W
  have h2 := wire_mono C hC (List.ofFn x ++ List.ofFn y) (List.ofFn x ++ List.replicate N true)
    (by simp) (by
      intro i hi
      rw [getD_app N _ _ (by simp)] at hi ⊢
      split_ifs at hi ⊢ with hiN
      · exact hi
      · rw [rep_getD]
        have : i - N < N := by
          by_contra hc
          rw [getD_of_length_le _ _ (by simp; omega)] at hi
          simp at hi
        simp [this]) W
  rw [h x] at h1 ⊢
  cases hv : (C.wires (List.ofFn x ++ List.ofFn y)).getD W false <;>
    cases hw : (C.wires (List.ofFn x ++ List.replicate N true)).getD W false <;> simp_all

theorem noP (N : ℕ) (C : Circuit) (hC : Monotone2 C) (W : ℕ)
    (h : ∀ y : Fin N → Bool, (C.wires (List.replicate N false ++ List.ofFn y)).getD W false =
      (C.wires (List.replicate N true ++ List.ofFn y)).getD W false)
    (x y : Fin N → Bool) :
    (C.wires (List.ofFn x ++ List.ofFn y)).getD W false =
      (C.wires (List.ofFn (fun _ : Fin N => false) ++ List.ofFn y)).getD W false := by
  rw [ofFn_const]
  have h1 := wire_mono C hC (List.replicate N false ++ List.ofFn y) (List.ofFn x ++ List.ofFn y)
    (by simp) (by
      intro i hi
      rw [getD_app N _ _ (by simp)] at hi ⊢
      split_ifs at hi ⊢ with hiN
      · rw [rep_getD] at hi; simp at hi
      · exact hi) W
  have h2 := wire_mono C hC (List.ofFn x ++ List.ofFn y) (List.replicate N true ++ List.ofFn y)
    (by simp) (by
      intro i hi
      rw [getD_app N _ _ (by simp)] at hi ⊢
      split_ifs at hi ⊢ with hiN
      · rw [rep_getD]; simp [hiN]
      · exact hi) W
  rw [h y] at h1 ⊢
  cases hv : (C.wires (List.ofFn x ++ List.ofFn y)).getD W false <;>
    cases hw : (C.wires (List.replicate N true ++ List.ofFn y)).getD W false <;> simp_all

/-- An accepted single pair is incident. -/
theorem pair_incident (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 0 < q)
    (hsound : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
      (¬∃ (p : Fin N) (l : Fin N), I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true) → circuitFun (N + N) C z = false)
    (p l : Fin N)
    (hacc : circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) :
    I p l := by
  by_contra hpl
  have hcard : Fintype.card { l' : Fin N //
      (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
        (Fin.natAdd N l') = true } ≤ q := by
    have : Fintype.card { l' : Fin N //
        (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
          (Fin.natAdd N l') = true } ≤ 1 := by
      apply Fintype.card_le_one_iff.mpr
      intro a b
      apply Subtype.ext
      have ha := a.2
      have hb := b.2
      simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at ha hb
      apply Fin.ext
      omega
    omega
  have hno : ¬∃ (p' : Fin N) (l' : Fin N), I p' l' ∧
      (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
        (Fin.castAdd N p') = true ∧
      (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
        (Fin.natAdd N l') = true := by
    rintro ⟨p', l', hI, h1, h2⟩
    simp only [decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at h1 h2
    have hp : p' = p := by
      apply Fin.ext
      rcases h1 with h1 | h1
      · exact h1
      · have := p'.isLt; omega
    have hl : l' = l := by
      apply Fin.ext
      rcases h2 with h2 | h2
      · have := p.isLt; omega
      · omega
    subst hp; subst hl
    exact hpl hI
  rw [hsound _ hcard hno] at hacc
  exact Bool.false_ne_true hacc

end PEqualNP.Outside.L_meta_2864_aux

theorem PEqualNP.Outside.L_meta_2864 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) →       PEqualNP.MetaComplexity.Monotone2 x5 →         (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) →           ∀ (x10 x11 : ℕ),             ¬((∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.false)).getD x12 Bool.false ≠ (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.true)).getD x12 Bool.false) ∨ ∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x14)).getD x12 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x14)).getD x12 Bool.false) →               have x13 : ℕ → (Fin x2 → Bool) → (Fin x2 → Bool) → Bool := fun (x13 : ℕ) (x14 x15 : Fin x2 → Bool) => (x5.wires (List.ofFn x14 ++ List.ofFn x15)).getD x13 Bool.false;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               (∃ x15 ∈ [x10, x11], ∀ (x16 x17 : Fin x2 → Bool), (x13 x10 x16 x17 && x13 x11 x16 x17) = x13 x15 x16 x17) ∨ ∃ (x15 : (Fin x2 → Bool) → Bool) (x16 : (Fin x2 → Bool) → Bool), (∀ (x17 x18 : Fin x2 → Bool), (x13 x10 x17 x18 && x13 x11 x17 x18) = (x15 x17 && x16 x18)) ∧ ((∀ (x17 x18 : Fin x2), (x15 (x14 x17) && x16 (x14 x18)) = Bool.true → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 x17 ∨ x20 = Fin.natAdd x2 x18)) = Bool.true) → ∀ (x18 x19 x20 x21 : Fin x2), (x15 (x14 x18) && x16 (x14 x20)) = Bool.true → (x15 (x14 x19) && x16 (x14 x21)) = Bool.true → x18 = x19 ∨ x20 = x21) := by
  intro q N I _ C hq huniq hC hsound A B hdep V e
  have hd := hdep
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    not_or, not_and_or, not_exists, not_not] at hd
  obtain ⟨hL, hP⟩ := hd
  -- independence facts
  have iL : ∀ W, (∀ x : Fin N → Bool,
      (C.wires (List.ofFn x ++ List.replicate N false)).getD W false =
      (C.wires (List.ofFn x ++ List.replicate N true)).getD W false) →
      ∀ x y, V W x y = V W x (fun _ => false) :=
    fun W h x y => PEqualNP.Outside.L_meta_2864_aux.noL N C hC W h x y
  have iP : ∀ W, (∀ y : Fin N → Bool,
      (C.wires (List.replicate N false ++ List.ofFn y)).getD W false =
      (C.wires (List.replicate N true ++ List.ofFn y)).getD W false) →
      ∀ x y, V W x y = V W (fun _ => false) y :=
    fun W h x y => PEqualNP.Outside.L_meta_2864_aux.noP N C hC W h x y
  -- the rectangle property
  have rect : ∀ (f g : (Fin N → Bool) → Bool),
      ((∀ (x17 x18 : Fin N), (f (e x17) && g (e x18)) = true →
        PEqualNP.MetaComplexity.circuitFun (N + N) C
          (fun k => decide (k = Fin.castAdd N x17 ∨ k = Fin.natAdd N x18)) = true) →
      ∀ (x18 x19 x20 x21 : Fin N), (f (e x18) && g (e x20)) = true →
        (f (e x19) && g (e x21)) = true → x18 = x19 ∨ x20 = x21) := by
    intro f g hacc p1 p2 l1 l2 h1 h2
    rw [Bool.and_eq_true] at h1 h2
    by_contra hc
    rw [not_or] at hc
    have i11 := PEqualNP.Outside.L_meta_2864_aux.pair_incident q N I C hq hsound p1 l1
      (hacc p1 l1 (by rw [Bool.and_eq_true]; exact ⟨h1.1, h1.2⟩))
    have i12 := PEqualNP.Outside.L_meta_2864_aux.pair_incident q N I C hq hsound p1 l2
      (hacc p1 l2 (by rw [Bool.and_eq_true]; exact ⟨h1.1, h2.2⟩))
    have i21 := PEqualNP.Outside.L_meta_2864_aux.pair_incident q N I C hq hsound p2 l1
      (hacc p2 l1 (by rw [Bool.and_eq_true]; exact ⟨h2.1, h1.2⟩))
    have i22 := PEqualNP.Outside.L_meta_2864_aux.pair_incident q N I C hq hsound p2 l2
      (hacc p2 l2 (by rw [Bool.and_eq_true]; exact ⟨h2.1, h2.2⟩))
    obtain ⟨l, _, hl⟩ := huniq p1 p2 hc.1
    exact hc.2 ((hl l1 ⟨i11, i21⟩).trans (hl l2 ⟨i12, i22⟩).symm)
  rcases hL with hLA | hLB <;> rcases hP with hPA | hPB
  · -- A depends on neither side: a constant
    left
    have hc : ∀ x y, V A x y = V A (fun _ => false) (fun _ => false) := by
      intro x y
      rw [iL A hLA x y, iP A hPA x (fun _ => false)]
    cases hcv : V A (fun _ => false) (fun _ => false)
    · exact ⟨A, by simp, fun x y => by rw [hc x y, hcv]; simp⟩
    · exact ⟨B, by simp, fun x y => by rw [hc x y, hcv]; simp⟩
  · right
    refine ⟨fun x => V A x (fun _ => false), fun y => V B (fun _ => false) y, ?_,
      rect (fun x => V A x (fun _ => false)) (fun y => V B (fun _ => false) y)⟩
    intro x y
    rw [iL A hLA x y, iP B hPB x y]
  · right
    refine ⟨fun x => V B x (fun _ => false), fun y => V A (fun _ => false) y, ?_,
      rect (fun x => V B x (fun _ => false)) (fun y => V A (fun _ => false) y)⟩
    intro x y
    rw [iL B hLB x y, iP A hPA x y, Bool.and_comm]
  · left
    have hc : ∀ x y, V B x y = V B (fun _ => false) (fun _ => false) := by
      intro x y
      rw [iL B hLB x y, iP B hPB x (fun _ => false)]
    cases hcv : V B (fun _ => false) (fun _ => false)
    · exact ⟨B, by simp, fun x y => by rw [hc x y, hcv]; simp⟩
    · exact ⟨A, by simp, fun x y => by rw [hc x y, hcv]; simp⟩
